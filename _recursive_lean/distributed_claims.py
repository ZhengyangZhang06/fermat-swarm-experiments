"""Durable, non-expiring ownership for a single authoritative Swarm broker.

Only controller-local broker/verification services open this SQLite database,
on its LOCAL filesystem. Workers use the broker API, never SQLite on shared
Ceph/NFS. A claim is not proof acceptance.
No timestamp is used for takeover: uncertain/crashed owners remain reserved.
"""
from __future__ import annotations

from contextlib import contextmanager
import json
from pathlib import Path
import re
import secrets
import sqlite3
import time


class OwnershipError(RuntimeError):
    pass


class ClaimLedger:
    def __init__(self, path: Path):
        self.path = path
        path.parent.mkdir(parents=True, exist_ok=True)
        with self._db() as db:
            db.execute("PRAGMA journal_mode=WAL")
            db.executescript("""
                CREATE TABLE IF NOT EXISTS claims (
                    attempt TEXT PRIMARY KEY,
                    project TEXT NOT NULL,
                    repository TEXT NOT NULL,
                    issue INTEGER NOT NULL CHECK(issue > 0),
                    owner TEXT NOT NULL,
                    token TEXT NOT NULL,
                    state TEXT NOT NULL CHECK(state IN ('owned', 'released')),
                    created REAL NOT NULL,
                    observed REAL NOT NULL,
                    receipt TEXT NOT NULL DEFAULT '{}',
                    job TEXT NOT NULL DEFAULT '{}',
                    outcome TEXT NOT NULL DEFAULT ''
                );
                CREATE UNIQUE INDEX IF NOT EXISTS one_project
                    ON claims(project) WHERE state = 'owned';
                CREATE UNIQUE INDEX IF NOT EXISTS one_issue
                    ON claims(repository, issue) WHERE state = 'owned';
                CREATE UNIQUE INDEX IF NOT EXISTS one_owner
                    ON claims(owner) WHERE state = 'owned';
            """)

    @contextmanager
    def _db(self):
        db = sqlite3.connect(self.path, timeout=30, isolation_level=None)
        db.row_factory = sqlite3.Row
        db.execute("PRAGMA synchronous=FULL")
        try:
            yield db
        finally:
            db.close()

    @staticmethod
    def _validate(project, repository, issue, owner, attempt):
        for value in (project, owner, attempt):
            if not isinstance(value, str) or not re.fullmatch(r"[A-Za-z0-9_.:/-]{1,240}", value):
                raise ValueError("invalid claim identity")
        if not re.fullmatch(r"[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+", repository):
            raise ValueError("invalid repository")
        if type(issue) is not int or issue < 1:
            raise ValueError("invalid issue")

    def claim(self, *, project: str, repository: str, issue: int,
              owner: str, attempt: str, job: dict | None = None) -> dict | None:
        self._validate(project, repository, issue, owner, attempt)
        repository = repository.casefold()
        with self._db() as db:
            db.execute("BEGIN IMMEDIATE")
            held = db.execute("SELECT * FROM claims WHERE attempt=?", (attempt,)).fetchone()
            if held:
                if (held['project'], held['repository'], held['issue'], held['owner']) != (
                    project, repository, issue, owner
                ):
                    raise OwnershipError("attempt identity changed")
                return dict(held) if held['state'] == 'owned' else None
            stamp = time.time()
            try:
                db.execute(
                    "INSERT INTO claims(attempt,project,repository,issue,owner,token,state,created,observed,job) "
                    "VALUES(?,?,?,?,?,?,'owned',?,?,?)",
                    (attempt, project, repository, issue, owner, secrets.token_hex(32), stamp, stamp,
                     json.dumps(job or {}, sort_keys=True)),
                )
            except sqlite3.IntegrityError:
                db.rollback()
                return None
            row = dict(db.execute("SELECT * FROM claims WHERE attempt=?", (attempt,)).fetchone())
            db.commit()
            return row

    def lookup(self, attempt: str, owner: str) -> dict | None:
        """Recover the immutable grant after an uncertain API response."""
        with self._db() as db:
            row = db.execute('SELECT * FROM claims WHERE attempt=?', (attempt,)).fetchone()
            if row and row['owner'] != owner:
                raise OwnershipError('attempt belongs to another worker')
            return dict(row) if row else None

    @staticmethod
    def _owned(db, attempt, owner, token):
        row = db.execute("SELECT * FROM claims WHERE attempt=?", (attempt,)).fetchone()
        if (not row or row['state'] != 'owned' or row['owner'] != owner
                or not secrets.compare_digest(row['token'], token)):
            raise OwnershipError("claim ownership does not match")
        return row

    def observe(self, attempt: str, owner: str, token: str, receipt: dict) -> None:
        """Record a task/process identity. This does not renew an expiring lease."""
        encoded = json.dumps(receipt, sort_keys=True)
        if len(encoded) > 16_384:
            raise ValueError("oversized process receipt")
        with self._db() as db:
            db.execute("BEGIN IMMEDIATE")
            self._owned(db, attempt, owner, token)
            db.execute("UPDATE claims SET observed=?, receipt=? WHERE attempt=?",
                       (time.time(), encoded, attempt))
            db.commit()

    def release(self, attempt: str, owner: str, token: str, outcome: str) -> None:
        """Caller MUST first establish its owned process tree is terminal.

        No public force-release operation exists. Crash recovery needs explicit
        task reconciliation outside this ledger, not a heartbeat timeout.
        """
        if outcome not in {'yielded', 'completed', 'failed-before-spawn', 'stopped'}:
            raise ValueError("invalid terminal outcome")
        with self._db() as db:
            db.execute("BEGIN IMMEDIATE")
            row = db.execute("SELECT * FROM claims WHERE attempt=?", (attempt,)).fetchone()
            if (row and row['state'] == 'released' and row['owner'] == owner
                    and secrets.compare_digest(row['token'], token) and row['outcome'] == outcome):
                return  # Lost release response: idempotent, not permission to restart.
            self._owned(db, attempt, owner, token)
            db.execute("UPDATE claims SET state='released', outcome=?, observed=? WHERE attempt=?",
                       (outcome, time.time(), attempt))
            db.commit()

    def active(self) -> list[dict]:
        """Private operator inventory; never publish bearer tokens on a website."""
        with self._db() as db:
            return [dict(r) for r in db.execute("SELECT * FROM claims WHERE state='owned' ORDER BY project")]
