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
                CREATE UNIQUE INDEX IF NOT EXISTS one_issue
                    ON claims(repository, issue) WHERE state = 'owned';
                CREATE UNIQUE INDEX IF NOT EXISTS one_owner
                    ON claims(owner) WHERE state = 'owned';
            """)
            self._migrate_scope(db)
            self._migrate_node_reservations(db)

    @staticmethod
    def _migrate_node_reservations(db):
        """Operator node roles also exclude old proof-claim SQL writers."""
        db.execute('BEGIN IMMEDIATE')
        try:
            db.execute('''CREATE TABLE IF NOT EXISTS node_reservation_history (
                reservation_id TEXT PRIMARY KEY, node TEXT NOT NULL,
                owner TEXT NOT NULL, purpose TEXT NOT NULL,
                state TEXT NOT NULL CHECK(state IN ('reserved','released')),
                created REAL NOT NULL, released REAL
            )''')
            db.execute('''CREATE TABLE IF NOT EXISTS node_reservations (
                node TEXT PRIMARY KEY, reservation_id TEXT NOT NULL UNIQUE,
                owner TEXT NOT NULL, purpose TEXT NOT NULL, created REAL NOT NULL
            )''')
            for operation in ('INSERT', 'UPDATE'):
                db.execute(f'''CREATE TRIGGER IF NOT EXISTS claims_node_role_{operation.lower()}
                    BEFORE {operation} ON claims
                    WHEN NEW.state='owned' AND EXISTS (
                        SELECT 1 FROM node_reservations reserved WHERE reserved.node =
                        CASE WHEN instr(NEW.owner,'/')>0
                            THEN substr(NEW.owner,1,instr(NEW.owner,'/')-1) ELSE NEW.owner END
                    )
                    BEGIN SELECT RAISE(ABORT, 'physical node reserved by operator'); END''')
            db.commit()
        except Exception:
            db.rollback()
            raise

    @staticmethod
    def _validate_node_reservation(node, reservation_id, owner, purpose=None):
        if (not isinstance(node, str) or not re.fullmatch(r'hoa(?:0|[1-9][0-9]{0,2})', node)
                or int(node[3:]) > 127):
            raise ValueError('invalid authorized physical node')
        for value in (reservation_id, owner):
            if not isinstance(value, str) or not re.fullmatch(r'[A-Za-z0-9_.:/-]{1,240}', value):
                raise ValueError('invalid operator reservation identity')
        if purpose is not None and (not isinstance(purpose, str)
                or not re.fullmatch(r'[A-Za-z0-9_.:/-]{1,240}', purpose)):
            raise ValueError('invalid operator reservation purpose')

    def reserve_node(self, *, node: str, reservation_id: str, owner: str,
                     purpose: str) -> dict | None:
        """Operator-only, non-expiring role grant; never exposed to worker HTTP.

        None means unavailable (including an already released reservation ID).
        The caller must retain identity durably before starting a verifier.
        """
        self._validate_node_reservation(node, reservation_id, owner, purpose)
        if purpose is None:
            raise ValueError('operator reservation purpose is required')
        with self._db() as db:
            db.execute('BEGIN IMMEDIATE')
            previous = db.execute('SELECT * FROM node_reservation_history WHERE reservation_id=?',
                                  (reservation_id,)).fetchone()
            if previous:
                if (previous['node'], previous['owner'], previous['purpose']) != (node, owner, purpose):
                    raise OwnershipError('reservation identity changed')
                return dict(previous) if previous['state'] == 'reserved' else None
            if db.execute('SELECT 1 FROM node_reservations WHERE node=?', (node,)).fetchone():
                return None
            if db.execute("SELECT 1 FROM claims WHERE state='owned' AND "
                          "(owner=? OR substr(owner,1,instr(owner,'/')-1)=?)", (node, node)).fetchone():
                return None
            stamp = time.time()
            db.execute('INSERT INTO node_reservations(node,reservation_id,owner,purpose,created) '
                       'VALUES(?,?,?,?,?)', (node, reservation_id, owner, purpose, stamp))
            db.execute('INSERT INTO node_reservation_history '
                       '(reservation_id,node,owner,purpose,state,created) VALUES(?,?,?,?,?,?)',
                       (reservation_id, node, owner, purpose, 'reserved', stamp))
            row = dict(db.execute('SELECT * FROM node_reservation_history WHERE reservation_id=?',
                                  (reservation_id,)).fetchone())
            db.commit()
            return row

    def release_node(self, *, node: str, reservation_id: str, owner: str) -> dict:
        """Operator MUST first establish all owned verifier processes terminal.

        No timeout, automatic release, claim mutation or worker HTTP is provided.
        An idempotent historical release cannot affect a newer reservation.
        """
        self._validate_node_reservation(node, reservation_id, owner)
        with self._db() as db:
            db.execute('BEGIN IMMEDIATE')
            row = db.execute('SELECT * FROM node_reservation_history WHERE reservation_id=?',
                             (reservation_id,)).fetchone()
            if not row or (row['node'], row['owner']) != (node, owner):
                raise OwnershipError('node reservation ownership does not match')
            if row['state'] == 'released':
                return dict(row)
            removed = db.execute('DELETE FROM node_reservations WHERE node=? AND reservation_id=? AND owner=?',
                                 (node, reservation_id, owner)).rowcount
            if removed != 1:
                raise OwnershipError('active node reservation identity does not match')
            db.execute("UPDATE node_reservation_history SET state='released',released=? WHERE reservation_id=?",
                       (time.time(), reservation_id))
            result = dict(db.execute('SELECT * FROM node_reservation_history WHERE reservation_id=?',
                                     (reservation_id,)).fetchone())
            db.commit()
            return result

    def active_node_reservations(self) -> list[dict]:
        """Private operator inventory; never a timeout-based recovery signal."""
        with self._db() as db:
            return [dict(row) for row in db.execute(
                "SELECT * FROM node_reservation_history WHERE state='reserved' ORDER BY node")]

    @staticmethod
    def _migrate_scope(db):
        """Retain live legacy grants and make opt-in issue grants coexist safely.

        Keep the old index NAME so an older ledger opener's IF NOT EXISTS cannot
        silently reinstall project-wide serialization. Old INSERTs receive the
        exclusive default; SQL triggers also protect against those old writers.
        This migration does not enable parallel runtime execution by itself.
        """
        db.execute('BEGIN IMMEDIATE')
        try:
            columns = {row['name'] for row in db.execute('PRAGMA table_info(claims)')}
            if 'scope' not in columns:
                db.execute("ALTER TABLE claims ADD COLUMN scope TEXT NOT NULL DEFAULT 'project' "
                           "CHECK(scope IN ('project','issue'))")
            index = db.execute("SELECT sql FROM sqlite_master WHERE type='index' AND name='one_project'").fetchone()
            if index is not None and "scope = 'project'" not in index['sql']:
                db.execute('DROP INDEX one_project')
            db.execute("CREATE UNIQUE INDEX IF NOT EXISTS one_project ON claims(project) "
                       "WHERE state = 'owned' AND scope = 'project'")
            db.execute("CREATE UNIQUE INDEX IF NOT EXISTS one_node ON claims("
                       "substr(owner,1,instr(owner,'/')-1)) "
                       "WHERE state='owned' AND instr(owner,'/')>0")
            for operation in ('INSERT', 'UPDATE'):
                db.execute(f'''CREATE TRIGGER IF NOT EXISTS claims_scope_{operation.lower()}
                    BEFORE {operation} ON claims
                    WHEN NEW.state='owned' AND EXISTS (
                        SELECT 1 FROM claims held
                        WHERE held.project=NEW.project AND held.state='owned'
                          AND held.attempt!=NEW.attempt
                          AND (NEW.scope='project' OR held.scope='project')
                    )
                    BEGIN SELECT RAISE(ABORT, 'project-exclusive claim exists'); END''')
            db.commit()
        except Exception:
            db.rollback()
            raise

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
              owner: str, attempt: str, job: dict | None = None,
              parallel: bool = False) -> dict | None:
        self._validate(project, repository, issue, owner, attempt)
        if type(parallel) is not bool:
            raise ValueError('parallel claim policy must be a boolean')
        scope = 'issue' if parallel else 'project'
        repository = repository.casefold()
        with self._db() as db:
            db.execute("BEGIN IMMEDIATE")
            held = db.execute("SELECT * FROM claims WHERE attempt=?", (attempt,)).fetchone()
            if held:
                if (held['project'], held['repository'], held['issue'], held['owner']) != (
                    project, repository, issue, owner
                ):
                    raise OwnershipError("attempt identity changed")
                if held['scope'] != scope:
                    raise OwnershipError('attempt claim scope changed')
                return dict(held) if held['state'] == 'owned' else None
            if db.execute('SELECT 1 FROM node_reservations WHERE node=?',
                          (owner.split('/', 1)[0],)).fetchone():
                return None
            stamp = time.time()
            try:
                db.execute(
                    "INSERT INTO claims(attempt,project,repository,issue,owner,token,state,created,observed,job,scope) "
                    "VALUES(?,?,?,?,?,?,'owned',?,?,?,?)",
                    (attempt, project, repository, issue, owner, secrets.token_hex(32), stamp, stamp,
                     json.dumps(job or {}, sort_keys=True), scope),
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
