"""Controller-owned immutable-revision verification, with durable request identity."""
from concurrent.futures import ThreadPoolExecutor
import json
import os
from pathlib import Path
import re
import secrets
import subprocess
import threading

from .distributed_claims import OwnershipError


class VerificationService:
    def __init__(self, ledger, directory, program, python, *, recover_existing=True,
                 max_workers=2, uncertain_exit_codes=()):
        if type(max_workers) is not int or max_workers < 1:
            raise ValueError('max_workers must be a positive integer')
        self.ledger, self.directory, self.program, self.python = ledger, Path(directory), str(program), str(python)
        self.directory.mkdir(parents=True, exist_ok=True)
        self.max_workers = max_workers
        self.uncertain_exit_codes = frozenset(uncertain_exit_codes)
        if 0 in self.uncertain_exit_codes:
            raise ValueError('success cannot be an uncertain exit code')
        self.pool = ThreadPoolExecutor(max_workers=max_workers, thread_name_prefix='frozen-verifier')
        self.lock, self.futures = threading.Lock(), {}
        with ledger._db() as db:
            db.execute('''CREATE TABLE IF NOT EXISTS verifications (
                id TEXT PRIMARY KEY, attempt TEXT NOT NULL, request TEXT NOT NULL,
                state TEXT NOT NULL, pid INTEGER, start_ticks TEXT,
                returncode INTEGER, log TEXT NOT NULL
            )''')
            # Never restart an ambiguous process after losing its controller.
            # Its actual PID/start identity is retained for operator reconciliation.
            if recover_existing:
                db.execute("UPDATE verifications SET state='uncertain' WHERE state IN ('spawning','running')")

    def dispatch_queued(self, *, ready):
        """Schedule existing requests on this controller without creating any.

        An additional controller-local dispatcher must be constructed with
        recover_existing=False. Database ownership remains authoritative:
        execute() atomically takes a queued row, so another dispatcher or the
        original broker may win without starting duplicate work. Running and
        uncertain requests are never adopted or restarted here.
        """
        if not ready:
            return []
        with self.lock:
            capacity = self.max_workers - sum(not future.done() for future in self.futures.values())
            if capacity <= 0:
                return []
            with self.ledger._db() as db:
                rows = db.execute("SELECT v.id FROM verifications v JOIN claims c "
                                  "ON c.attempt=v.attempt WHERE v.state='queued' AND c.state='owned' "
                                  "ORDER BY v.rowid").fetchall()
            selected = [row['id'] for row in rows if row['id'] not in self.futures][:capacity]
            for request_id in selected:
                self.futures[request_id] = self.pool.submit(self.execute, request_id)
            return selected

    def submit(self, owner, body, *, ready):
        claim = self.ledger.lookup(body['attempt'], owner)
        if not claim or claim['state'] != 'owned' or not secrets.compare_digest(claim['token'], body['claim_token']):
            raise OwnershipError('verification requires the live issue claim')
        registration = json.loads(claim['job']).get('verification')
        if not registration:
            raise ValueError('no registered verifier project')
        request_id = body['request_id']
        if not re.fullmatch(r'[a-f0-9]{32}', request_id):
            raise ValueError('invalid verification request identity')
        revision = body['revision']
        if not re.fullmatch(r'[a-f0-9]{40}', revision):
            raise ValueError('invalid immutable Git revision')
        project = Path(registration['project']).resolve()
        candidate, run = Path(body['candidate']).resolve(), Path(body['run_directory']).resolve()
        if not candidate.is_relative_to(project.parent) or not run.is_relative_to(project / '.humanize'):
            raise ValueError('verification paths outside registered project area')
        if not re.fullmatch(r'[A-Za-z0-9_.-]+', body['node_id']):
            raise ValueError('invalid theorem node')
        # Immutable registry data wins over every worker-supplied field.
        request = {**registration, 'candidate': str(candidate), 'run_directory': str(run),
                   'revision': revision, 'node_id': body['node_id']}
        encoded = json.dumps(request, sort_keys=True)
        with self.ledger._db() as db:
            db.execute('BEGIN IMMEDIATE')
            row = db.execute('SELECT * FROM verifications WHERE id=?', (request_id,)).fetchone()
            if row and (row['attempt'] != body['attempt'] or row['request'] != encoded):
                raise OwnershipError('verification request identity changed')
            if not row:
                db.execute('INSERT INTO verifications(id,attempt,request,state,log) VALUES(?,?,?,?,?)',
                           (request_id, body['attempt'], encoded, 'queued', str(self.directory / f'{request_id}.log')))
            db.commit()
        if ready:
            with self.lock:
                if request_id not in self.futures:
                    self.futures[request_id] = self.pool.submit(self.execute, request_id)
        return self.result(request_id, revision)

    def execute(self, request_id):
        with self.ledger._db() as db:
            db.execute('BEGIN IMMEDIATE')
            row = db.execute('SELECT * FROM verifications WHERE id=?', (request_id,)).fetchone()
            if not row or row['state'] != 'queued':
                return
            claim = db.execute('SELECT state FROM claims WHERE attempt=?', (row['attempt'],)).fetchone()
            if not claim or claim['state'] != 'owned':
                return
            db.execute("UPDATE verifications SET state='spawning' WHERE id=?", (request_id,))
            db.commit()
        request = json.loads(row['request'])
        environment = dict(os.environ)
        environment.update(
            FERMAT_VERIFICATION_REQUEST_ID=request_id,
            FERMAT_VERIFIER_PROJECT=request['project'],
            FERMAT_FROZEN_SOURCE=request['source_commit'],
            FERMAT_ROOT_NAME=request['root_name'],
            FERMAT_CONTRACT_FILE=request['contract_file'],
            FERMAT_CANDIDATE_REVISION=request['revision'],
            FERMAT_VERIFIER_OUTPUT=str(self.directory / request_id),
            HUMANIZE_RUN_DIR=request['run_directory'], HUMANIZE_NODE_ID=request['node_id'],
        )
        try:
            with open(row['log'], 'w') as output:
                process = subprocess.Popen([self.python, self.program], cwd=request['candidate'],
                                           env=environment, stdout=output, stderr=subprocess.STDOUT,
                                           start_new_session=True)
                stat = Path(f'/proc/{process.pid}/stat').read_text().rsplit(')', 1)[1].split()
                with self.ledger._db() as db:
                    db.execute("UPDATE verifications SET state='running',pid=?,start_ticks=? WHERE id=?",
                               (process.pid, stat[19], request_id))
                code = process.wait()
            with self.ledger._db() as db:
                state = 'uncertain' if code in self.uncertain_exit_codes else 'finished'
                db.execute("UPDATE verifications SET state=?,returncode=? WHERE id=?", (state, code, request_id))
        except Exception:
            with self.ledger._db() as db:
                db.execute("UPDATE verifications SET state='uncertain' WHERE id=?", (request_id,))
            raise

    def result(self, request_id, revision):
        with self.ledger._db() as db:
            row = db.execute('SELECT * FROM verifications WHERE id=?', (request_id,)).fetchone()
        response = {'request_id': request_id, 'revision': revision, 'state': row['state']}
        if row['state'] == 'finished':
            response.update(returncode=row['returncode'], output=Path(row['log']).read_text())
        return response

    def pending(self, attempt):
        with self.ledger._db() as db:
            return bool(db.execute("SELECT 1 FROM verifications WHERE attempt=? AND state!='finished' LIMIT 1", (attempt,)).fetchone())
