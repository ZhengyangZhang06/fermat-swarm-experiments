"""Operator-only durable capacity slot for one physical remote verifier node.

The process lock prevents concurrent controllers; the persisted request survives
controller loss. Neither a missing PID nor an expired observation frees capacity.
"""
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import secrets
import stat
import subprocess

from .swarm_verification import bind_service, digest, terminal_result


def docker(*args):
    return subprocess.run(['sudo', '-n', 'docker', *args], check=True,
                          capture_output=True, text=True, timeout=30).stdout


def inspect(kind, identity):
    command = (kind, 'inspect', identity) if kind in {'node', 'service'} else ('inspect', identity)
    values = json.loads(docker(*command))
    if len(values) != 1:
        raise RuntimeError('ambiguous remote verifier identity')
    return values[0]


def private_directory(path):
    path = Path(path).absolute()
    if any(part.is_symlink() for part in (path, *path.parents)):
        raise RuntimeError('remote slot paths must not traverse symlinks')
    info = path.stat()
    if not stat.S_ISDIR(info.st_mode) or info.st_uid != os.getuid() or info.st_mode & 0o077:
        raise RuntimeError('remote slot directory must be private and operator-owned')
    return path


def read_record(path):
    fd = os.open(path, os.O_RDONLY | os.O_NOFOLLOW)
    with os.fdopen(fd) as stream:
        info = os.fstat(stream.fileno())
        if not stat.S_ISREG(info.st_mode) or info.st_uid != os.getuid() or info.st_mode & 0o077:
            raise RuntimeError('remote slot receipt must be private and operator-owned')
        return json.load(stream)


class RemoteDispatchSlot:
    def __init__(self, ledger, node, directory):
        if not re.fullmatch(r'hoa(?:[0-9]|[1-9][0-9]|1[01][0-9]|12[0-7])', node):
            raise ValueError('invalid authorized remote verifier hostname')
        self.ledger, self.node = ledger, node
        self.directory = private_directory(directory)
        # Fixed by the authoritative ledger, NOT a caller-selected packet path.
        self.root = Path(ledger.path).resolve().parent / 'remote-verifier-slots'
        self.root.mkdir(mode=0o700, exist_ok=True)
        private_directory(self.root)
        self.path = self.root / f'{node}.json'
        self.lock = None

    def __enter__(self):
        fd = os.open(self.root / f'{self.node}.lock', os.O_RDWR | os.O_CREAT | os.O_NOFOLLOW, 0o600)
        self.lock = os.fdopen(fd, 'r+')
        try:
            info = os.fstat(fd)
            if not stat.S_ISREG(info.st_mode) or info.st_uid != os.getuid() or info.st_mode & 0o077:
                raise RuntimeError('unsafe remote verifier lock')
            fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
            node = inspect('node', self.node)
            self.node_id = node.get('ID', '')
            if (not re.fullmatch(r'[a-z0-9]{25}', self.node_id)
                    or node.get('Description', {}).get('Hostname') != self.node
                    or node.get('Status', {}).get('State') != 'ready'
                    or node.get('Spec', {}).get('Availability') != 'active'
                    or node.get('Spec', {}).get('Labels', {}).get('fermat-swarm-20261007') != 'true'):
                raise RuntimeError('remote verifier node is not authorized ready active')
            return self
        except BaseException:
            self.lock.close()
            self.lock = None
            raise

    def __exit__(self, *args):
        self.lock.close()
        self.lock = None

    def _write(self, value):
        # All readers/writers hold the stable lock inode; replacing the state is safe.
        temporary = self.path.with_suffix('.tmp')
        fd = os.open(temporary, os.O_WRONLY | os.O_CREAT | os.O_TRUNC | os.O_NOFOLLOW, 0o600)
        with os.fdopen(fd, 'w') as stream:
            json.dump(value, stream, sort_keys=True)
            stream.flush()
            os.fsync(stream.fileno())
        temporary.replace(self.path)
        fd = os.open(self.root, os.O_RDONLY | os.O_DIRECTORY)
        try:
            os.fsync(fd)
        finally:
            os.close(fd)

    def _row(self, request_id):
        with self.ledger._db() as db:
            return db.execute('SELECT * FROM verifications WHERE id=?', (request_id,)).fetchone()

    def readiness(self, catalog, *, checker, environment):
        """Require exact operator diagnostic evidence before new fleet dispatch."""
        gate = read_record(catalog)
        if gate.get('verifier_ready') is False:
            return False
        expected = dict(node=self.node, node_id=self.node_id,
                        reference_digest=environment['FERMAT_VERIFIER_REFERENCE_DIGEST'],
                        reference_volume=environment['FERMAT_SWARM_VERIFIER_REFERENCE_VOLUME'],
                        verifier_sha256=hashlib.sha256(Path(checker).read_bytes()).hexdigest())
        if gate.get('verifier_ready') is not True or any(gate.get(key) != value for key, value in expected.items()):
            raise RuntimeError('remote readiness differs from node/cache/checker identity')
        if not all(isinstance(gate.get(key), str) and re.fullmatch(r'[a-f0-9]{64}', gate[key])
                   for key in ('config_sha256', 'diagnostic_spec_sha256')):
            raise RuntimeError('remote readiness lacks diagnostic configuration identity')
        service_id, task_id = gate.get('diagnostic_service_id'), gate.get('diagnostic_task_id')
        if not all(isinstance(value, str) and re.fullmatch(r'[a-z0-9]{25}', value) for value in (service_id, task_id)):
            raise RuntimeError('remote readiness lacks exact diagnostic task identity')
        try:
            current_node = inspect('node', self.node)
            if current_node.get('ID') != self.node_id:
                raise RuntimeError('remote readiness physical node identity changed')
            service = inspect('service', service_id)
            if service.get('ID') != service_id or digest(service['Spec']) != gate['diagnostic_spec_sha256']:
                raise RuntimeError('remote readiness diagnostic service specification changed')
            if docker('service', 'ps', '--no-trunc', '--format', '{{.ID}}', service_id).splitlines() != [task_id]:
                raise RuntimeError('remote readiness diagnostic task list changed')
            task = inspect('task', task_id)
            if task.get('NodeID') != self.node_id or terminal_result(task, service_id, task_id=task_id) != 0:
                raise RuntimeError('remote readiness diagnostic is not exactly terminal successful')
        except (subprocess.CalledProcessError, subprocess.TimeoutExpired):
            # Read-only observation failure closes readiness for this poll. It
            # neither frees a held slot nor authorizes a duplicate task launch.
            return False
        return True

    def reconcile(self):
        """Free only this slot's known completed request; all ambiguity blocks."""
        if not self.path.exists():
            return True
        state = read_record(self.path)
        if state.get('node') != self.node or state.get('node_id') != self.node_id:
            raise RuntimeError('remote verifier slot node identity changed')
        if state.get('directory') != str(self.directory):
            raise RuntimeError('remote verifier packet directory changed')
        if state.get('state') == 'idle':
            return True
        request_id = state['request_id']
        if not re.fullmatch(r'[a-f0-9]{32}', request_id):
            raise RuntimeError('invalid retained request identity')
        row = self._row(request_id)
        if not row or hashlib.sha256(row['request'].encode()).hexdigest() != state['request_sha256']:
            raise RuntimeError('remote verifier ledger request changed')
        if row['state'] != 'finished' or type(row['returncode']) is not int or row['returncode'] == 75:
            return False
        request_root = private_directory(self.directory / request_id)
        receipt = read_record(request_root / 'operation.json')
        if (receipt.get('request_id') != request_id or receipt.get('node') != self.node
                or receipt.get('node_id') != self.node_id):
            raise RuntimeError('remote verifier operation identity changed')
        if receipt.get('state') == 'preparation-failed':
            if row['returncode'] == 0 or any(key in receipt for key in (
                    'service_id', 'service_name', 'task_id', 'packet_digest', 'service_spec_sha256')):
                raise RuntimeError('preparation failure contains submit evidence')
        else:
            expected = 'verified' if row['returncode'] == 0 else 'terminal'
            if receipt.get('state') != expected:
                return False
            if receipt.get('candidate_commit') != json.loads(row['request'])['revision']:
                raise RuntimeError('remote verifier candidate identity changed')
            service_id, task_id = receipt['service_id'], receipt['task_id']
            if not all(re.fullmatch(r'[a-z0-9]{25}', item) for item in (service_id, task_id)):
                raise RuntimeError('invalid retained service/task identity')
            if not re.fullmatch(r'[a-f0-9]{64}', receipt['packet_digest']):
                raise RuntimeError('invalid packet identity')
            if not re.fullmatch(r'[a-f0-9]{64}', receipt['service_spec_sha256']):
                raise RuntimeError('missing service specification binding')
            service = inspect('service', service_id)
            bind_service(service, request_id, receipt['packet_digest'], service_id=service_id,
                         spec_digest=receipt['service_spec_sha256'])
            if docker('service', 'ps', '--no-trunc', '--format', '{{.ID}}', service_id).splitlines() != [task_id]:
                raise RuntimeError('remote verifier task list changed')
            task = inspect('task', task_id)
            if task.get('NodeID') != self.node_id:
                raise RuntimeError('remote verifier task node changed')
            code = terminal_result(task, service_id, task_id=task_id)
            if code is None or code != receipt.get('returncode'):
                return False
            if row['returncode'] != (0 if code == 0 else 1):
                raise RuntimeError('remote verifier return code differs from ledger')
        self._write(dict(state, state='idle', completed_request=request_id))
        return True

    def execute_next(self, service, *, ready, request_id=None):
        if self.lock is None:
            raise RuntimeError('remote dispatch requires exclusive node lock')
        if not self.reconcile():
            raise RuntimeError('remote verifier slot retained; operator reconciliation required')
        if not ready:
            return None
        with self.ledger._db() as db:
            rows = db.execute("SELECT v.* FROM verifications v JOIN claims c ON c.attempt=v.attempt "
                              "WHERE v.state='queued' AND c.state='owned' ORDER BY v.rowid").fetchall()
        row = next((row for row in rows if request_id is None or row['id'] == request_id), None)
        if row is None:
            # Explicit-request absence does not establish that the whole queue
            # is empty. Keep the reservation until a normal idle poll confirms it.
            if not rows and self.path.exists():
                saved = read_record(self.path)
                reservation = saved.get('reservation_id')
                if reservation:
                    active = self.ledger.active_node_reservations()
                    if any(item['reservation_id'] == reservation for item in active):
                        self.ledger.release_node(node=self.node, reservation_id=reservation,
                                                 owner=saved['owner'])
                    self._write(dict(saved, reservation_id=None))
            return None
        request = json.loads(row['request'])
        if self.directory.is_relative_to(Path(request['project']).resolve().parent):
            raise RuntimeError('remote packets must remain outside worker projects')
        saved = read_record(self.path) if self.path.exists() else dict(
            state='idle', node=self.node, node_id=self.node_id, directory=str(self.directory))
        if saved.get('reservation_id'):
            # A crash after ledger release but before clearing the slot must not
            # strand this node forever on a non-reactivatable historical ID.
            # Only an exact released identity permits rotation; absence or an
            # active identity is never treated as permission to steal a role.
            with self.ledger._db() as db:
                history = db.execute('SELECT * FROM node_reservation_history WHERE reservation_id=?',
                                     (saved['reservation_id'],)).fetchone()
            if history is not None:
                if (history['node'], history['owner'], history['purpose']) != (
                        self.node, saved['owner'], 'remote-verification'):
                    raise RuntimeError('remote verifier reservation identity changed')
                if history['state'] == 'released':
                    saved = dict(saved, reservation_id=None)
                    self._write(saved)
        if not saved.get('owner') or not saved.get('reservation_id'):
            saved = dict(saved, owner=saved.get('owner') or 'remote-dispatch-' + secrets.token_hex(16),
                         reservation_id=secrets.token_hex(16))
            self._write(saved)
        # Same SQLite transaction boundary as fresh proof claims. A concurrent
        # proof owner wins cleanly; it is never preempted to create verifier room.
        reservation = self.ledger.reserve_node(node=self.node, reservation_id=saved['reservation_id'],
                                                owner=saved['owner'], purpose='remote-verification')
        if reservation is None:
            return None
        won = False
        def before_spawn(claimed):
            nonlocal won
            if claimed['id'] != row['id'] or claimed['request'] != row['request']:
                raise RuntimeError('selected remote verification request changed')
            self._write(dict(saved, state='reserved', request_id=row['id'],
                             request_sha256=hashlib.sha256(row['request'].encode()).hexdigest()))
            won = True
        # Only the actual winner writes request intent, inside the ledger claim
        # transaction, before spawning. Other-node selectors simply poll again.
        service.execute(row['id'], before_spawn=before_spawn)
        if not won:
            return None
        if not self.reconcile():
            raise RuntimeError('remote verifier slot retained after execution')
        return row['id']
