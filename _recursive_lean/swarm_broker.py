"""Authenticated single-writer ownership broker; workers select issues themselves.

The catalogue is operator-owned, not executable instructions from GitHub issues.
SQLite must reside on the broker's local disk. TLS is mandatory on the CLI.
"""
from __future__ import annotations

import argparse
import datetime
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
import json
import os
from pathlib import Path
import re
import secrets
import ssl
import subprocess
import threading
import time

from .distributed_claims import ClaimLedger, OwnershipError
from .store import atomic_text
from .remote_verification import VerificationService
from .parallel import PROTOCOL, child_publication_pending, child_publication_checkpoint


def authorized_node_name(value: str) -> str:
    if not isinstance(value, str) or not re.fullmatch(
            r'hoa(?:[0-9]|[1-9][0-9]|1[01][0-9]|12[0-7])', value):
        raise ValueError('worker node outside the authorized fleet')
    return value


def runner_runtime_path(value: str | Path) -> str:
    """Accept exactly one operator-selected archive in the worker runtime mount.

    This path is interpreted inside the worker container, not on the broker.
    Deployment must mount the selected immutable archive; issue bodies and worker
    requests cannot choose it.
    """
    if not isinstance(value, (str, Path)):
        raise ValueError('runner runtime must be an absolute archive path')
    value = str(value)
    if not re.fullmatch(r'/runtime/flows/[A-Za-z0-9][A-Za-z0-9_.-]{0,127}', value):
        raise ValueError('runner runtime must name one archive under /runtime/flows')
    return value


class Broker:
    def __init__(self, catalog: Path, ledger: ClaimLedger, token: str, snapshot: Path, gh: str,
                 *, runner_runtime: str | Path | None = None, reserved_nodes=()):
        if len(token) < 32:
            raise ValueError('broker token too short')
        self.catalog, self.ledger, self.token, self.snapshot, self.gh = catalog, ledger, token, snapshot, gh
        self.runner_runtime = runner_runtime_path(runner_runtime) if runner_runtime is not None else None
        # Startup-only operator policy, never read from a worker or mutable catalog.
        self._reserved_nodes = frozenset(authorized_node_name(node) for node in reserved_nodes)
        self.lock = threading.RLock()
        self.workers = {}
        self.cache = {}
        self.last_saved = 0.0
        self.verifier = None

    @property
    def reserved_nodes(self):
        return self._reserved_nodes

    def configuration(self):
        config = json.loads(self.catalog.read_text())
        if not isinstance(config.get('projects'), list):
            raise ValueError('invalid operator catalogue')
        return config

    @staticmethod
    def parallel(project):
        protocol = project.get('issue_runtime_protocol', '')
        if protocol not in ('', PROTOCOL):
            raise ValueError('unsupported registered issue runtime protocol')
        return protocol == PROTOCOL

    def check_generation(self, held):
        protocol = self.configuration().get('broker_protocol')
        if protocol and (not held or json.loads(held['job']).get('environment', {}).get('HUMANIZE_SWARM_PROTOCOL') != protocol):
            raise OwnershipError('claim belongs to another broker generation')

    def github(self, repository, resource):
        if not re.fullmatch(r'[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+', repository):
            raise ValueError('invalid repository')
        args = [self.gh, 'api', f'repos/{repository}/{resource}']
        paginated = resource.startswith('issues?')
        if paginated:
            args += ['--paginate', '--slurp']
        result = subprocess.run(args, capture_output=True, text=True, timeout=60, check=True)
        data = json.loads(result.stdout)
        return [one for page in data for one in page] if paginated else data

    def issues(self):
        """Coalesce GitHub reads, not worker choices; never fabricate ready work."""
        with self.lock:
            config = self.configuration()
            repository = config['repository']
            cached = self.cache.get(repository)
            if not cached or time.monotonic() - cached[0] > 45:
                rows = self.github(repository, 'issues?state=open&per_page=100')
                self.cache[repository] = (time.monotonic(), rows)
            else:
                rows = cached[1]
            open_issues = {int(row['number']): row for row in rows if not row.get('pull_request')}
            claims = self.ledger.active()
            owned = {one['project'] for one in claims}
            exclusive = {one['project'] for one in claims if one.get('scope', 'project') == 'project'}
            issues_owned = {(one['repository'], one['issue']) for one in claims}
            jobs = []
            for project in config['projects']:
                parallel = self.parallel(project)
                if not project.get('enabled') or project['id'] in (exclusive if parallel else owned):
                    continue
                # The runtime rechecks the actual DAG after the claim. This list
                # is an availability hint, never an acceptance/eligibility gate.
                for issue in self.project_issues(project, repository):
                    if (issue in open_issues
                            and (repository.casefold(), issue) not in issues_owned
                            and issue not in project.get('quarantined_issues', [])):
                        jobs.append({'project': project['id'], 'issue': issue,
                                     'title': open_issues[issue]['title']})
            return {'issues': jobs, 'open_issues': len(open_issues),
                    'enabled_projects': sum(bool(p.get('enabled')) for p in config['projects'])}

    @staticmethod
    def project_issues(project, repository):
        """Read published DAG leaves; parents never notify or assign workers.

        These are availability hints only. The proof runtime independently
        rechecks contracts, handoffs, dependencies and acceptance after claiming.
        """
        registered = project.get('verification')
        if not registered:
            return project.get('issue_numbers', [project['root_issue']])
        root = Path(registered['project']).resolve()
        artifacts = root / '.humanize/github-theorem-prover'
        latest = artifacts / 'LATEST'
        if not latest.exists():
            return [project['root_issue']]
        run = (root / latest.read_text().strip()).resolve()
        if not run.is_relative_to(artifacts.resolve()):
            raise ValueError('run pointer outside registered project')
        dag_path = run / 'dag.json'
        if not dag_path.exists():
            return [project['root_issue']]
        nodes = {node['id']: node for node in json.loads(dag_path.read_text())['nodes']}
        if 'root' not in nodes:
            return [project['root_issue']]
        active, pending = set(), ['root']
        while pending:
            key = pending.pop()
            if key in active:
                continue
            active.add(key)
            if key not in nodes:
                raise ValueError('missing dependency in registered DAG')
            pending.extend(nodes[key].get('children', []) + nodes[key].get('depends_on', []))
        available = []
        for key in active:
            node = nodes[key]
            if node.get('status') == 'proved' and not Broker.parallel(project):
                continue
            if key != 'root' and not all(node.get(field) for field in
                    ('workspace_handoff_commit', 'workspace_bundle_path', 'parent_handoff')):
                continue
            dependencies = node.get('children', []) + node.get('depends_on', [])
            recovery = Broker.parallel(project) and child_publication_pending(node, nodes)
            if recovery:
                try:
                    child_publication_checkpoint(root, run, node, nodes)
                except (OSError, ValueError, KeyError):
                    continue
            if not recovery and any(nodes[d].get('status') != 'proved' for d in dependencies):
                continue
            match = re.fullmatch(r'https://github\.com/' + re.escape(repository) + r'/issues/([1-9][0-9]*)',
                                 node.get('github_issue_url', ''))
            if match:
                available.append(int(match[1]))
            elif key == 'root':
                available.append(project['root_issue'])
        return sorted(set(available))

    @staticmethod
    def identity(body):
        node, task, boot = (body.get(key, '') for key in ('node', 'task', 'boot'))
        authorized_node_name(node)
        if not all(re.fullmatch(r'[A-Za-z0-9_-]{8,80}', x) for x in (task, boot)):
            raise ValueError('invalid worker process identity')
        return f'{node}/{task}/{boot}'

    def heartbeat(self, body):
        owner = self.identity(body)
        phase = body.get('phase')
        if phase not in {'starting', 'polling', 'idle', 'working', 'error', 'uncertain', 'stopped'}:
            raise ValueError('invalid worker phase')
        with self.lock:
            self.workers[owner] = {
                'node': body['node'], 'task': body['task'], 'boot': body['boot'],
                'phase': phase, 'observed_at': time.time(),
                'issue': body.get('issue') if type(body.get('issue')) is int else None,
                'polls': int(body.get('polls', 0)),
            }
            if time.monotonic() - self.last_saved > 5:
                atomic_text(self.snapshot, json.dumps({
                    'observed_at': datetime.datetime.now(datetime.UTC).isoformat(),
                    'workers': list(self.workers.values()),
                    # Deliberately no tokens or process receipts in the snapshot.
                    'claims': [{k: r[k] for k in ('project', 'repository', 'issue', 'owner', 'created')}
                               for r in self.ledger.active()],
                }, indent=2) + '\n')
                self.last_saved = time.monotonic()
        return {'ok': True}

    def claim(self, body):
        owner = self.identity(body)
        held = self.ledger.lookup(body['attempt'], owner)
        if held:
            self.check_generation(held)
            if held['project'] != body.get('project') or held['issue'] != body.get('issue'):
                raise OwnershipError('attempt identity changed')
            return {'claim': held, 'job': json.loads(held['job'])} if held['state'] == 'owned' else {'claim': None}
        if body['node'] in self.reserved_nodes:
            # A reservation is not a claim or cancellation. Held jobs above keep
            # their immutable grant, and observe/release remain available.
            return {'claim': None}
        config = self.configuration()
        project = next((p for p in config['projects'] if p['id'] == body.get('project')), None)
        if not project or not project.get('enabled'):
            return {'claim': None}
        issue = body.get('issue')
        if issue in project.get('quarantined_issues', []):
            return {'claim': None}
        if type(issue) is not int or issue not in self.project_issues(project, config['repository']):
            raise ValueError('issue is outside the registered project')
        # Ownership never follows an arbitrary issue-body shell command.
        command = project.get('command')
        if not isinstance(command, list) or not command or not all(isinstance(a, str) for a in command):
            raise ValueError('registered runner is missing')
        if self.runner_runtime is not None:
            # Only fresh grants use the operator override. The held-claim path
            # above returns its immutable ledger job, even after broker restart.
            # Never rewrite the shared catalogue or its quarantine state.
            command = ['python3', self.runner_runtime + '/scripts/swarm-run-issue.py']
        current = self.github(config['repository'], f'issues/{issue}')
        if current.get('state') != 'open' or current.get('pull_request'):
            return {'claim': None}
        parallel = self.parallel(project)
        environment = dict(project.get('environment', {}))
        if parallel:
            environment['HUMANIZE_SWARM_PROTOCOL'] = PROTOCOL
        else:
            environment.pop('HUMANIZE_SWARM_PROTOCOL', None)
        job = {
            'cwd': project['cwd'], 'command': command,
            'environment': environment,
            'log_directory': project['log_directory'],
            'verification': project.get('verification'),
        }
        claim = self.ledger.claim(project=project['id'], repository=config['repository'],
                                  issue=issue, owner=owner, attempt=body['attempt'], job=job, parallel=parallel)
        if not claim:
            return {'claim': None}
        return {'claim': claim, 'job': json.loads(claim['job'])}

    def observe(self, body):
        owner = self.identity(body)
        self.check_generation(self.ledger.lookup(body['attempt'], owner))
        self.ledger.observe(body['attempt'], owner, body['claim_token'], body['receipt'])
        return {'ok': True}

    def release(self, body):
        # Serialize release with verifier registration: no late request may
        # start after the project has been released to a different worker.
        with self.lock:
            return self._release(body)

    def _release(self, body):
        owner = self.identity(body)
        self.check_generation(self.ledger.lookup(body['attempt'], owner))
        if self.verifier and self.verifier.pending(body['attempt']):
            raise OwnershipError('verification processes are not yet terminal')
        if body.get('processes_remaining') != 0 or type(body.get('returncode')) is not int:
            raise OwnershipError('process-tree termination has not been established')
        self.ledger.release(body['attempt'], owner, body['claim_token'], body['outcome'])
        if body['returncode'] != 0:
            # A broken runner is not an invitation to spend model calls forever.
            # Preserve its released receipt and require an operator to re-enable it.
            held = self.ledger.lookup(body['attempt'], owner)
            with self.lock:
                config = self.configuration()
                for project in config['projects']:
                    if project['id'] == held['project']:
                        if held.get('scope') == 'issue':
                            project['quarantined_issues'] = sorted(set(project.get('quarantined_issues', [])) | {held['issue']})
                        else:
                            project.update(enabled=False, disabled_reason='nonzero runner exit; inspect before retry')
                atomic_text(self.catalog, json.dumps(config, indent=2) + '\n')
        return {'ok': True}

    def verify(self, body):
        with self.lock:
            self.check_generation(self.ledger.lookup(body['attempt'], self.identity(body)))
            if not self.verifier:
                raise ValueError('verifier service not configured')
            return self.verifier.submit(self.identity(body), body, ready=bool(self.configuration().get('verifier_ready')))


def handler(broker):
    class Handler(BaseHTTPRequestHandler):
        def log_message(self, fmt, *args):
            pass  # Neither credentials nor request bodies enter access logs.

        def answer(self, status, payload):
            raw = json.dumps(payload).encode()
            self.send_response(status)
            self.send_header('Content-Type', 'application/json')
            self.send_header('Content-Length', str(len(raw)))
            self.end_headers()
            self.wfile.write(raw)

        def authorized(self):
            if not secrets.compare_digest(self.headers.get('Authorization', '').encode(), ('Bearer ' + broker.token).encode()):
                self.answer(401, {'error': 'unauthorized'})
                return False
            return True

        def do_GET(self):
            if not self.authorized():
                return
            try:
                if self.path == '/issues':
                    self.answer(200, broker.issues())
                elif self.path == '/health':
                    self.answer(200, {'ok': True, 'ownership': 'durable-non-expiring'})
                else:
                    self.answer(404, {'error': 'not found'})
            except Exception as exc:
                self.answer(503, {'error': type(exc).__name__})

        def do_POST(self):
            if not self.authorized():
                return
            try:
                length = int(self.headers.get('Content-Length', '0'))
                if length < 1 or length > 65536:
                    raise ValueError('invalid request size')
                self.connection.settimeout(30)
                body = json.loads(self.rfile.read(length))
                routes = {'/heartbeat': broker.heartbeat, '/claim': broker.claim,
                          '/observe': broker.observe, '/release': broker.release,
                          '/verify': broker.verify}
                if self.path not in routes:
                    self.answer(404, {'error': 'not found'})
                    return
                self.answer(200, routes[self.path](body))
            except (ValueError, KeyError, TypeError):
                self.answer(400, {'error': 'invalid request'})
            except OwnershipError:
                self.answer(409, {'error': 'ownership mismatch'})
            except Exception as exc:
                self.answer(503, {'error': type(exc).__name__})
    return Handler


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ('catalog', 'database', 'token_file', 'snapshot', 'certificate', 'key'):
        parser.add_argument('--' + name.replace('_', '-'), required=True, type=Path)
    parser.add_argument('--bind', required=True)
    parser.add_argument('--port', type=int, default=8847)
    parser.add_argument('--gh', default='gh')
    parser.add_argument('--verifier', type=Path)
    parser.add_argument('--runner-runtime', type=runner_runtime_path,
                        help='Operator-selected /runtime/flows/<archive> for new grants only')
    parser.add_argument('--reserve-node', action='append', default=[], type=authorized_node_name,
                        help='Reserve an authorized physical node from new proof claims (repeatable)')
    parser.add_argument('--preserve-existing-verifications', action='store_true',
                        help='Additive broker: leave other live controllers and their receipts unchanged')
    args = parser.parse_args()
    os.umask(0o077)
    broker = Broker(args.catalog, ClaimLedger(args.database), args.token_file.read_text().strip(), args.snapshot, args.gh,
                    runner_runtime=args.runner_runtime, reserved_nodes=args.reserve_node)
    if args.verifier:
        import sys
        broker.verifier = VerificationService(broker.ledger, args.database.parent / 'verification', args.verifier, sys.executable,
                                             recover_existing=not args.preserve_existing_verifications,
                                             claim_protocol=broker.configuration().get('broker_protocol'))
    class FleetServer(ThreadingHTTPServer):
        request_queue_size = 256
    server = FleetServer((args.bind, args.port), handler(broker))
    context = ssl.SSLContext(ssl.PROTOCOL_TLS_SERVER)
    context.load_cert_chain(args.certificate, args.key)
    server.socket = context.wrap_socket(server.socket, server_side=True)
    print('Swarm ownership broker listening with TLS', flush=True)
    server.serve_forever(poll_interval=1)


if __name__ == '__main__':
    main()
