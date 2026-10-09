#!/usr/bin/env python3
"""Publish allowlisted fleet observations; Swarm task state AND heartbeat required.

Minute-addressed raw snapshots avoid GitHub CDN's fixed-path cache. The durable
proof DAG and its review/merge evidence are separate from worker activity. This
observer does not modify or restart worker services.
"""
import argparse
import datetime
import fcntl
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import time

SERVICE = 'fermat-issue-resolvers-20261007'
PRIVATE = Path('/var/tmp/fermat-swarm-20261007')
SSH = 'ssh -F /dev/null -o BatchMode=yes -o IdentitiesOnly=yes -o StrictHostKeyChecking=yes -i /mnt/data/zhengyang-workspace/.ssh/fermat-example.aeaAzs/id_ed25519'
CAMPAIGN = Path(__file__).resolve().parents[1]
if os.environ.get('THEOREM_WORKFLOW_ROOT'):
    sys.path.insert(0, os.environ['THEOREM_WORKFLOW_ROOT'])
    from _recursive_lean.fleet_status import (
        observed_workers, running_service_tasks, fleet_generations,
        attach_worker_activity as shared_attach_worker_activity,
    )
    from _recursive_lean.verification_status import observe_verifications, attach_verification_activity


def proof_records(config):
    """Allowlist public theorem fields; never publish raw logs or filesystem paths."""
    campaign = json.loads((CAMPAIGN / 'campaign.json').read_text())
    registered = {p['id']: p for p in config['projects']}
    reports = []
    for problem in campaign['problems']:
        registration = registered[problem['id']]
        frozen = dict(id=problem['id'] + '/root', problem=problem['id'], local_id='root',
                      title=problem['theorem'], status='queued', requires=[], active=True,
                      issue_url=problem['issue_url'], issue_state='not checked',
                      pr_url='', pr_state='', merge_commit='',
                      lean_verified=False, accepted=False, integrated=False, prose_status='pending')
        report = dict(id=problem['id'], enabled=bool(registration.get('enabled')), nodes=[frozen],
                      graph_ok=True, root_integrated=False, natural_proof_reviewed=False)
        verification = registration.get('verification')
        if not verification:
            reports.append(report)
            continue
        project = Path(verification['project']).resolve()
        artifacts = project / '.humanize/github-theorem-prover'
        latest = artifacts / 'LATEST'
        if not latest.exists():
            reports.append(report)
            continue
        run = (project / latest.read_text().strip()).resolve()
        if not run.is_relative_to(artifacts.resolve()):
            raise ValueError('invalid proof run pointer')
        if not (run / 'dag.json').exists():
            reports.append(report)
            continue
        payload = json.loads((run / 'dag.json').read_text())
        nodes = {n['id']: n for n in payload['nodes']}
        active, visiting = set(), set()
        def visit(key):
            if key in visiting or key not in nodes:
                raise ValueError('cyclic or missing theorem dependency')
            if key in active:
                return
            visiting.add(key)
            for dep in nodes[key].get('children', []) + nodes[key].get('depends_on', []):
                visit(dep)
            visiting.remove(key)
            active.add(key)
        if 'root' not in nodes:
            reports.append(report)
            continue
        visit('root')
        public = []
        for key in sorted(active):
            node = nodes[key]
            def link(field, kind):
                value = node.get(field, '')
                return value if re.fullmatch(r'https://github\.com/' + re.escape(config['repository'])
                                             + '/' + kind + r'/[1-9][0-9]*', value) else ''
            verified = node.get('status') == 'proved' and bool(node.get('integrated_commit'))
            integrated = verified and node.get('github_pr_state') == 'merged' and bool(node.get('github_merge_commit'))
            prose = 'checkpoint recorded' if node.get('natural_proof') else 'pending'
            proof_path = (project / node.get('natural_proof', '')).resolve()
            match = re.fullmatch(r'natural-proof-v([0-9]+)\.md', proof_path.name)
            if match and proof_path.is_relative_to(run) and proof_path.is_file():
                audit_path = proof_path.with_name('natural-audit-v' + match[1] + '.json')
                if audit_path.exists():
                    audit = json.loads(audit_path.read_text())
                    if audit.get('acceptable') and not audit.get('first_invalid_step') and not audit.get('required_changes'):
                        prose = 'reviewed'
            # A later decomposition audit can expose a mathematical gap and
            # send the root back to revision. Its old passing artifact remains
            # useful history, but is not acceptance of the current argument.
            if node.get('status') == 'natural-proof':
                prose = 'revising' if node.get('natural_proof') else 'drafting'
            elif node.get('status') == 'natural-review':
                prose = 'under review'
            public.append(dict(id=problem['id'] + '/' + key, problem=problem['id'], local_id=key,
                title=node.get('lean_name') or node.get('title') or key, status=node.get('status', 'queued'),
                requires=[problem['id'] + '/' + d for d in dict.fromkeys(node.get('children', []) + node.get('depends_on', []))],
                active=True, issue_url=problem['issue_url'] if key == 'root' else link('github_issue_url', 'issues'),
                issue_state=node.get('github_issue_state') if node.get('github_issue_state') in ('open', 'closed') else 'not checked',
                pr_url=link('github_pr_url', 'pull'),
                pr_state=node.get('github_pr_state', ''), merge_commit=node.get('github_merge_commit', ''),
                lean_verified=verified, integrated=integrated, prose_status=prose,
                accepted=node.get('status') == 'proved' or (
                    node.get('status') == 'integrating' and bool(node.get('candidate_commit')))))
        root = next(n for n in public if n['local_id'] == 'root')
        report.update(nodes=public, root_integrated=root['integrated'] and all(n['integrated'] for n in public),
                      natural_proof_reviewed=root['prose_status'] == 'reviewed')
        reports.append(report)
    return reports


def attach_worker_activity(proofs, workers):
    """A prepared/decomposing DAG node is not necessarily executing on a worker.

    Call only with workers already validated against live Swarm tasks and fresh
    heartbeats. An absent match reports lack of observation, not eligibility.
    """
    if os.environ.get('THEOREM_WORKFLOW_ROOT'):
        return shared_attach_worker_activity(proofs, workers)
    executing = {str(w['issue']): w['node'] for w in workers
                 if w['phase'] == 'working' and w['issue'] is not None}
    for problem in proofs:
        for node in problem['nodes']:
            issue = node['issue_url'].rsplit('/', 1)[-1]
            node['worker_node'] = executing.get(issue, '')
            node['observed_running'] = bool(node['worker_node'])


def collect():
    snapshot = json.loads((PRIVATE / 'snapshot.json').read_text())
    config = json.loads((PRIVATE / 'catalog.json').read_text())
    snapshots = [snapshot]
    services = [SERVICE]
    if os.environ.get('THEOREM_WORKFLOW_ROOT'):
        config, snapshots, services = fleet_generations(PRIVATE, [
            ('catalog.json', 'snapshot.json', SERVICE),
            ('parallel-catalog.json', 'parallel-snapshot.json', 'fermat-parallel-resolvers-20261007'),
            ('recovery-catalog.json', 'recovery-snapshot.json', 'fermat-recovery-resolvers-20261007'),
        ])
    proofs = proof_records(config)
    if os.environ.get('THEOREM_WORKFLOW_ROOT'):
        running = running_service_tasks(services)
    else:
        tasks = [json.loads(line) for line in subprocess.check_output(
            ['sudo', '-n', 'docker', 'service', 'ps', '--no-trunc', *services, '--format', '{{json .}}'],
            text=True, timeout=30,
        ).splitlines()]
        running = {task['ID']: task for task in tasks
                   if task['DesiredState'] == 'Running' and task['CurrentState'].startswith('Running ')}
    stamp = time.time()
    if os.environ.get('THEOREM_WORKFLOW_ROOT'):
        selected_workers = observed_workers(snapshots, running, stamp=stamp)
    else:
        selected_workers = None
    workers = []
    for worker in snapshot['workers']:
        task = running.get(worker['task'])
        if not task or task['Node'] != worker['node'] or stamp - worker['observed_at'] > 90:
            continue
        workers.append({key: worker[key] for key in ('node', 'phase', 'polls', 'issue', 'observed_at')})
    nodes = {worker['node'] for worker in workers}
    if len(nodes) != len(workers):
        raise RuntimeError('duplicate live workers on one node')
    if selected_workers is not None:
        workers = selected_workers
    attach_worker_activity(proofs, workers)
    verification_activity = dict(available=False, observed_at=stamp, counts=None, nodes=[])
    if os.environ.get('THEOREM_WORKFLOW_ROOT'):
        verification_activity = observe_verifications(PRIVATE / 'claims.sqlite', config['repository'], stamp=stamp)
        attach_verification_activity(proofs, verification_activity, config['repository'], stamp=stamp)
    enabled = sum(bool(p.get('enabled')) for p in config['projects'])
    working = sum(worker['phase'] == 'working' for worker in workers)
    integrated = sum(p['root_integrated'] for p in proofs)
    reviewed = sum(p['natural_proof_reviewed'] for p in proofs)
    return {
        'observed_at': datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'phase': 'proving' if enabled else 'project-validation', 'readiness_passed': 128,
        'running_resolvers': len(workers), 'working_resolvers': working,
        'verified_integrated_roots': integrated, 'reviewed_natural_proofs': reviewed,
        'proof_feed_active': True, 'enabled_projects': enabled, 'problems': proofs,
        'workers': sorted(workers, key=lambda worker: int(worker['node'][3:])),
        'verification_activity': {key: verification_activity[key] for key in ('available', 'observed_at', 'counts')},
        'message': f"{len(workers)}/128 node workers are running and heartbeating. "
                   f"{working} are executing issue jobs; {enabled}/10 projects are enabled. "
                   f"{reviewed}/10 current root prose proofs have passed review; "
                   f"{integrated}/10 roots have workflow verification and merge evidence. "
                   + ("Proof execution remains disabled during project/verifier preparation." if not enabled else
                      "Model activity, prose review, Lean verification and integration are distinct stages."),
    }


def publish_snapshot(worktree, content, minute):
    """Publish only this observation without sharing a checkout's Git index.

    An interrupted Git command can leave index.lock behind. Each attempt uses a
    fresh local index, so that lock cannot block later observations or require
    guessing whether another process owns it. The ordinary index is untouched.
    """
    paths = [Path('status.json'), Path(f'ticks/{minute}/status.json'),
             Path(f'ticks/{minute + 1}/status.json')]
    for relative in paths:
        path = worktree / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content)
    with tempfile.TemporaryDirectory(prefix='fermat-status-index-') as temporary:
        environment = {**os.environ, 'GIT_INDEX_FILE': str(Path(temporary) / 'index')}

        def git(*args):
            try:
                return subprocess.run(['git', '-c', 'core.sshCommand=' + SSH, *args],
                                      cwd=worktree, env=environment, check=True,
                                      capture_output=True, text=True, timeout=120).stdout.strip()
            except subprocess.CalledProcessError as error:
                # Identify the failed step without logging arbitrary remote stderr.
                raise RuntimeError(f'Status Git {args[0]} failed (exit {error.returncode})') from error
            except subprocess.TimeoutExpired as error:
                raise RuntimeError(f'Status Git {args[0]} timed out') from error

        parent = git('rev-parse', 'HEAD')
        git('read-tree', parent)
        git('add', '--', *(str(path) for path in paths))
        tree = git('write-tree')
        if tree != git('rev-parse', parent + '^{tree}'):
            commit = git('commit-tree', tree, '-p', parent, '-m',
                         'Observe live Swarm workers and theorem DAG evidence')
            # Fail rather than overwrite another writer's concurrent branch update.
            git('update-ref', 'HEAD', commit, parent)
        # A prior push may have failed after creating a local commit. Retry even
        # if collection returned the same observation, without inventing freshness.
        git('push', 'origin', 'HEAD:status-live')


def publish(worktree):
    report = collect()
    content = json.dumps(report, indent=2) + '\n'
    minute = int(time.time() // 60)
    publish_snapshot(worktree, content, minute)
    print(json.dumps({'observed_at': report['observed_at'], 'running_resolvers': report['running_resolvers']}), flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--worktree', type=Path, required=True)
    parser.add_argument('--once', action='store_true')
    args = parser.parse_args()
    lock_dir = args.worktree / '.humanize'
    lock_dir.mkdir(exist_ok=True)
    lock = (lock_dir / 'status-publisher.lock').open('a')
    try:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError:
        raise SystemExit('This status worktree already has a publisher')
    while True:
        try:
            publish(args.worktree)
        except Exception as exc:
            detail = str(exc) if isinstance(exc, RuntimeError) and str(exc).startswith('Status Git ') else type(exc).__name__
            print(f'Publication observation failed: {detail}', flush=True)
            if args.once:
                raise
        if args.once:
            break
        time.sleep(60)


if __name__ == '__main__':
    main()
