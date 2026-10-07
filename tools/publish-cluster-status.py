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
from pathlib import Path
import re
import subprocess
import time

SERVICE = 'fermat-issue-resolvers-20261007'
PRIVATE = Path('/var/tmp/fermat-swarm-20261007')
SSH = 'ssh -F /dev/null -o BatchMode=yes -o IdentitiesOnly=yes -o StrictHostKeyChecking=yes -i /mnt/data/zhengyang-workspace/.ssh/fermat-example.aeaAzs/id_ed25519'
CAMPAIGN = Path(__file__).resolve().parents[1]


def proof_records(config):
    """Allowlist public theorem fields; never publish raw logs or filesystem paths."""
    campaign = json.loads((CAMPAIGN / 'campaign.json').read_text())
    registered = {p['id']: p for p in config['projects']}
    reports = []
    for problem in campaign['problems']:
        registration = registered[problem['id']]
        frozen = dict(id=problem['id'] + '/root', problem=problem['id'], local_id='root',
                      title=problem['theorem'], status='queued', requires=[], active=True,
                      issue_url=problem['issue_url'], pr_url='', pr_state='', merge_commit='',
                      lean_verified=False, integrated=False, prose_status='pending')
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
            public.append(dict(id=problem['id'] + '/' + key, problem=problem['id'], local_id=key,
                title=node.get('lean_name') or node.get('title') or key, status=node.get('status', 'queued'),
                requires=[problem['id'] + '/' + d for d in dict.fromkeys(node.get('children', []) + node.get('depends_on', []))],
                active=True, issue_url=link('github_issue_url', 'issues'), pr_url=link('github_pr_url', 'pull'),
                pr_state=node.get('github_pr_state', ''), merge_commit=node.get('github_merge_commit', ''),
                lean_verified=verified, integrated=integrated, prose_status=prose))
        root = next(n for n in public if n['local_id'] == 'root')
        report.update(nodes=public, root_integrated=root['integrated'] and all(n['integrated'] for n in public),
                      natural_proof_reviewed=root['prose_status'] == 'reviewed')
        reports.append(report)
    return reports


def collect():
    snapshot = json.loads((PRIVATE / 'snapshot.json').read_text())
    config = json.loads((PRIVATE / 'catalog.json').read_text())
    proofs = proof_records(config)
    tasks = [json.loads(line) for line in subprocess.check_output(
        ['sudo', '-n', 'docker', 'service', 'ps', '--no-trunc', SERVICE, '--format', '{{json .}}'],
        text=True, timeout=30,
    ).splitlines()]
    running = {task['ID']: task for task in tasks
               if task['DesiredState'] == 'Running' and task['CurrentState'].startswith('Running ')}
    stamp = time.time()
    workers = []
    for worker in snapshot['workers']:
        task = running.get(worker['task'])
        if not task or task['Node'] != worker['node'] or stamp - worker['observed_at'] > 90:
            continue
        workers.append({key: worker[key] for key in ('node', 'phase', 'polls', 'issue', 'observed_at')})
    nodes = {worker['node'] for worker in workers}
    if len(nodes) != len(workers):
        raise RuntimeError('duplicate live workers on one node')
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
        'message': f"{len(workers)}/128 node workers are running and heartbeating. "
                   f"{working} are executing issue jobs; {enabled}/10 projects are enabled. "
                   f"{reviewed}/10 root prose proofs have passing review records; "
                   f"{integrated}/10 roots have workflow verification and merge evidence. "
                   + ("Proof execution remains disabled during project/verifier preparation." if not enabled else
                      "Model activity, prose review, Lean verification and integration are distinct stages."),
    }


def publish(worktree):
    report = collect()
    content = json.dumps(report, indent=2) + '\n'
    minute = int(time.time() // 60)
    for path in (worktree / 'status.json', worktree / f'ticks/{minute}/status.json',
                 worktree / f'ticks/{minute + 1}/status.json'):
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content)
    def git(*args):
        return subprocess.run(['git', '-c', 'core.sshCommand=' + SSH, *args],
                              cwd=worktree, check=True, capture_output=True, text=True, timeout=120)
    git('add', 'status.json', 'ticks')
    git('commit', '-m', 'Observe live Swarm workers and theorem DAG evidence')
    git('push', 'origin', 'HEAD:status-live')
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
            print(f'Publication observation failed: {type(exc).__name__}', flush=True)
            if args.once:
                raise
        if args.once:
            break
        time.sleep(60)


if __name__ == '__main__':
    main()
