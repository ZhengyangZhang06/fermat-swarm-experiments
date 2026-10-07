#!/usr/bin/env python3
"""Disable legacy intake, enable issue polling, and stop exact legacy containers.

Claims remain held until a separate authoritative terminal reconciliation. This
operator action preserves worktrees and never accepts mathematical evidence.
"""
import argparse
import json
from pathlib import Path
import sqlite3
import subprocess
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from _recursive_lean.store import atomic_text


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--private', required=True, type=Path)
    p.add_argument('--projects', nargs='+', required=True)
    p.add_argument('--legacy-service', required=True)
    args = p.parse_args()
    root = args.private.resolve(strict=True)
    db = sqlite3.connect(f'file:{root / "claims.sqlite"}?mode=ro', uri=True)
    db.row_factory = sqlite3.Row
    targets = []
    for project in args.projects:
        held = db.execute("SELECT * FROM claims WHERE project=? AND state='owned'", (project,)).fetchall()
        if len(held) != 1 or held[0]['scope'] != 'project':
            raise RuntimeError(f'{project}: expected exactly one legacy grant')
        claim = held[0]
        node, task_id, _ = claim['owner'].split('/')
        task = json.loads(subprocess.check_output(['sudo', '-n', 'docker', 'inspect', '--type', 'task', task_id]))[0]
        service = json.loads(subprocess.check_output(['sudo', '-n', 'docker', 'service', 'inspect', args.legacy_service]))[0]
        if task['ServiceID'] != service['ID'] or task['Status']['State'] != 'running':
            raise RuntimeError(f'{project}: task is not the running legacy service')
        node_info = json.loads(subprocess.check_output(['sudo', '-n', 'docker', 'node', 'inspect', task['NodeID']]))[0]
        if node_info['Description']['Hostname'] != node:
            raise RuntimeError('owner node mismatch')
        targets.append(dict(project=project, attempt=claim['attempt'], node=node, task=task_id,
                            container=task['Status']['ContainerStatus']['ContainerID']))
    for name, enabled in [('catalog.json', False), ('parallel-catalog.json', True)]:
        path = root / name
        config = json.loads(path.read_text())
        for project in args.projects:
            entry = next(x for x in config['projects'] if x['id'] == project)
            if enabled and entry.get('issue_runtime_protocol') != 'shared-theorem-issues-v1':
                raise RuntimeError('new catalog lacks shared runtime protocol')
            entry['enabled'] = enabled
            if enabled:
                entry.pop('disabled_reason', None)
            else:
                entry['disabled_reason'] = 'operator-controlled parallel cutover; retain legacy claim until terminal'
        atomic_text(path, json.dumps(config, indent=2) + '\n')
    image = 'python:3.12-bookworm@sha256:5560e9ab8709f459489e5b8aa696eda8a07ef821e14bb122be62d91234bfa98b'
    script = Path(__file__).with_name('stop-owned-swarm-container.py').resolve()
    for target in targets:
        name = f"{target['project']}-handover-{target['attempt'][:8]}"
        old = subprocess.run(['sudo', '-n', 'docker', 'service', 'inspect', name], capture_output=True)
        if old.returncode == 0:
            raise RuntimeError(f'existing handover service: inspect {name} before retrying')
        subprocess.run(['sudo', '-n', 'docker', 'service', 'create', '--detach=true', '--name', name,
                        '--label', 'experiment=fermat-swarm-20261007', '--restart-condition', 'none',
                        '--constraint', f"node.hostname=={target['node']}", '--read-only', '--cap-drop', 'ALL',
                        '--limit-cpu', '0.2', '--limit-memory', '128M',
                        '--mount', 'type=bind,src=/var/run/docker.sock,dst=/var/run/docker.sock',
                        '--mount', f'type=bind,src={script},dst=/stop.py,readonly', image,
                        'python3', '/stop.py', '--container', target['container'], '--task', target['task'],
                        '--service', args.legacy_service], check=True)
        print(json.dumps({**target, 'handover_service': name, 'claim_released': False}), flush=True)


if __name__ == '__main__':
    main()
