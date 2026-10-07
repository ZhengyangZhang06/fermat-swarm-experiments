"""Truthful per-node activity during rolling issue-worker deployments."""

import json
import subprocess


def running_service_tasks(services, *, docker=('sudo', '-n', 'docker')):
    """Observe only existing authorized services, including during retirement.

    A removed generation is expected. A failed inventory or absence of every
    authorized service is not evidence of an empty fleet: let the caller retain
    its previous observation and report the collection failure.
    """
    present = set(subprocess.check_output(
        [*docker, 'service', 'ls', '--format', '{{.Name}}'], text=True, timeout=30,
    ).splitlines())
    selected = list(dict.fromkeys(service for service in services if service in present))
    if not selected:
        raise RuntimeError('no authorized issue-worker service is observable')
    tasks = [json.loads(line) for line in subprocess.check_output(
        [*docker, 'service', 'ps', '--no-trunc', *selected, '--format', '{{json .}}'],
        text=True, timeout=30,
    ).splitlines()]
    return {task['ID']: task for task in tasks
            if task['DesiredState'] == 'Running' and task['CurrentState'].startswith('Running ')}


def observed_workers(snapshots, running_tasks, *, stamp, freshness=90):
    """Collapse idle old/new pollers, but never hide two live jobs on one node."""
    by_node = {}
    for snapshot in snapshots:
        for worker in snapshot.get('workers', []):
            task = running_tasks.get(worker['task'])
            if not task or task['Node'] != worker['node'] or stamp - worker['observed_at'] > freshness:
                continue
            held = by_node.get(worker['node'])
            if held and held['phase'] == worker['phase'] == 'working' and held['task'] != worker['task']:
                raise RuntimeError('two observed active issue jobs on one node')
            if not held or (worker['phase'] == 'working', worker['observed_at']) > (held['phase'] == 'working', held['observed_at']):
                by_node[worker['node']] = worker
    return [{key: worker[key] for key in ('node', 'phase', 'polls', 'issue', 'observed_at')}
            for worker in by_node.values()]
