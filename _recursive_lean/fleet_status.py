"""Truthful per-node activity during rolling issue-worker deployments."""

import json
import subprocess
from pathlib import Path


def fleet_generations(directory, generations):
    """Read a required first generation and optional later deployment inputs.

    Catalogs must identify the same repository and projects. Optional snapshots
    cannot invent a generation without its catalog; actual task and heartbeat
    validation still happens separately in ``observed_workers``.
    """
    directory = Path(directory)
    config, snapshots, services = None, [], []
    for catalog_name, snapshot_name, service in generations:
        catalog_path = directory / catalog_name
        if config is not None and not catalog_path.exists():
            continue
        current = json.loads(catalog_path.read_text())
        if config is None:
            config = current
        else:
            registered = {project['id']: project for project in current['projects']}
            if (current['repository'] != config['repository'] or
                    set(registered) != {project['id'] for project in config['projects']}):
                raise ValueError('fleet generation repository or project identities differ')
            for project in config['projects']:
                project['enabled'] = bool(project.get('enabled') or registered[project['id']].get('enabled'))
        snapshot_path = directory / snapshot_name
        if snapshot_path.exists():
            snapshots.append(json.loads(snapshot_path.read_text()))
        services.append(service)
    if config is None:
        raise ValueError('at least one fleet generation is required')
    return config, snapshots, services


def attach_worker_activity(proofs, workers):
    """Attach validated activity without treating unpublished children as ready."""
    executing = {str(worker['issue']): worker['node'] for worker in workers
                 if worker['phase'] == 'working' and worker['issue'] is not None}
    for problem in proofs:
        for node in problem['nodes']:
            issue_url = node.get('issue_url', '')
            pending = not issue_url and node.get('local_id') != 'root'
            node['publication_pending'] = pending
            node['worker_node'] = executing.get(issue_url.rsplit('/', 1)[-1], '') if issue_url else ''
            node['observed_running'] = bool(node['worker_node'])
            node['activity_reason'] = ('pending issue publication' if pending else
                                       'worker ' + node['worker_node'] if node['observed_running'] else
                                       'no active worker observed')


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
