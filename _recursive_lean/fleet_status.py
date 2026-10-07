"""Truthful per-node activity during rolling issue-worker deployments."""


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
