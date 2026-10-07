import unittest
import json
import subprocess
import tempfile
from pathlib import Path
from unittest.mock import patch
from _recursive_lean.fleet_status import (
    observed_workers, running_service_tasks, fleet_generations, attach_worker_activity,
)


class FleetStatusTests(unittest.TestCase):
    def test_optional_recovery_generation_requires_catalog_and_retains_identity(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            base = dict(repository='owner/repo', projects=[dict(id='p1', enabled=False)])
            (root / 'base.json').write_text(json.dumps(base))
            (root / 'base-snapshot.json').write_text(json.dumps(dict(workers=[])))
            (root / 'recovery-snapshot.json').write_text(json.dumps(dict(workers=[dict(issue=7)])))
            generations = [('base.json', 'base-snapshot.json', 'old'),
                           ('recovery.json', 'recovery-snapshot.json', 'recovery')]
            config, snapshots, services = fleet_generations(root, generations)
            self.assertEqual(services, ['old'])
            self.assertEqual(len(snapshots), 1)
            base['projects'][0]['enabled'] = True
            (root / 'recovery.json').write_text(json.dumps(base))
            config, snapshots, services = fleet_generations(root, generations)
            self.assertTrue(config['projects'][0]['enabled'])
            self.assertEqual(services, ['old', 'recovery'])
            self.assertEqual(len(snapshots), 2)
            base['repository'] = 'other/repo'
            (root / 'recovery.json').write_text(json.dumps(base))
            with self.assertRaisesRegex(ValueError, 'identities differ'):
                fleet_generations(root, generations)

    def test_three_generations_deduplicate_node_without_hiding_recovery_job(self):
        idle = dict(node='hoa1', task='parallel', phase='idle', issue=None, polls=3, observed_at=101)
        recovery = dict(idle, task='recovery', phase='working', issue=7, observed_at=100)
        old = dict(idle, task='retired', phase='working', issue=2, observed_at=100)
        tasks = {key: {'Node': 'hoa1'} for key in ('parallel', 'recovery')}
        workers = observed_workers([{'workers': [old]}, {'workers': [idle]}, {'workers': [recovery]}],
                                   tasks, stamp=102)
        self.assertEqual(len(workers), 1)
        self.assertEqual(workers[0]['issue'], 7)
        recovery['observed_at'] = 0
        workers = observed_workers([{'workers': [idle]}, {'workers': [recovery]}], tasks, stamp=102)
        self.assertEqual(workers[0]['phase'], 'idle')

    def test_unpublished_child_is_pending_publication_not_running(self):
        child = dict(local_id='child', issue_url='', status='planning')
        published = dict(local_id='sibling', issue_url='https://github.com/o/r/issues/7')
        attach_worker_activity([dict(nodes=[child, published])],
                               [dict(phase='working', issue=7, node='hoa1')])
        self.assertTrue(child['publication_pending'])
        self.assertFalse(child['observed_running'])
        self.assertEqual(child['status'], 'planning')
        self.assertEqual(child['activity_reason'], 'pending issue publication')
        self.assertFalse(published['publication_pending'])
        self.assertTrue(published['observed_running'])

    def test_retired_service_is_omitted_but_unrelated_services_are_not_observed(self):
        task = {'ID': 'newtask', 'Node': 'hoa1', 'DesiredState': 'Running', 'CurrentState': 'Running 1 minute ago'}
        with patch('_recursive_lean.fleet_status.subprocess.check_output',
                   side_effect=['new\nunrelated\n', json.dumps(task) + '\n']) as call:
            self.assertEqual(running_service_tasks(['old', 'new']), {'newtask': task})
        self.assertEqual(call.call_args.args[0], ['sudo', '-n', 'docker', 'service', 'ps',
                                                '--no-trunc', 'new', '--format', '{{json .}}'])

    def test_missing_fleet_or_failed_inventory_is_not_an_empty_successful_observation(self):
        with patch('_recursive_lean.fleet_status.subprocess.check_output', return_value='unrelated\n') as call:
            with self.assertRaisesRegex(RuntimeError, 'no authorized'):
                running_service_tasks(['old', 'new'])
            self.assertEqual(call.call_count, 1)
        with patch('_recursive_lean.fleet_status.subprocess.check_output',
                   side_effect=subprocess.CalledProcessError(1, ['docker'])):
            with self.assertRaises(subprocess.CalledProcessError):
                running_service_tasks(['new'])

    def test_terminal_or_replaced_tasks_do_not_count_as_running(self):
        tasks = [dict(ID='ended', DesiredState='Running', CurrentState='Failed 1 minute ago'),
                 dict(ID='replaced', DesiredState='Shutdown', CurrentState='Running 1 minute ago')]
        with patch('_recursive_lean.fleet_status.subprocess.check_output',
                   side_effect=['new\n', '\n'.join(json.dumps(t) for t in tasks)]):
            self.assertEqual(running_service_tasks(['new']), {})

    def test_new_and_legacy_pollers_do_not_hide_active_jobs(self):
        old = dict(node='hoa1', task='old', phase='working', issue=21, polls=3, observed_at=100)
        new = dict(node='hoa1', task='new', phase='idle', issue=None, polls=5, observed_at=101)
        tasks = {key: {'Node': 'hoa1'} for key in ('old', 'new')}
        self.assertEqual(observed_workers([{'workers': [old]}, {'workers': [new]}], tasks, stamp=102)[0]['issue'], 21)
        old['phase'] = 'idle'
        new.update(phase='working', issue=22)
        self.assertEqual(observed_workers([{'workers': [old]}, {'workers': [new]}], tasks, stamp=102)[0]['issue'], 22)

    def test_stale_missing_or_wrong_node_task_is_not_reported_running(self):
        worker = dict(node='hoa1', task='task', phase='working', issue=21, polls=3, observed_at=0)
        for tasks, stamp in (({}, 1), ({'task': {'Node': 'hoa2'}}, 1), ({'task': {'Node': 'hoa1'}}, 100)):
            self.assertEqual(observed_workers([{'workers': [worker]}], tasks, stamp=stamp), [])

    def test_two_active_jobs_on_one_node_is_an_error_not_hidden(self):
        a = dict(node='hoa1', task='old', phase='working', issue=21, polls=3, observed_at=100)
        b = dict(a, task='new', issue=22)
        with self.assertRaises(RuntimeError):
            observed_workers([{'workers': [a, b]}], {'old': {'Node': 'hoa1'}, 'new': {'Node': 'hoa1'}}, stamp=101)
