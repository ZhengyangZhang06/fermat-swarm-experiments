import unittest
import json
import subprocess
from unittest.mock import patch
from _recursive_lean.fleet_status import observed_workers, running_service_tasks


class FleetStatusTests(unittest.TestCase):
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
