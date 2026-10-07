import unittest
from _recursive_lean.fleet_status import observed_workers


class FleetStatusTests(unittest.TestCase):
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
