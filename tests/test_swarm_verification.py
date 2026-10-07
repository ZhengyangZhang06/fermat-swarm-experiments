import copy
import unittest

from _recursive_lean.swarm_verification import bind_service, terminal_result, verify_result_evidence


class SwarmVerificationTests(unittest.TestCase):
    def setUp(self):
        self.service = {'ID': 'service', 'Spec': {'Labels': {'fermat.request': 'request', 'fermat.packet': 'digest'},
                                                'TaskTemplate': {'ContainerSpec': {'Image': 'pinned'}}}}
        self.task = {'ID': 'task', 'ServiceID': 'service', 'Status': {'State': 'running',
                     'ContainerStatus': {'PID': 123, 'ExitCode': 0}}}

    def test_service_binding_detects_changed_identity_labels_and_configuration(self):
        expected = bind_service(self.service, 'request', 'digest', service_id='service')
        for field in ('id', 'label', 'image'):
            changed = copy.deepcopy(self.service)
            if field == 'id':
                changed['ID'] = 'other'
            elif field == 'label':
                changed['Spec']['Labels']['fermat.packet'] = 'other'
            else:
                changed['Spec']['TaskTemplate']['ContainerSpec']['Image'] = 'other'
            with self.subTest(field=field), self.assertRaises(RuntimeError):
                bind_service(changed, 'request', 'digest', service_id='service', spec_digest=expected)

    def test_running_exit_zero_is_not_a_result(self):
        self.assertIsNone(terminal_result(self.task, 'service', task_id='task'))

    def test_terminal_success_and_failure_are_distinct(self):
        self.task['Status'] = {'State': 'complete', 'ContainerStatus': {'PID': 0, 'ExitCode': 0}}
        self.assertEqual(terminal_result(self.task, 'service'), 0)
        self.task['Status'] = {'State': 'failed', 'ContainerStatus': {'PID': 0, 'ExitCode': 1}}
        self.assertEqual(terminal_result(self.task, 'service'), 1)

    def test_lost_or_replaced_tasks_require_reconciliation(self):
        for state in ('orphaned', 'shutdown', 'rejected', 'unknown'):
            self.task['Status']['State'] = state
            with self.subTest(state=state), self.assertRaises(RuntimeError):
                terminal_result(self.task, 'service')
        with self.assertRaisesRegex(RuntimeError, 'identity changed'):
            terminal_result(self.task, 'different-service')
        with self.assertRaisesRegex(RuntimeError, 'identity changed'):
            terminal_result(self.task, 'service', task_id='different-task')

    def test_terminal_status_requires_a_stopped_container_and_consistent_code(self):
        for state, pid, code in [('complete', 123, 0), ('complete', 0, 1), ('failed', 0, 0), ('complete', 0, None)]:
            self.task['Status'] = {'State': state, 'ContainerStatus': {'PID': pid, 'ExitCode': code}}
            with self.subTest(state=state, pid=pid, code=code), self.assertRaises(RuntimeError):
                terminal_result(self.task, 'service')

    def test_verified_evidence_must_match_every_registered_field(self):
        prepared = {'status': 'checking', 'candidate_commit': 'a', 'checked_theorems': ['root', 'child'],
                    'verifier_sha256': 'v', 'dependency_revisions': {'mathlib': 'm'}}
        verified = {**prepared, 'status': 'verified'}
        verify_result_evidence(verified, prepared)
        for key, value in [('candidate_commit', 'b'), ('checked_theorems', ['root']),
                           ('status', 'checking'), ('verifier_sha256', 'other'),
                           ('dependency_revisions', {})]:
            with self.subTest(key=key), self.assertRaises(RuntimeError):
                verify_result_evidence({**verified, key: value}, prepared)
        with self.assertRaises(RuntimeError):
            verify_result_evidence({**verified, 'extra': 'unregistered'}, prepared)


if __name__ == '__main__':
    unittest.main()
