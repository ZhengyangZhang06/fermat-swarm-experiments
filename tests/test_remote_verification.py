import json
import os
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import Mock
from unittest.mock import patch

from _recursive_lean.distributed_claims import ClaimLedger, OwnershipError
from _recursive_lean.remote_verification import VerificationService


class RemoteVerificationTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.project = self.root / 'project'
        self.project.mkdir()
        self.ledger = ClaimLedger(self.root / 'claims.sqlite')
        self.registration = dict(project=str(self.project), source_commit='a' * 40,
                                 root_name='frozen', contract_file='Submission.lean')
        self.claim = self.ledger.claim(project='p01', repository='owner/repo', issue=1,
            owner='worker', attempt='attempt01', job={'verification': self.registration})
        self.program = self.root / 'verifier.py'
        self.program.write_text('import os\nprint(os.environ["FERMAT_ROOT_NAME"])\n')
        self.service = VerificationService(self.ledger, self.root / 'logs', self.program, sys.executable)
        self.addCleanup(self.service.pool.shutdown)
        self.body = dict(attempt='attempt01', claim_token=self.claim['token'], request_id='b' * 32,
                         revision='c' * 40, candidate=str(self.project),
                         run_directory=str(self.project / '.humanize' / 'run'), node_id='root')

    def test_not_ready_queues_without_process_or_fake_success(self):
        result = self.service.submit('worker', self.body, ready=False)
        self.assertEqual(result['state'], 'queued')
        self.assertTrue(self.service.pending('attempt01'))
        self.assertFalse(self.service.futures)
        self.assertNotIn('returncode', result)

    def test_same_request_retries_one_process_and_returns_exact_identity(self):
        self.service.submit('worker', self.body, ready=True)
        self.service.futures[self.body['request_id']].result(timeout=10)
        result = self.service.submit('worker', self.body, ready=True)
        self.assertEqual(result['state'], 'finished')
        self.assertEqual(result['revision'], 'c' * 40)
        self.assertEqual(result['returncode'], 0)
        self.assertEqual(result['output'], 'frozen\n')
        self.assertEqual(len(self.service.futures), 1)
        self.assertFalse(self.service.pending('attempt01'))

    def test_registration_wins_over_worker_fields(self):
        self.service.submit('worker', {**self.body, 'root_name': 'fake', 'source_commit': 'd' * 40}, ready=False)
        with self.ledger._db() as db:
            row = db.execute('SELECT request FROM verifications').fetchone()
        self.assertEqual(json.loads(row['request'])['root_name'], 'frozen')
        self.assertEqual(json.loads(row['request'])['source_commit'], 'a' * 40)

    def test_identity_reuse_cannot_change_revision(self):
        self.service.submit('worker', self.body, ready=False)
        with self.assertRaises(OwnershipError):
            self.service.submit('worker', {**self.body, 'revision': 'd' * 40}, ready=False)

    def test_wrong_owner_or_capability_and_released_claim_rejected(self):
        for owner, token in [('different', self.claim['token']), ('worker', 'wrong')]:
            with self.assertRaises(OwnershipError):
                self.service.submit(owner, {**self.body, 'claim_token': token}, ready=True)
        self.ledger.release('attempt01', 'worker', self.claim['token'], 'yielded')
        with self.assertRaises(OwnershipError):
            self.service.submit('worker', self.body, ready=True)

    def test_paths_revision_and_node_are_validated(self):
        for changes in ({'candidate': '/tmp/unregistered'}, {'run_directory': str(self.root)},
                        {'revision': 'HEAD'}, {'request_id': '../bad'}, {'node_id': '../root'}):
            with self.subTest(changes=changes), self.assertRaises(ValueError):
                self.service.submit('worker', {**self.body, **changes}, ready=False)

    def test_restart_retains_uncertain_identity_without_respawning(self):
        self.service.submit('worker', self.body, ready=False)
        with self.ledger._db() as db:
            db.execute("UPDATE verifications SET state='running',pid=123,start_ticks='456'")
        restarted = VerificationService(self.ledger, self.root / 'logs', self.program, sys.executable)
        self.addCleanup(restarted.pool.shutdown)
        result = restarted.submit('worker', self.body, ready=True)
        restarted.futures[self.body['request_id']].result(timeout=10)
        self.assertEqual(result['state'], 'uncertain')
        self.assertTrue(restarted.pending('attempt01'))
        self.assertFalse((self.root / 'logs' / ('b' * 32 + '.log')).exists())

    def additional_dispatcher(self, **kwargs):
        service = VerificationService(self.ledger, self.root / 'logs', self.program,
                                      sys.executable, recover_existing=False, max_workers=1, **kwargs)
        self.addCleanup(service.pool.shutdown)
        return service

    def test_additional_dispatcher_preserves_live_process_identity(self):
        self.service.submit('worker', self.body, ready=False)
        with self.ledger._db() as db:
            db.execute("UPDATE verifications SET state='running',pid=123,start_ticks='456'")
        extra = self.additional_dispatcher()
        self.assertEqual(extra.dispatch_queued(ready=True), [])
        with self.ledger._db() as db:
            row = db.execute('SELECT state,pid,start_ticks FROM verifications').fetchone()
        self.assertEqual(tuple(row), ('running', 123, '456'))

    def test_dispatch_respects_readiness_and_existing_request_identity(self):
        self.service.submit('worker', self.body, ready=False)
        extra = self.additional_dispatcher()
        self.assertEqual(extra.dispatch_queued(ready=False), [])
        ids = extra.dispatch_queued(ready=True)
        self.assertEqual(ids, [self.body['request_id']])
        extra.futures[ids[0]].result(timeout=10)
        result = self.service.result(ids[0], self.body['revision'])
        self.assertEqual(result['returncode'], 0)
        self.assertEqual(result['revision'], self.body['revision'])
        self.assertEqual(extra.dispatch_queued(ready=True), [])

    def test_two_controllers_racing_execute_spawn_only_once(self):
        self.service.submit('worker', self.body, ready=False)
        extra = self.additional_dispatcher()
        process = Mock(pid=os.getpid())
        process.wait.return_value = 0
        with patch('_recursive_lean.remote_verification.subprocess.Popen', return_value=process) as spawn:
            first = self.service.pool.submit(self.service.execute, self.body['request_id'])
            second = extra.pool.submit(extra.execute, self.body['request_id'])
            first.result(timeout=10)
            second.result(timeout=10)
            self.assertEqual(spawn.call_count, 1)
            self.assertEqual(spawn.call_args.kwargs['env']['FERMAT_VERIFICATION_REQUEST_ID'], self.body['request_id'])

    def test_released_claim_cannot_start_a_queued_verification(self):
        self.service.submit('worker', self.body, ready=False)
        # Simulate stale input after an operator reconciliation. Normal broker
        # release separately refuses any pending verification.
        self.ledger.release('attempt01', 'worker', self.claim['token'], 'yielded')
        extra = self.additional_dispatcher()
        self.assertEqual(extra.dispatch_queued(ready=True), [])
        with patch('_recursive_lean.remote_verification.subprocess.Popen') as spawn:
            extra.execute(self.body['request_id'])
            spawn.assert_not_called()

    def test_uncertain_remote_exit_keeps_claim_pending_without_retry(self):
        self.service.submit('worker', self.body, ready=False)
        extra = self.additional_dispatcher(uncertain_exit_codes=(75,))
        process = Mock(pid=os.getpid())
        process.wait.return_value = 75
        with patch('_recursive_lean.remote_verification.subprocess.Popen', return_value=process):
            extra.execute(self.body['request_id'])
        result = extra.result(self.body['request_id'], self.body['revision'])
        self.assertEqual(result['state'], 'uncertain')
        self.assertNotIn('returncode', result)
        self.assertTrue(extra.pending('attempt01'))
        self.assertEqual(extra.dispatch_queued(ready=True), [])

    def test_dispatch_capacity_does_not_enqueue_unbounded_work(self):
        extra = self.additional_dispatcher()
        extra.futures['occupied'] = Mock(done=lambda: False)
        self.service.submit('worker', self.body, ready=False)
        self.assertEqual(extra.dispatch_queued(ready=True), [])

    def test_missing_request_is_not_spawned(self):
        with patch('_recursive_lean.remote_verification.subprocess.Popen') as spawn:
            self.service.execute('f' * 32)
            spawn.assert_not_called()


if __name__ == '__main__':
    unittest.main()
