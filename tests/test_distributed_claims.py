from concurrent.futures import ThreadPoolExecutor
import importlib.util
from pathlib import Path
import tempfile
import unittest

spec = importlib.util.spec_from_file_location(
    'distributed_claims', Path(__file__).resolve().parents[1] / '_recursive_lean/distributed_claims.py'
)
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)
ClaimLedger, OwnershipError = module.ClaimLedger, module.OwnershipError


class DistributedClaimsTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.path = Path(self.tmp.name) / 'claims.sqlite'
        self.ledger = ClaimLedger(self.path)

    def claim(self, **overrides):
        args = dict(project='fermat/p01', repository='Owner/Repo', issue=1,
                    owner='hoa0/task0/boot0', attempt='attempt0')
        args.update(overrides)
        return self.ledger.claim(**args)

    def test_128_connections_have_one_owner(self):
        def compete(i):
            return self.claim(owner=f'hoa{i}/task{i}/boot0', attempt=f'attempt{i}')
        with ThreadPoolExecutor(max_workers=128) as pool:
            results = list(pool.map(compete, range(128)))
        self.assertEqual(sum(r is not None for r in results), 1)
        self.assertEqual(len(self.ledger.active()), 1)

    def test_lost_response_and_restart_preserve_ownership(self):
        first = self.claim()
        self.ledger = ClaimLedger(self.path)
        self.assertEqual(self.claim(), first)
        self.assertIsNone(self.claim(owner='hoa1/task1/boot0', attempt='second'))

    def test_same_attempt_cannot_change_identity(self):
        self.claim()
        with self.assertRaises(OwnershipError):
            self.claim(issue=2)

    def test_project_issue_and_owner_all_exclusive(self):
        self.claim()
        self.assertIsNone(self.claim(issue=2, owner='other', attempt='second'))
        self.assertIsNone(self.claim(project='p02', owner='other', attempt='third'))
        self.assertIsNone(self.claim(project='p02', issue=2, attempt='fourth'))
        self.assertIsNotNone(self.claim(project='p02', issue=2, owner='other', attempt='fifth'))

    def test_stale_token_cannot_release_or_overwrite(self):
        first = self.claim()
        for token in ('wrong', ''):
            with self.assertRaises(OwnershipError):
                self.ledger.release(first['attempt'], first['owner'], token, 'yielded')
            with self.assertRaises(OwnershipError):
                self.ledger.observe(first['attempt'], first['owner'], token, {})

    def test_release_is_idempotent_and_old_attempt_cannot_restart(self):
        first = self.claim()
        args = (first['attempt'], first['owner'], first['token'], 'yielded')
        self.ledger.release(*args)
        self.ledger.release(*args)
        self.assertIsNone(self.claim())
        second = self.claim(attempt='second')
        self.assertIsNotNone(second)
        self.assertNotEqual(first['token'], second['token'])
        with self.assertRaises(OwnershipError):
            self.ledger.observe(first['attempt'], first['owner'], first['token'], {})

    def test_observation_records_identity_not_timeout_takeover(self):
        first = self.claim()
        self.ledger.observe(first['attempt'], first['owner'], first['token'],
                            {'node': 'hoa0', 'swarm_task': 'abc', 'pid': 42, 'start_ticks': '123'})
        self.assertIsNone(self.claim(owner='hoa1/task1/boot0', attempt='second'))
        self.assertIn('swarm_task', self.ledger.active()[0]['receipt'])

    def test_bad_inputs_fail_closed(self):
        for overrides in ({'issue': 0}, {'issue': True}, {'repository': 'not-a-repository'},
                          {'owner': ''}, {'attempt': 'bad\nidentity'}):
            with self.assertRaises(ValueError):
                self.claim(**overrides)


if __name__ == '__main__':
    unittest.main()
