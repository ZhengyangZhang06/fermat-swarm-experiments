from concurrent.futures import ThreadPoolExecutor
import importlib.util
import sqlite3
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

    def test_128_independent_issues_in_one_project_can_run(self):
        def compete(i):
            return self.claim(issue=i + 1, owner=f'hoa{i}/task{i}/boot0',
                              attempt=f'attempt{i}', parallel=True)
        with ThreadPoolExecutor(max_workers=128) as pool:
            results = list(pool.map(compete, range(128)))
        self.assertEqual(sum(r is not None for r in results), 128)
        self.assertTrue(all(r['scope'] == 'issue' for r in results))
        self.assertEqual(len(self.ledger.active()), 128)

    def test_parallel_claims_still_exclude_duplicate_issue_and_owner(self):
        first = self.claim(parallel=True)
        self.assertIsNotNone(first)
        self.assertIsNone(self.claim(parallel=True, owner='other', attempt='duplicate'))
        self.assertIsNone(self.claim(parallel=True, issue=2, attempt='same-owner'))
        with self.assertRaises(OwnershipError):
            self.claim(parallel=False)

    def test_128_parallel_contenders_for_same_issue_have_one_owner(self):
        with ThreadPoolExecutor(max_workers=128) as pool:
            results = list(pool.map(lambda i: self.claim(parallel=True,
                owner=f'hoa{i}/task{i}/boot0', attempt=f'attempt{i}'), range(128)))
        self.assertEqual(sum(r is not None for r in results), 1)

    def test_legacy_claim_blocks_parallel_until_terminal_release(self):
        legacy = self.claim()
        self.assertIsNone(self.claim(parallel=True, issue=2, owner='other', attempt='second'))
        self.ledger.release(legacy['attempt'], legacy['owner'], legacy['token'], 'yielded')
        self.assertIsNotNone(self.claim(parallel=True, issue=2, owner='other', attempt='second'))
        self.assertIsNone(self.claim(issue=3, owner='legacy', attempt='third'))

    def test_old_ledger_initializer_and_insert_cannot_remove_barrier(self):
        self.claim(parallel=True)
        with sqlite3.connect(self.path) as db:
            # Literal old constructor/INSERT protocol: no knowledge of scope.
            db.execute("CREATE UNIQUE INDEX IF NOT EXISTS one_project ON claims(project) WHERE state='owned'")
            with self.assertRaises(sqlite3.IntegrityError):
                db.execute("INSERT INTO claims(attempt,project,repository,issue,owner,token,state,created,observed) "
                           "VALUES('old','fermat/p01','owner/repo',2,'old-worker','test','owned',0,0)")
        self.assertIsNotNone(self.claim(parallel=True, issue=2, owner='other', attempt='new'))

    def test_migration_preserves_original_live_legacy_row(self):
        legacy_path = self.path.parent / 'legacy.sqlite'
        with sqlite3.connect(legacy_path) as db:
            db.execute("CREATE TABLE claims (attempt TEXT PRIMARY KEY, project TEXT NOT NULL, "
                       "repository TEXT NOT NULL, issue INTEGER NOT NULL, owner TEXT NOT NULL, "
                       "token TEXT NOT NULL, state TEXT NOT NULL, created REAL NOT NULL, "
                       "observed REAL NOT NULL, receipt TEXT NOT NULL DEFAULT '{}', "
                       "job TEXT NOT NULL DEFAULT '{}', outcome TEXT NOT NULL DEFAULT '')")
            db.execute("CREATE UNIQUE INDEX one_project ON claims(project) WHERE state='owned'")
            db.execute("INSERT INTO claims(attempt,project,repository,issue,owner,token,state,created,observed) "
                       "VALUES('attempt0','fermat/p01','owner/repo',1,'hoa0/task0/boot0','retained','owned',1,2)")
        migrated = ClaimLedger(legacy_path)
        row = migrated.lookup('attempt0', 'hoa0/task0/boot0')
        self.assertEqual((row['token'], row['created'], row['observed'], row['scope']),
                         ('retained', 1, 2, 'project'))
        self.assertIsNone(migrated.claim(project='fermat/p01', repository='owner/repo', issue=2,
                                        owner='other', attempt='second', parallel=True))
        ClaimLedger(legacy_path)
        self.assertEqual(migrated.lookup('attempt0', 'hoa0/task0/boot0'), row)

    def test_old_insert_defaults_to_exclusive_in_empty_project(self):
        with sqlite3.connect(self.path) as db:
            db.execute("INSERT INTO claims(attempt,project,repository,issue,owner,token,state,created,observed) "
                       "VALUES('old','fermat/p01','owner/repo',2,'old-worker','test','owned',0,0)")
        self.assertEqual(self.ledger.lookup('old', 'old-worker')['scope'], 'project')
        self.assertIsNone(self.claim(parallel=True))

    def test_update_cannot_cross_scope_barrier(self):
        legacy = self.claim()
        self.ledger.release(legacy['attempt'], legacy['owner'], legacy['token'], 'yielded')
        self.claim(parallel=True, issue=2, owner='second', attempt='second')
        self.claim(parallel=True, issue=3, owner='third', attempt='third')
        self.claim(project='other', issue=4, owner='fourth', attempt='fourth')
        with sqlite3.connect(self.path) as db:
            for statement in (
                "UPDATE claims SET state='owned' WHERE attempt='attempt0'",
                "UPDATE claims SET scope='project' WHERE attempt='second'",
                "UPDATE claims SET project='fermat/p01' WHERE attempt='fourth'",
            ):
                with self.assertRaises(sqlite3.IntegrityError):
                    db.execute(statement)

    def test_observe_release_and_reopen_preserve_parallel_siblings(self):
        first = self.claim(parallel=True)
        second = self.claim(parallel=True, issue=2, owner='second', attempt='second')
        self.ledger.observe(first['attempt'], first['owner'], first['token'], {'pid': 123})
        self.ledger.release(first['attempt'], first['owner'], first['token'], 'yielded')
        ClaimLedger(self.path)
        self.assertEqual(self.ledger.active(), [second])

    def test_mixed_scope_contention_never_mixes_owned_scopes(self):
        with ThreadPoolExecutor(max_workers=128) as pool:
            results = list(pool.map(lambda i: self.claim(parallel=bool(i % 2), issue=i + 1,
                owner=f'hoa{i}/task{i}/boot0', attempt=f'attempt{i}'), range(128)))
        winners = [r for r in results if r]
        self.assertTrue(winners)
        if any(r['scope'] == 'project' for r in winners):
            self.assertEqual(len(winners), 1)
        else:
            self.assertTrue(all(r['scope'] == 'issue' for r in winners))

    def test_concurrent_old_and_new_openers_preserve_parallel_claims(self):
        first = self.claim(parallel=True)
        second = self.claim(parallel=True, issue=2, owner='second', attempt='second')
        def reopen(i):
            if i % 2:
                ClaimLedger(self.path)
            else:
                with sqlite3.connect(self.path, timeout=30) as db:
                    db.execute("CREATE UNIQUE INDEX IF NOT EXISTS one_project ON claims(project) WHERE state='owned'")
        with ThreadPoolExecutor(max_workers=32) as pool:
            list(pool.map(reopen, range(64)))
        self.assertEqual({r['attempt'] for r in self.ledger.active()}, {first['attempt'], second['attempt']})
        self.assertIsNotNone(self.claim(parallel=True, issue=3, owner='third', attempt='third'))

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
                          {'owner': ''}, {'attempt': 'bad\nidentity'}, {'parallel': 'true'}, {'parallel': 1}):
            with self.assertRaises(ValueError):
                self.claim(**overrides)


if __name__ == '__main__':
    unittest.main()
