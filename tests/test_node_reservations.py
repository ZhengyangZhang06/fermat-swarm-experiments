from concurrent.futures import ThreadPoolExecutor
import importlib.util
from pathlib import Path
import sqlite3
import tempfile
import threading
import unittest


SPEC = importlib.util.spec_from_file_location(
    'node_reservation_ledger', Path(__file__).resolve().parents[1] / '_recursive_lean/distributed_claims.py')
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)
ClaimLedger, OwnershipError = MODULE.ClaimLedger, MODULE.OwnershipError


class NodeReservationsTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.path = Path(temporary.name) / 'ledger.sqlite'
        self.ledger = ClaimLedger(self.path)

    def reserve(self, **changes):
        return self.ledger.reserve_node(**dict(
            dict(node='hoa0', reservation_id='verify-0', owner='controller-0', purpose='verification'),
            **changes))

    def claim(self, **changes):
        return self.ledger.claim(**dict(dict(project='p01', repository='owner/repo', issue=1,
            owner='hoa0/task/boot', attempt='proof-0', parallel=True), **changes))

    def release(self, **changes):
        return self.ledger.release_node(**dict(
            dict(node='hoa0', reservation_id='verify-0', owner='controller-0'), **changes))

    def test_reserved_node_blocks_fresh_claim_not_other_nodes(self):
        self.reserve()
        self.assertIsNone(self.claim())
        self.assertIsNone(self.claim(owner='hoa0'))
        self.assertIsNotNone(self.claim(owner='hoa1/task/boot'))
        self.assertIsNotNone(self.claim(owner='other-local-worker', issue=2, attempt='proof-1'))

    def test_owned_node_cannot_be_reserved_and_held_job_is_unchanged(self):
        held = self.claim(job={'immutable': 'job'})
        self.assertIsNone(self.reserve())
        self.assertEqual(self.claim(job={'changed': 'ignored'}), held)
        self.assertEqual(self.ledger.lookup(held['attempt'], held['owner']), held)
        self.assertEqual(self.ledger.active_node_reservations(), [])
        self.ledger.observe(held['attempt'], held['owner'], held['token'], {'pid': 1})
        self.ledger.release(held['attempt'], held['owner'], held['token'], 'yielded')
        self.assertIsNotNone(self.reserve())

    def test_bare_node_owner_also_excludes_reservation(self):
        self.claim(owner='hoa0')
        self.assertIsNone(self.reserve())

    def test_reservation_is_durable_idempotent_and_cannot_change_identity(self):
        original = self.reserve()
        self.ledger = ClaimLedger(self.path)
        self.assertEqual(self.reserve(), original)
        self.assertEqual(self.ledger.active_node_reservations(), [original])
        for change in ({'owner': 'controller-1'}, {'purpose': 'other'}, {'node': 'hoa1'}):
            with self.subTest(change=change), self.assertRaises(OwnershipError):
                self.reserve(**change)
        self.assertIsNone(self.reserve(reservation_id='verify-1', owner='controller-1'))

    def test_wrong_release_cannot_free_node(self):
        original = self.reserve()
        for change in ({'owner': 'controller-1'}, {'reservation_id': 'wrong'}, {'node': 'hoa1'}):
            with self.subTest(change=change), self.assertRaises(OwnershipError):
                self.release(**change)
        self.assertEqual(self.ledger.active_node_reservations(), [original])
        self.assertIsNone(self.claim())

    def test_valid_release_allows_proof_and_retains_history(self):
        original = self.reserve()
        released = self.release()
        self.assertEqual(released['state'], 'released')
        self.assertEqual(released['created'], original['created'])
        self.assertGreaterEqual(released['released'], original['created'])
        self.assertEqual(self.release(), released)
        self.assertIsNone(self.reserve())  # An old identity is not a new grant.
        self.assertEqual(self.ledger.active_node_reservations(), [])
        self.assertIsNotNone(self.claim())

    def test_stale_idempotent_release_cannot_release_new_reservation(self):
        self.reserve()
        old = self.release()
        current = self.reserve(reservation_id='verify-1')
        self.assertEqual(self.release(), old)
        self.assertEqual(self.ledger.active_node_reservations(), [current])
        self.assertIsNone(self.claim())

    def test_proof_and_reservation_race_exactly_one_wins(self):
        # Distinct physical nodes cover repeated races without releasing owners.
        for index in range(32):
            barrier = threading.Barrier(2)
            def proof():
                barrier.wait()
                return self.claim(owner=f'hoa{index}/task/boot', issue=index + 1,
                                  attempt=f'proof-{index}')
            def verifier():
                barrier.wait()
                return self.reserve(node=f'hoa{index}', reservation_id=f'verify-{index}')
            with ThreadPoolExecutor(max_workers=2) as pool:
                futures = [pool.submit(proof), pool.submit(verifier)]
                outcomes = [future.result() for future in futures]
            self.assertEqual(sum(row is not None for row in outcomes), 1)

    def test_two_controllers_cannot_reserve_same_node(self):
        barrier = threading.Barrier(2)
        def compete(index):
            barrier.wait()
            return self.reserve(owner=f'controller-{index}', reservation_id=f'verify-{index}')
        with ThreadPoolExecutor(max_workers=2) as pool:
            results = list(pool.map(compete, range(2)))
        self.assertEqual(sum(row is not None for row in results), 1)
        self.assertEqual(len(self.ledger.active_node_reservations()), 1)

    def test_old_sql_claim_writer_cannot_bypass_reservation(self):
        self.reserve()
        with sqlite3.connect(self.path) as db:
            with self.assertRaises(sqlite3.IntegrityError):
                db.execute("INSERT INTO claims(attempt,project,repository,issue,owner,token,state,created,observed) "
                           "VALUES('old','p01','owner/repo',1,'hoa0/old/boot','secret','owned',0,0)")
        held = self.claim(owner='hoa1/task/boot')
        with sqlite3.connect(self.path) as db:
            with self.assertRaises(sqlite3.IntegrityError):
                db.execute('UPDATE claims SET owner=? WHERE attempt=?', ('hoa0/task/boot', held['attempt']))

    def test_invalid_node_and_identity_values(self):
        for node in ('hoa128', 'hoa-1', 'hoa00', 'hoa01', 'hoa999', 'hoa0/task', '', None, 0, 'HOA0'):
            with self.subTest(node=node), self.assertRaises(ValueError):
                self.reserve(node=node)
            with self.subTest(release_node=node), self.assertRaises(ValueError):
                self.release(node=node)
        for change in ({'owner': ''}, {'reservation_id': None}, {'purpose': ''},
                       {'purpose': None}, {'owner': 'newline\n'}, {'purpose': 'x' * 241}):
            with self.subTest(change=change), self.assertRaises(ValueError):
                self.reserve(**change)
        self.assertIsNotNone(self.reserve(node='hoa127'))


if __name__ == '__main__':
    unittest.main()
