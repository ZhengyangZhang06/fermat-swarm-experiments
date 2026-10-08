import hashlib
import json
from pathlib import Path
import sqlite3
import subprocess
import tempfile
import unittest
from unittest.mock import patch

from _recursive_lean.distributed_claims import ClaimLedger
from _recursive_lean.remote_dispatch_slot import RemoteDispatchSlot
from _recursive_lean.swarm_verification import digest


class RemoteSlotTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.packets = self.root / 'packets'
        self.packets.mkdir(mode=0o700)
        self.ledger = ClaimLedger(self.root / 'claims.sqlite')
        with self.ledger._db() as db:
            db.execute('CREATE TABLE verifications (id TEXT PRIMARY KEY, attempt TEXT, request TEXT, state TEXT, returncode INTEGER)')
            # The slot only reads claim state; construct a genuine ledger row.
            db.execute("INSERT INTO claims(attempt,project,repository,issue,owner,token,state,created,observed,job) "
                       "VALUES('attempt','project','repo',1,'owner','token','owned',0,0,'{}')")
        self.request_id = 'a' * 32
        self.node_id, self.service_id, self.task_id = 'n' * 25, 's' * 25, 't' * 25
        self.request = json.dumps(dict(project=str(self.root / 'workers/project'), revision='b' * 40))
        self.enqueue(self.request_id)
        self.node = dict(ID=self.node_id, Description=dict(Hostname='hoa127'),
                         Status=dict(State='ready'), Spec=dict(Availability='active',
                         Labels={'fermat-swarm-20261007': 'true'}))
        self.service = dict(ID=self.service_id, Spec=dict(Labels={
            'fermat.request': self.request_id, 'fermat.packet': 'c' * 64}))
        self.task = dict(ID=self.task_id, ServiceID=self.service_id, NodeID=self.node_id,
                         Status=dict(State='complete', ContainerStatus=dict(ExitCode=0, PID=0)))
        self.inspect = patch('_recursive_lean.remote_dispatch_slot.inspect', side_effect=self.inspect_record).start()
        self.docker = patch('_recursive_lean.remote_dispatch_slot.docker', return_value=self.task_id + '\n').start()
        self.addCleanup(patch.stopall)

    def inspect_record(self, kind, identity):
        return {'node': self.node, 'service': self.service, 'task': self.task}[kind]

    def enqueue(self, request_id):
        with self.ledger._db() as db:
            db.execute('INSERT INTO verifications VALUES(?,?,?,?,NULL)',
                       (request_id, 'attempt', self.request, 'queued'))

    def finish(self, state='finished', code=0):
        with self.ledger._db() as db:
            db.execute('UPDATE verifications SET state=?,returncode=? WHERE id=?', (state, code, self.request_id))

    def receipt(self, **updates):
        root = self.packets / self.request_id
        root.mkdir(mode=0o700, exist_ok=True)
        value = dict(request_id=self.request_id, node='hoa127', node_id=self.node_id,
                     state='verified', candidate_commit='b' * 40, service_id=self.service_id,
                     task_id=self.task_id, packet_digest='c' * 64,
                     service_spec_sha256=digest(self.service['Spec']), returncode=0)
        value.update(updates)
        path = root / 'operation.json'
        path.write_text(json.dumps(value))
        path.chmod(0o600)
        return path

    def reserve(self, slot):
        slot._write(dict(state='reserved', node='hoa127', node_id=self.node_id,
                         directory=str(self.packets), request_id=self.request_id,
                         request_sha256=hashlib.sha256(self.request.encode()).hexdigest()))

    def slot(self):
        return RemoteDispatchSlot(self.ledger, 'hoa127', self.packets)

    def test_exclusive_same_physical_node_even_different_packet_directory(self):
        other = self.root / 'other'
        other.mkdir(mode=0o700)
        with self.slot():
            with self.assertRaises(BlockingIOError):
                with RemoteDispatchSlot(self.ledger, 'hoa127', other):
                    self.fail('duplicate controller acquired slot')

    def test_intent_persisted_before_execute(self):
        parent = self
        class Service:
            def execute(self, identity, *, before_spawn):
                before_spawn(dict(id=identity, request=parent.request))
                saved = json.loads((parent.root / 'remote-verifier-slots/hoa127.json').read_text())
                parent.assertEqual(saved['request_id'], identity)
                raise RuntimeError('simulated controller failure')
        with self.slot() as slot:
            with self.assertRaisesRegex(RuntimeError, 'controller failure'):
                slot.execute_next(Service(), ready=True)
        with self.slot() as resumed:
            self.assertFalse(resumed.reconcile())

    def test_exit75_retains_slot_across_restart(self):
        with self.slot() as slot:
            self.reserve(slot)
            self.finish('uncertain', 75)
        with self.slot() as resumed:
            self.assertFalse(resumed.reconcile())
            with self.assertRaisesRegex(RuntimeError, 'retained'):
                resumed.execute_next(None, ready=True)

    def test_finished75_never_frees_slot(self):
        with self.slot() as slot:
            self.reserve(slot)
            self.finish(code=75)
            self.receipt()
            self.assertFalse(slot.reconcile())

    def test_verified_terminal_advances_and_retains_history(self):
        with self.slot() as slot:
            self.reserve(slot)
            self.finish()
            self.receipt()
            self.assertTrue(slot.reconcile())
            self.assertEqual(json.loads(slot.path.read_text())['completed_request'], self.request_id)
        with self.slot() as resumed:
            self.assertTrue(resumed.reconcile())

    def test_terminal_failed_proof_frees_slot(self):
        with self.slot() as slot:
            self.reserve(slot)
            self.finish(code=1)
            self.task['Status'] = dict(State='failed', ContainerStatus=dict(ExitCode=2, PID=0))
            self.receipt(state='terminal', returncode=2)
            self.assertTrue(slot.reconcile())

    def test_explicit_presubmit_failure_frees_slot(self):
        with self.slot() as slot:
            self.reserve(slot)
            self.finish(code=1)
            path = self.receipt()
            path.write_text(json.dumps(dict(request_id=self.request_id, node='hoa127', node_id=self.node_id,
                                            state='preparation-failed')))
            self.assertTrue(slot.reconcile())
            self.docker.assert_not_called()

    def test_presubmit_failure_with_submit_evidence_blocks(self):
        with self.slot() as slot:
            self.reserve(slot)
            self.finish(code=1)
            self.receipt(state='preparation-failed')
            with self.assertRaisesRegex(RuntimeError, 'submit evidence'):
                slot.reconcile()

    def test_missing_evidence_never_frees_slot(self):
        with self.slot() as slot:
            self.reserve(slot)
            self.finish()
            with self.assertRaises(FileNotFoundError):
                slot.reconcile()
            self.assertEqual(json.loads(slot.path.read_text())['state'], 'reserved')

    def test_mismatched_operation_identity_blocks(self):
        for field, bad in (('request_id', 'd' * 32), ('node_id', 'x' * 25),
                           ('candidate_commit', 'e' * 40), ('node', 'hoa126')):
            with self.subTest(field=field), self.slot() as slot:
                self.reserve(slot)
                self.finish()
                self.receipt(**{field: bad})
                with self.assertRaises(RuntimeError):
                    slot.reconcile()

    def test_node_replacement_blocks_restart(self):
        with self.slot() as slot:
            self.reserve(slot)
        self.node['ID'] = 'x' * 25
        with self.slot() as resumed:
            with self.assertRaisesRegex(RuntimeError, 'node identity'):
                resumed.reconcile()

    def test_packet_directory_change_blocks_restart(self):
        with self.slot() as slot:
            self.reserve(slot)
        other = self.root / 'other'
        other.mkdir(mode=0o700)
        with RemoteDispatchSlot(self.ledger, 'hoa127', other) as resumed:
            with self.assertRaisesRegex(RuntimeError, 'directory changed'):
                resumed.reconcile()

    def test_live_task_and_uncertain_operation_do_not_free_slot(self):
        with self.slot() as slot:
            self.reserve(slot)
            self.finish()
            self.receipt(state='uncertain')
            self.assertFalse(slot.reconcile())
            self.receipt()
            self.task['Status'] = dict(State='running')
            self.assertFalse(slot.reconcile())

    def test_replaced_task_or_service_or_wrong_node_blocks(self):
        for change in ('task_list', 'service', 'node'):
            with self.subTest(change=change), self.slot() as slot:
                self.reserve(slot)
                self.finish()
                self.receipt()
                if change == 'task_list':
                    self.docker.return_value = self.task_id + '\n' + 'u' * 25 + '\n'
                elif change == 'service':
                    self.service['Spec']['Changed'] = True
                else:
                    self.task['NodeID'] = 'x' * 25
                with self.assertRaises(RuntimeError):
                    slot.reconcile()
                self.docker.return_value = self.task_id + '\n'
                self.service['Spec'].pop('Changed', None)
                self.task['NodeID'] = self.node_id

    def test_no_dispatch_without_ready_or_lock(self):
        with self.slot() as slot:
            self.assertIsNone(slot.execute_next(None, ready=False))
            self.assertFalse(slot.path.exists())
        with self.assertRaisesRegex(RuntimeError, 'exclusive node lock'):
            slot.execute_next(None, ready=True)

    def test_proof_owned_node_never_starts_verifier(self):
        with self.ledger._db() as db:
            db.execute("UPDATE claims SET owner='hoa127/proof-task'")
        with self.slot() as slot:
            self.assertIsNone(slot.execute_next(None, ready=True))
            self.assertEqual(self.ledger.active_node_reservations(), [])
            self.assertEqual(json.loads(slot.path.read_text())['state'], 'idle')

    def test_atomic_role_retained_after_controller_loss(self):
        parent = self
        class Service:
            def execute(self, request_id, *, before_spawn):
                before_spawn(dict(id=request_id, request=parent.request))
                raise RuntimeError('lost controller')
        with self.slot() as slot:
            with self.assertRaisesRegex(RuntimeError, 'lost controller'):
                slot.execute_next(Service(), ready=True)
        reserved = self.ledger.active_node_reservations()
        self.assertEqual(len(reserved), 1)
        with self.slot() as resumed:
            with self.assertRaisesRegex(RuntimeError, 'retained'):
                resumed.execute_next(None, ready=True)
        self.assertEqual(self.ledger.active_node_reservations(), reserved)

    def test_terminal_execution_releases_role_only_on_empty_queue(self):
        parent = self
        class Service:
            def execute(self, request_id, *, before_spawn):
                before_spawn(dict(id=request_id, request=parent.request))
                parent.assertEqual(len(parent.ledger.active_node_reservations()), 1)
                parent.finish()
                parent.receipt()
        with self.slot() as slot:
            self.assertEqual(slot.execute_next(Service(), ready=True), self.request_id)
            first = self.ledger.active_node_reservations()[0]
            self.assertEqual(json.loads(slot.path.read_text())['state'], 'idle')
            self.assertIsNone(slot.execute_next(None, ready=True))
            self.assertEqual(self.ledger.active_node_reservations(), [])
            # A fresh request cycle gets a new reservation, keeping the owner.
            with self.ledger._db() as db:
                db.execute("UPDATE verifications SET state='queued',returncode=NULL")
            self.assertEqual(slot.execute_next(Service(), ready=True), self.request_id)
            second = self.ledger.active_node_reservations()[0]
            self.assertNotEqual(first['reservation_id'], second['reservation_id'])
            self.assertEqual(first['owner'], second['owner'])

    def test_other_node_wins_request_without_retaining_false_intent(self):
        class Service:
            def execute(self, request_id, *, before_spawn):
                return  # Lost atomic ledger claim; callback was never called.
        with self.slot() as slot:
            self.assertIsNone(slot.execute_next(Service(), ready=True))
            self.assertEqual(json.loads(slot.path.read_text())['state'], 'idle')
            self.assertTrue(slot.reconcile())

    def test_restart_after_role_release_before_slot_clear_rotates_exact_history(self):
        class Service:
            def execute(self, request_id, *, before_spawn):
                return  # Keep known-idle slot, simulating another claim winner.
        with self.slot() as slot:
            slot.execute_next(Service(), ready=True)
            old = json.loads(slot.path.read_text())
            self.ledger.release_node(node='hoa127', reservation_id=old['reservation_id'], owner=old['owner'])
            # Simulate process loss before slot JSON clears the released ID.
        with self.slot() as resumed:
            resumed.execute_next(Service(), ready=True)
            current = json.loads(resumed.path.read_text())
            self.assertNotEqual(current['reservation_id'], old['reservation_id'])
            self.assertEqual(current['owner'], old['owner'])
            self.assertEqual(self.ledger.active_node_reservations()[0]['reservation_id'], current['reservation_id'])

    def bound_gate(self, **changes):
        checker = self.root / 'checker.py'
        checker.write_text('trusted checker')
        gate = dict(verifier_ready=True, node='hoa127', node_id=self.node_id,
                    reference_digest='d' * 64, reference_volume='trusted-cache',
                    verifier_sha256=hashlib.sha256(checker.read_bytes()).hexdigest(),
                    config_sha256='e' * 64, diagnostic_spec_sha256=digest(self.service['Spec']),
                    diagnostic_service_id=self.service_id, diagnostic_task_id=self.task_id)
        gate.update(changes)
        path = self.root / 'readiness.json'
        path.write_text(json.dumps(gate))
        path.chmod(0o600)
        return dict(catalog=path, checker=checker, environment={
            'FERMAT_VERIFIER_REFERENCE_DIGEST': 'd' * 64,
            'FERMAT_SWARM_VERIFIER_REFERENCE_VOLUME': 'trusted-cache'})

    def test_bound_readiness_requires_exact_terminal_diagnostic(self):
        with self.slot() as slot:
            self.assertTrue(slot.readiness(**self.bound_gate()))
            self.task['Status'] = dict(State='running')
            with self.assertRaisesRegex(RuntimeError, 'terminal successful'):
                slot.readiness(**self.bound_gate())

    def test_bound_readiness_false_gate_needs_no_diagnostic(self):
        with self.slot() as slot:
            args = self.bound_gate(verifier_ready=False)
            self.inspect.reset_mock()
            self.assertFalse(slot.readiness(**args))
            self.inspect.assert_not_called()

    def test_bound_readiness_rejects_wrong_identity_or_missing_receipts(self):
        for key, wrong in (('node', 'hoa126'), ('node_id', 'x' * 25),
                           ('reference_digest', 'f' * 64), ('reference_volume', 'different-cache'),
                           ('verifier_sha256', 'f' * 64), ('config_sha256', ''),
                           ('diagnostic_spec_sha256', 'f' * 64), ('diagnostic_task_id', None)):
            with self.subTest(key=key), self.slot() as slot:
                with self.assertRaises(RuntimeError):
                    slot.readiness(**self.bound_gate(**{key: wrong}))

    def test_bound_readiness_rechecks_current_physical_node(self):
        with self.slot() as slot:
            args = self.bound_gate()
            self.node['ID'] = 'x' * 25
            with self.assertRaisesRegex(RuntimeError, 'physical node identity'):
                slot.readiness(**args)

    def test_readiness_observation_failure_waits_without_starting_or_releasing(self):
        with self.slot() as slot:
            args = self.bound_gate()
            for failure in (subprocess.TimeoutExpired('docker', 30),
                            subprocess.CalledProcessError(1, 'docker')):
                with self.subTest(failure=failure), patch(
                        '_recursive_lean.remote_dispatch_slot.inspect', side_effect=failure):
                    self.assertFalse(slot.readiness(**args))
                    self.assertFalse(slot.path.exists())
                    self.assertEqual(self.ledger.active_node_reservations(), [])
            self.assertTrue(slot.readiness(**args))

    def test_terminal_observation_retry_preserves_slot_without_rerunning_adapter(self):
        with self.slot() as slot:
            self.reserve(slot)
            self.finish()
            self.receipt()
            with patch('_recursive_lean.remote_dispatch_slot.inspect',
                       side_effect=subprocess.TimeoutExpired('docker', 30)):
                with self.assertRaises(subprocess.TimeoutExpired):
                    slot.execute_next(None, ready=True)
            self.assertEqual(json.loads(slot.path.read_text())['state'], 'reserved')
            # No queued row remains. Retry observes the retained terminal job,
            # clears its slot and never invokes any adapter execution.
            self.assertIsNone(slot.execute_next(None, ready=True))
            self.assertEqual(json.loads(slot.path.read_text())['state'], 'idle')


if __name__ == '__main__':
    unittest.main()
