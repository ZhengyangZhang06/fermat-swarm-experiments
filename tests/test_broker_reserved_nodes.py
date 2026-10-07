import contextlib
import io
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import Mock, patch

from _recursive_lean.distributed_claims import ClaimLedger, OwnershipError
from _recursive_lean.parallel import PROTOCOL
from _recursive_lean.swarm_broker import Broker, authorized_node_name, main


class ReservedNodeTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.catalog = self.root / 'catalog.json'
        self.config = {'repository': 'owner/repo', 'broker_protocol': PROTOCOL,
                       'projects': [{'id': 'p01', 'root_issue': 1, 'issue_numbers': [1, 2],
                           'issue_runtime_protocol': PROTOCOL, 'enabled': True,
                           'command': ['/trusted/runner'], 'cwd': '/registered/project',
                           'environment': {}, 'log_directory': '/private/logs'}]}
        self.catalog.write_text(json.dumps(self.config))
        self.ledger = ClaimLedger(self.root / 'claims.sqlite')
        self.body = {'node': 'hoa127', 'task': 'task000000', 'boot': 'boot000000',
                     'project': 'p01', 'issue': 1, 'attempt': 'attempt0000'}

    def broker(self, **kwargs):
        broker = Broker(self.catalog, self.ledger, 'fixture-token-' * 4,
                        self.root / 'snapshot.json', 'gh', **kwargs)
        broker.github = Mock(return_value={'state': 'open'})
        return broker

    def test_default_empty_preserves_new_grants(self):
        broker = self.broker()
        self.assertEqual(broker.reserved_nodes, frozenset())
        self.assertIsNotNone(broker.claim(self.body)['claim'])

    def test_invalid_reserved_node_names_rejected(self):
        for node in ('', 'hoa128', 'hoa-1', 'hoa00', 'hoa01', 'manager',
                     'hoa127\n', 'hoa1/other', 'hoa1,hoa2', None, 1):
            with self.subTest(node=node), self.assertRaises(ValueError):
                self.broker(reserved_nodes=[node])
        for node in ('hoa0', 'hoa9', 'hoa10', 'hoa99', 'hoa100', 'hoa127'):
            self.assertEqual(authorized_node_name(node), node)

    def test_reserved_physical_node_gets_no_fresh_grant_or_ledger_record(self):
        before = self.catalog.read_bytes()
        broker = self.broker(reserved_nodes=['hoa127'])
        for task, boot, attempt in [('task000000', 'boot000000', 'attempt0000'),
                                    ('task111111', 'boot111111', 'attempt1111')]:
            body = {**self.body, 'task': task, 'boot': boot, 'attempt': attempt,
                    'reserved_nodes': [], 'reserve_node': 'hoa0'}
            self.assertIsNone(broker.claim(body)['claim'])
            self.assertIsNone(self.ledger.lookup(attempt, broker.identity(body)))
        self.assertEqual(self.ledger.active(), [])
        broker.github.assert_not_called()
        self.assertEqual(self.catalog.read_bytes(), before)

    def test_other_nodes_still_get_independent_sibling_grants(self):
        before = self.catalog.read_bytes()
        broker = self.broker(reserved_nodes=['hoa127'])
        for node, issue in [('hoa0', 1), ('hoa1', 2)]:
            claim = broker.claim({**self.body, 'node': node, 'issue': issue, 'attempt': node})['claim']
            self.assertIsNotNone(claim)
            self.assertEqual(claim['scope'], 'issue')
        self.assertEqual(len(self.ledger.active()), 2)
        self.assertEqual(self.catalog.read_bytes(), before)

    def test_reservation_is_frozen_at_startup_not_mutable_catalog_or_caller_input(self):
        supplied = ['hoa127', 'hoa127']
        broker = self.broker(reserved_nodes=supplied)
        supplied.clear()
        self.config['reserved_nodes'] = ['hoa0']
        self.catalog.write_text(json.dumps(self.config))
        before = self.catalog.read_bytes()
        self.assertEqual(broker.reserved_nodes, frozenset({'hoa127'}))
        with self.assertRaises(AttributeError):
            broker.reserved_nodes = frozenset()
        self.assertIsNone(broker.claim(self.body)['claim'])
        self.assertIsNotNone(broker.claim({**self.body, 'node': 'hoa0'})['claim'])
        self.assertEqual(self.catalog.read_bytes(), before)

    def test_held_reserved_node_grant_recovers_unchanged_and_can_observe_release(self):
        original = self.broker().claim(self.body)
        before = self.catalog.read_bytes()
        broker = self.broker(reserved_nodes=['hoa127'], runner_runtime='/runtime/flows/new')
        self.assertEqual(broker.claim(self.body), original)
        broker.github.assert_not_called()
        auth = {**self.body, 'claim_token': original['claim']['token']}
        receipt = {'node': 'hoa127', 'task': self.body['task'], 'state': 'running', 'pid': 15}
        self.assertEqual(broker.observe({**auth, 'receipt': receipt}), {'ok': True})
        held = self.ledger.lookup(self.body['attempt'], broker.identity(self.body))
        self.assertEqual(held['job'], original['claim']['job'])
        self.assertEqual(json.loads(held['receipt']), receipt)
        terminal = {**auth, 'outcome': 'completed', 'processes_remaining': 0, 'returncode': 0}
        broker.release(terminal)
        broker.release(terminal)
        self.assertEqual(self.ledger.active(), [])
        self.assertIsNone(broker.claim(self.body)['claim'])
        self.assertIsNone(broker.claim({**self.body, 'attempt': 'fresh-after-release'})['claim'])
        self.assertEqual(self.catalog.read_bytes(), before)

    def test_reservation_does_not_bypass_held_identity_or_terminal_checks(self):
        original = self.broker().claim(self.body)
        broker = self.broker(reserved_nodes=['hoa127'])
        with self.assertRaises(OwnershipError):
            broker.claim({**self.body, 'issue': 2})
        with self.assertRaises(OwnershipError):
            broker.claim({**self.body, 'boot': 'differentboot'})
        with self.assertRaises(OwnershipError):
            broker.release({**self.body, 'claim_token': original['claim']['token'],
                            'outcome': 'completed', 'processes_remaining': 1, 'returncode': 0})
        self.assertEqual(len(self.ledger.active()), 1)

    def cli_arguments(self):
        token = self.root / 'token'
        token.write_text('fixture-token-' * 4)
        args = ['swarm-broker', '--bind', '127.0.0.1']
        for name in ('catalog', 'database', 'token-file', 'snapshot', 'certificate', 'key'):
            value = token if name == 'token-file' else self.root / name
            args.extend(['--' + name, str(value)])
        return args

    def test_cli_repeatable_reservation_wires_into_broker_constructor(self):
        args = self.cli_arguments() + ['--reserve-node', 'hoa126', '--reserve-node', 'hoa127']
        with patch('sys.argv', args), patch('_recursive_lean.swarm_broker.Broker') as constructor, \
                patch('_recursive_lean.swarm_broker.ThreadingHTTPServer.__init__', return_value=None), \
                patch('_recursive_lean.swarm_broker.ThreadingHTTPServer.serve_forever'), \
                patch('_recursive_lean.swarm_broker.ThreadingHTTPServer.socket', new=Mock(), create=True), \
                patch('_recursive_lean.swarm_broker.ssl.SSLContext'), \
                patch('_recursive_lean.swarm_broker.os.umask'), contextlib.redirect_stdout(io.StringIO()):
            main()
        self.assertEqual(constructor.call_args.kwargs['reserved_nodes'], ['hoa126', 'hoa127'])

    def test_cli_rejects_invalid_node_before_ledger_or_server_creation(self):
        with patch('sys.argv', self.cli_arguments() + ['--reserve-node', 'hoa128']), \
                patch('_recursive_lean.swarm_broker.ClaimLedger') as ledger, \
                patch('_recursive_lean.swarm_broker.Broker') as constructor, \
                contextlib.redirect_stderr(io.StringIO()), self.assertRaises(SystemExit) as raised:
            main()
        self.assertEqual(raised.exception.code, 2)
        ledger.assert_not_called()
        constructor.assert_not_called()


if __name__ == '__main__':
    unittest.main()
