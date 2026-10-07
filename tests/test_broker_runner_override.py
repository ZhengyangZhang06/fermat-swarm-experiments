import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import Mock

from _recursive_lean.distributed_claims import ClaimLedger
from _recursive_lean.parallel import PROTOCOL
from _recursive_lean.swarm_broker import Broker, runner_runtime_path


class RunnerOverrideTests(unittest.TestCase):
    runtime = '/runtime/flows/math-lean-flow-policy-v4'

    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.catalog = self.root / 'catalog.json'
        self.config = {'repository': 'owner/repo', 'broker_protocol': PROTOCOL,
                       'verifier_ready': False, 'projects': [{
                           'id': 'p01', 'root_issue': 1, 'issue_numbers': [1, 2, 3],
                           'issue_runtime_protocol': PROTOCOL, 'enabled': True,
                           'quarantined_issues': [3],
                           'command': ['python3', '/runtime/flows/old/scripts/swarm-run-issue.py'],
                           'cwd': '/registered/project', 'environment': {'EXAMPLE': 'preserved'},
                           'verification': None, 'log_directory': '/private/logs',
                       }]}
        self.save()
        self.ledger = ClaimLedger(self.root / 'claims.sqlite')
        self.body = {'node': 'hoa0', 'task': 'task000000', 'boot': 'boot000000',
                     'project': 'p01', 'issue': 1, 'attempt': 'attempt0000'}

    def save(self):
        self.catalog.write_text(json.dumps(self.config))

    def broker(self, **kwargs):
        broker = Broker(self.catalog, self.ledger, 'fixture-token-' * 4,
                        self.root / 'snapshot.json', 'gh', **kwargs)
        broker.github = Mock(return_value={'state': 'open'})
        return broker

    def test_default_preserves_registered_command(self):
        before = self.catalog.read_bytes()
        result = self.broker().claim(self.body)
        self.assertEqual(result['job']['command'], self.config['projects'][0]['command'])
        self.assertEqual(self.catalog.read_bytes(), before)

    def test_new_grant_uses_only_operator_override_and_preserves_job_fields(self):
        before = self.catalog.read_bytes()
        result = self.broker(runner_runtime=self.runtime).claim(
            {**self.body, 'command': ['worker-injected'], 'runner_runtime': '/evil'})
        self.assertEqual(result['job']['command'], ['python3', self.runtime + '/scripts/swarm-run-issue.py'])
        self.assertEqual(result['job']['cwd'], '/registered/project')
        self.assertEqual(result['job']['environment']['EXAMPLE'], 'preserved')
        self.assertEqual(result['job']['environment']['HUMANIZE_SWARM_PROTOCOL'], PROTOCOL)
        self.assertEqual(json.loads(result['claim']['job']), result['job'])
        self.assertEqual(self.catalog.read_bytes(), before)

    def test_held_grant_remains_pinned_across_broker_restart(self):
        old = self.broker().claim(self.body)
        updated = self.broker(runner_runtime=self.runtime)
        self.assertEqual(updated.claim(self.body), old)
        updated.github.assert_not_called()
        second = updated.claim({**self.body, 'node': 'hoa1', 'issue': 2, 'attempt': 'second-attempt'})
        self.assertEqual(second['job']['command'], ['python3', self.runtime + '/scripts/swarm-run-issue.py'])
        self.assertEqual(self.ledger.lookup(self.body['attempt'], old['claim']['owner'])['job'], old['claim']['job'])

    def test_quarantine_and_disable_remain_authoritative_without_catalog_writes(self):
        broker = self.broker(runner_runtime=self.runtime)
        before = self.catalog.read_bytes()
        self.assertIsNone(broker.claim({**self.body, 'issue': 3})['claim'])
        self.assertEqual(self.catalog.read_bytes(), before)
        self.config['projects'][0]['enabled'] = False
        self.save()
        before = self.catalog.read_bytes()
        self.assertIsNone(broker.claim(self.body)['claim'])
        self.assertEqual(self.catalog.read_bytes(), before)
        broker.github.assert_not_called()

    def test_runner_override_does_not_resurrect_released_claim(self):
        original = self.broker()
        claim = original.claim(self.body)['claim']
        original.release({**self.body, 'claim_token': claim['token'], 'outcome': 'stopped',
                          'processes_remaining': 0, 'returncode': 1})
        before = self.catalog.read_bytes()
        updated = self.broker(runner_runtime=self.runtime)
        self.assertIsNone(updated.claim(self.body)['claim'])
        self.assertIsNone(updated.claim({**self.body, 'attempt': 'retry-attempt'})['claim'])
        self.assertEqual(json.loads(before)['projects'][0]['quarantined_issues'], [1, 3])
        self.assertEqual(self.catalog.read_bytes(), before)

    def test_unsafe_runtime_paths_rejected(self):
        for value in ('', 'runtime/flows/a', '/runtime/flows', '/runtime/flows/',
                      '/runtime/flows/.', '/runtime/flows/..', '/runtime/flows/a/../b',
                      '/runtime/flows/a/scripts', '/runtime//flows/a', '/runtime/flows/a/',
                      '/tmp/flows/a', '/runtime/flows/a\n', '/runtime/flows/a b',
                      '/runtime/flows/a;echo', '/runtime/flows/' + 'x' * 129, 7):
            with self.subTest(value=value), self.assertRaises(ValueError):
                self.broker(runner_runtime=value)
        self.assertEqual(runner_runtime_path(self.runtime), self.runtime)
        self.assertEqual(runner_runtime_path(Path(self.runtime)), self.runtime)


if __name__ == '__main__':
    unittest.main()
