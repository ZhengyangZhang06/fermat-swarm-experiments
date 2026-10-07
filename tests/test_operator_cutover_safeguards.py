"""Operator safety checks using temporary ledgers and mocked Docker/HTTP only."""
import importlib.util
import json
from pathlib import Path
import sqlite3
import sys
import tempfile
import unittest
from unittest.mock import Mock, patch


def script(name):
    path = Path(__file__).resolve().parents[1] / 'scripts' / (name + '.py')
    spec = importlib.util.spec_from_file_location(name.replace('-', '_'), path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


class OperatorCutoverSafeguards(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.project = self.root / 'project'
        self.project.mkdir()
        self.database = self.root / 'claims.sqlite'
        self.task = 'a' * 25
        self.container = 'b' * 64
        self.status = {'Status': {'State': 'shutdown', 'Timestamp': '2026-10-07T15:00:00Z',
            'ContainerStatus': {'ContainerID': self.container, 'ExitCode': 137, 'PID': 0}}}
        with sqlite3.connect(self.database) as db:
            db.execute('CREATE TABLE claims(attempt TEXT, owner TEXT, token TEXT, job TEXT, state TEXT, scope TEXT)')
            db.execute('INSERT INTO claims VALUES(?,?,?,?,?,?)', ('attempt', 'hoa1/' + self.task + '/boot',
                'test-only-token', json.dumps({'verification': {'project': str(self.project)}}), 'owned', 'project'))
            db.execute('CREATE TABLE verifications(id TEXT, attempt TEXT, state TEXT, pid INTEGER, start_ticks TEXT, log TEXT, returncode INTEGER)')

    def check(self, key, state='queued', pid=None, ticks=None):
        directory = self.root / 'verification'
        directory.mkdir(exist_ok=True)
        with sqlite3.connect(self.database) as db:
            db.execute('INSERT INTO verifications VALUES(?,?,?,?,?,?,?)',
                (key, 'attempt', state, pid, ticks, str(directory / (key + '.log')), None))

    def cancel(self):
        module = script('cancel-unstarted-swarm-checks')
        with patch.object(sys, 'argv', ['cancel', '--database', str(self.database), '--attempt', 'attempt']), \
                patch.object(module.subprocess, 'check_output', return_value=json.dumps([self.status]).encode()):
            module.main()

    def test_cancel_marks_only_unstarted_checks_as_failure(self):
        self.check('queued')
        self.check('running', 'running', 123, '456')
        self.check('uncertain', 'uncertain', 124, '457')
        self.cancel()
        with sqlite3.connect(self.database) as db:
            rows = {row[0]: row[1:] for row in db.execute('SELECT id,state,returncode FROM verifications')}
        self.assertEqual(rows['queued'], ('finished', 125))
        self.assertEqual(rows['running'], ('running', None))
        self.assertEqual(rows['uncertain'], ('uncertain', None))

    def test_cancel_rejects_live_owner_and_process_identity(self):
        self.check('queued', pid=123, ticks='456')
        with self.assertRaisesRegex(RuntimeError, 'process identity'):
            self.cancel()
        self.status['Status']['State'] = 'running'
        with self.assertRaisesRegex(RuntimeError, 'not terminal'):
            self.cancel()
        with sqlite3.connect(self.database) as db:
            self.assertEqual(db.execute('SELECT state FROM verifications').fetchone()[0], 'queued')

    def test_stop_checks_exact_task_and_service_before_post(self):
        module = script('stop-owned-swarm-container')
        response = Mock(status=200)
        response.read.return_value = json.dumps({'Id': self.container, 'Config': {'Labels': {
            'com.docker.swarm.task.id': 'foreign-task', 'com.docker.swarm.service.name': 'legacy'}},
            'State': {'Running': True}}).encode()
        connection = Mock()
        connection.getresponse.return_value = response
        with patch.object(sys, 'argv', ['stop', '--container', self.container, '--task', self.task, '--service', 'legacy']), \
                patch.object(module, 'DockerConnection', return_value=connection):
            with self.assertRaisesRegex(RuntimeError, 'authorized task'):
                module.main()
        self.assertEqual(connection.request.call_count, 1)
        self.assertEqual(connection.request.call_args.args[0], 'GET')

    def reconcile(self, endpoint, host):
        module = script('reconcile-terminal-swarm-claim')
        receipt = self.project / '.humanize/github-theorem-prover/runs/run/nodes/leaf/rlcr-process.json'
        receipt.parent.mkdir(parents=True, exist_ok=True)
        receipt.write_text(json.dumps({'execution_host': host, 'consumed': False}))
        (self.root / 'broker.token').write_text('test-only-not-a-real-token')
        argv = ['reconcile', '--private', str(self.root), '--attempt', 'attempt', '--task', self.task,
                '--receipt', str(receipt), '--endpoint', endpoint]
        with patch.object(sys, 'argv', argv), \
                patch.object(module.subprocess, 'check_output', return_value=json.dumps([self.status]).encode()), \
                patch.object(module.ssl, 'create_default_context'), \
                patch.object(module, 'urlopen', side_effect=AssertionError('unsafe HTTP request reached')):
            module.main()

    def test_reconcile_rejects_plaintext_endpoint_before_transmission(self):
        with self.assertRaisesRegex(RuntimeError, 'HTTPS|TLS|endpoint'):
            self.reconcile('http://example.invalid', self.container[:12])

    def test_reconcile_rejects_credentials_paths_and_queries_in_endpoint(self):
        for endpoint in ('https://user@example.invalid', 'https://example.invalid/path',
                         'https://example.invalid?token=value', 'https://example.invalid#fragment'):
            with self.subTest(endpoint=endpoint), self.assertRaisesRegex(RuntimeError, 'origin'):
                self.reconcile(endpoint, self.container[:12])

    def test_reconcile_rejects_empty_execution_host(self):
        with self.assertRaisesRegex(RuntimeError, 'host|container'):
            self.reconcile('https://example.invalid', '')

    def test_reconcile_preserves_claim_with_pending_verifier(self):
        self.check('live', 'running', 123, '456')
        with self.assertRaisesRegex(RuntimeError, 'verification is not terminal'):
            self.reconcile('https://example.invalid', self.container[:12])
        with sqlite3.connect(self.database) as db:
            self.assertEqual(db.execute('SELECT state FROM claims').fetchone()[0], 'owned')


if __name__ == '__main__':
    unittest.main()
