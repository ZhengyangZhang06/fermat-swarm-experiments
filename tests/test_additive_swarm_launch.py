import importlib.util
import json
from pathlib import Path
import sqlite3
import sys
import tempfile
import unittest
from unittest.mock import patch


spec = importlib.util.spec_from_file_location('additive_launch', Path(__file__).resolve().parents[1] / 'scripts/launch-parallel-swarm.py')
launch = importlib.util.module_from_spec(spec)
spec.loader.exec_module(launch)


class AdditiveLaunchTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.root.chmod(0o700)
        self.database = self.root / 'claims.sqlite'
        self.catalog = {'repository': 'Owner/Repo', 'verifier_ready': True, 'projects': [
            {'id': 'p1', 'enabled': True, 'quarantined_issues': [21, 22]}]}
        with sqlite3.connect(self.database) as db:
            db.execute('CREATE TABLE claims(attempt TEXT,state TEXT,job TEXT,receipt TEXT,project TEXT,repository TEXT,issue INTEGER)')
            db.execute('CREATE TABLE verifications(attempt TEXT,state TEXT)')
            db.execute('INSERT INTO claims VALUES(?,?,?,?,?,?,?)', ('attempt1', 'released',
                json.dumps({'log_directory': str(self.root)}), json.dumps({'state': 'terminal', 'returncode': 1}),
                'p1', 'owner/repo', 21))
        (self.root / 'attempt1.log').write_text('Traceback (most recent call last):\n'
            '_recursive_lean.github.PublicationError: GitHub PATCH issues/21 failed; '
            'check gh authentication/repository access, then resume\n')

    def test_only_explicit_terminal_publication_failure_is_retried(self):
        evidence = launch.retry_publication_failures(self.catalog, self.database, [21])
        self.assertEqual(self.catalog['projects'][0]['quarantined_issues'], [22])
        self.assertEqual(evidence[0]['attempt'], 'attempt1')
        with sqlite3.connect(self.database) as db:
            self.assertEqual(db.execute('select state from claims').fetchone()[0], 'released')

    def test_live_or_uncertain_receipt_is_not_retried(self):
        for change in ("state='owned'", "receipt='{}'"):
            with sqlite3.connect(self.database) as db:
                db.execute('UPDATE claims SET ' + change)
            with self.assertRaises(RuntimeError):
                launch.retry_publication_failures(self.catalog, self.database, [21])
        self.assertEqual(self.catalog['projects'][0]['quarantined_issues'], [21, 22])

    def test_pending_verifier_is_not_retried(self):
        with sqlite3.connect(self.database) as db:
            db.execute("INSERT INTO verifications VALUES('attempt1','queued')")
        with self.assertRaisesRegex(RuntimeError, 'nonterminal verification'):
            launch.retry_publication_failures(self.catalog, self.database, [21])

    def test_math_failure_after_prior_publication_error_is_not_retried(self):
        with (self.root / 'attempt1.log').open('a') as log:
            log.write('Traceback (most recent call last):\nValueError: proof contract mismatch\n')
        with self.assertRaisesRegex(RuntimeError, 'publication failure'):
            launch.retry_publication_failures(self.catalog, self.database, [21])

    def test_existing_comparator_mount_is_replaced_not_duplicated(self):
        mounts = launch.mount_arguments({'Mounts': [
            {'Type': 'bind', 'Source': '/old/client.py', 'Target': launch.COMPARATOR_TARGET},
            {'Type': 'bind', 'Source': '/runtime', 'Target': '/runtime', 'ReadOnly': True},
            {'Type': 'tmpfs', 'Target': '/home/ubuntu', 'TmpfsOptions': {'Mode': 0o1777}},
        ]}, Path('/immutable/new'))
        self.assertEqual(sum(launch.COMPARATOR_TARGET in arg for arg in mounts), 1)
        self.assertNotIn('/old/client.py', ' '.join(mounts))
        self.assertIn('type=bind,source=/runtime,destination=/runtime,readonly', mounts)

    def test_additive_launch_does_not_mutate_source_or_restart_existing_service(self):
        flow = self.root / 'runtime'
        (flow / 'scripts').mkdir(parents=True)
        (flow / 'scripts/swarm-bootstrap.py').write_text('# test')
        source = self.root / 'parallel-catalog.json'
        source.write_text(json.dumps(self.catalog))
        source_bytes = source.read_bytes()
        source_spec = {'Spec': {'TaskTemplate': {'ContainerSpec': {'Image': 'ubuntu:test',
            'Env': ['HUMANIZE_SWARM_ENDPOINT=https://old:8848'], 'Mounts': [], 'Secrets': [
                {'SecretName': 'old-token', 'File': {'Name': 'broker_token', 'UID': '1000', 'GID': '1000', 'Mode': 0o400}}],
            'Configs': [{'ConfigName': 'broker-ca', 'File': {'Name': '/broker.crt', 'UID': '0', 'GID': '0', 'Mode': 0o444}}]},
            'Placement': {'Constraints': ['node.labels.authorized==true']}}}}
        commands = []
        def command(*args, **kwargs):
            commands.append(args)
            return json.dumps([source_spec]) if 'inspect' in args else 'created-service'
        args = ['launch', '--private', str(self.root), '--runtime', str(flow), '--container-runtime', '/runtime/new',
            '--legacy-service', 'old-workers', '--service', 'new-workers', '--unit', 'new-broker',
            '--bind', '10.44.0.210', '--port', '8849', '--python', '/python', '--gh', '/gh', '--verifier', '/checker',
            '--source-catalog', source.name, '--deployment-prefix', 'recovery', '--additive', '--verifier-paused',
            '--retry-publication-issue', '21']
        with patch.object(sys, 'argv', args), patch.object(launch, 'command', command):
            launch.main()
        self.assertEqual(source.read_bytes(), source_bytes)
        result = json.loads((self.root / 'recovery-catalog.json').read_text())
        self.assertFalse(result['verifier_ready'])
        self.assertEqual(result['projects'][0]['quarantined_issues'], [22])
        self.assertTrue(result['projects'][0]['enabled'])
        broker = next(args for args in commands if args[0] == 'systemd-run')
        self.assertIn('--preserve-existing-verifications', broker)
        self.assertIn(str(self.database), broker)
        self.assertFalse(any('restart' in args or 'stop' in args or 'update' in args for args in commands))
        create = next(args for args in commands if 'service' in args and 'create' in args)
        self.assertIn('HUMANIZE_SWARM_ENDPOINT=https://10.44.0.210:8849', create)
        self.assertNotIn('HUMANIZE_SWARM_ENDPOINT=https://old:8848', create)
        self.assertIn('source=new-workers-broker-token,target=broker_token,uid=1000,gid=1000,mode=0400', create)
        self.assertIn('source=broker-ca,target=/broker.crt,uid=0,gid=0,mode=0444', create)


if __name__ == '__main__':
    unittest.main()
