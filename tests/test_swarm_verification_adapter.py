import importlib.util
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch


SOURCE = Path(__file__).resolve().parents[1] / 'scripts/swarm-verify-frozen-node.py'
SPEC = importlib.util.spec_from_file_location('swarm_adapter', SOURCE)
ADAPTER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(ADAPTER)


class SwarmAdapterTests(unittest.TestCase):
    def test_job_has_only_scoped_mounts_and_no_credentials_or_control_socket(self):
        command = ADAPTER.create_command('job', 'hoa1', 'a' * 32, 'b' * 64,
                                         Path('/private/job'), Path('/private/job/input'))
        self.assertEqual(command[command.index('--user') + 1], '1000:1000')
        self.assertEqual(command[command.index('--cap-drop') + 1], 'ALL')
        self.assertEqual(command[command.index('--restart-condition') + 1], 'none')
        self.assertIn('--read-only', command)
        self.assertIn(ADAPTER.IMAGE, command)
        mounts = [command[i + 1] for i, value in enumerate(command) if value == '--mount']
        writable = [value for value in mounts if value.startswith('type=bind') and not value.endswith(',readonly')]
        self.assertEqual(writable, ['type=bind,source=/private/job/output,destination=/output'])
        self.assertEqual(len(mounts), 7)
        for forbidden in ('docker.sock', '/home/', '/run/secrets', 'claims.sqlite'):
            self.assertNotIn(forbidden, ' '.join(command))

    def test_mount_field_injection_is_rejected(self):
        with self.assertRaisesRegex(ValueError, 'mount path'):
            ADAPTER.create_command('job', 'hoa1', 'a' * 32, 'b' * 64,
                                   Path('/private/other,destination=/'), Path('/private/input'))

    def test_invalid_node_and_request_stop_before_creating_a_job(self):
        for request, node in [('bad', 'hoa1'), ('a' * 32, 'hoa128'), ('a' * 32, 'manager'), ('a' * 32, 'hoa01')]:
            with self.subTest(request=request, node=node), \
                    patch.dict(os.environ, FERMAT_VERIFICATION_REQUEST_ID=request, FERMAT_SWARM_VERIFIER_NODE=node), \
                    patch.object(ADAPTER.os, 'umask'), self.assertRaisesRegex(ValueError, 'registered request'):
                ADAPTER.execute()

    def test_private_receipt_is_atomically_replaced(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / 'operation.json'
            ADAPTER.record(path, {'state': 'prepared'})
            ADAPTER.record(path, {'state': 'submitted', 'service_id': 'known'})
            self.assertEqual(json.loads(path.read_text()), {'state': 'submitted', 'service_id': 'known'})
            self.assertFalse(path.with_suffix('.tmp').exists())


if __name__ == '__main__':
    unittest.main()
