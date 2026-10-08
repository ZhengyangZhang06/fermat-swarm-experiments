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
    def test_cached_job_uses_only_readonly_named_volume_and_controller_digest(self):
        command = ADAPTER.create_command('job', 'hoa1', 'a' * 32, 'b' * 64,
            Path('/private/job'), Path('/private/job/input'), reference_volume='trusted-reference-volume',
            reference_digest='c' * 64)
        mounts = [command[i + 1] for i, value in enumerate(command) if value == '--mount']
        self.assertIn('type=volume,source=trusted-reference-volume,destination=/reference,readonly,volume-nocopy', mounts)
        self.assertIn('FERMAT_VERIFIER_REFERENCE_CACHE=/reference', command)
        self.assertIn('FERMAT_VERIFIER_REFERENCE_DIGEST=' + 'c' * 64, command)
        self.assertEqual(command[command.index('--limit-memory') + 1], '12G')
        self.assertFalse(any('/.lake/packages' in value or '/toolchains/' in value for value in mounts))
        self.assertEqual([one for one in mounts if one.startswith('type=bind') and not one.endswith(',readonly')],
                         ['type=bind,source=/private/job/output,destination=/output'])
        for forbidden in ('docker.sock', '/home/', '/run/secrets', 'claims.sqlite'):
            self.assertNotIn(forbidden, ' '.join(command))

    def test_remote_cache_configuration_is_explicit_and_fail_closed(self):
        self.assertEqual(ADAPTER.reference_volume_settings({}), (None, None))
        configured = {'FERMAT_VERIFIER_REFERENCE_CACHE': '/private/controller-cache',
                      'FERMAT_VERIFIER_REFERENCE_DIGEST': 'c' * 64,
                      'FERMAT_SWARM_VERIFIER_REFERENCE_VOLUME': 'trusted-reference-volume'}
        self.assertEqual(ADAPTER.reference_volume_settings(configured), ('trusted-reference-volume', 'c' * 64))
        for missing in configured:
            with self.subTest(missing=missing), self.assertRaises(RuntimeError):
                ADAPTER.reference_volume_settings({key: value for key, value in configured.items() if key != missing})
        for key, value in [('FERMAT_VERIFIER_REFERENCE_CACHE', 'relative/path'),
                           ('FERMAT_VERIFIER_REFERENCE_DIGEST', 'g' * 64),
                           ('FERMAT_SWARM_VERIFIER_REFERENCE_VOLUME', 'name,destination=/')]:
            with self.subTest(key=key), self.assertRaises(ValueError):
                ADAPTER.reference_volume_settings({**configured, key: value})

    def test_direct_command_rejects_incomplete_or_injected_cache_binding(self):
        for volume, digest in [('volume', None), (None, 'a' * 64), ('bad,name', 'a' * 64), ('volume', 'bad')]:
            with self.subTest(volume=volume, digest=digest), self.assertRaises(ValueError):
                ADAPTER.create_command('job', 'hoa1', 'a' * 32, 'b' * 64,
                    Path('/private/job'), Path('/private/job/input'), reference_volume=volume, reference_digest=digest)

    def test_cached_task_is_bound_to_actual_authorized_docker_node_id(self):
        node = dict(ID='n' * 25, Description={'Hostname': 'hoa1'}, Status={'State': 'ready'},
                    Spec={'Availability': 'active', 'Labels': {'fermat-swarm-20261007': 'true'}})
        self.assertEqual(ADAPTER.registered_node(node, 'hoa1'), 'n' * 25)
        for bad in ({**node, 'ID': 'invalid'}, {**node, 'Description': {'Hostname': 'hoa2'}},
                    {**node, 'Status': {'State': 'down'}}, {**node, 'Spec': {'Availability': 'drain'}},
                    {**node, 'Spec': {'Availability': 'active', 'Labels': {}}}):
            with self.assertRaises(RuntimeError):
                ADAPTER.registered_node(bad, 'hoa1')
        ADAPTER.bound_task({'NodeID': 'n' * 25, 'Status': {'State': 'running'}}, 'n' * 25)
        ADAPTER.bound_task({'Status': {'State': 'pending'}}, 'n' * 25)
        for task in ({'NodeID': 'x' * 25, 'Status': {'State': 'running'}}, {'Status': {'State': 'complete'}}):
            with self.assertRaisesRegex(RuntimeError, 'node/cache identity'):
                ADAPTER.bound_task(task, 'n' * 25)

    def test_job_has_only_scoped_mounts_and_no_credentials_or_control_socket(self):
        command = ADAPTER.create_command('job', 'hoa1', 'a' * 32, 'b' * 64,
                                         Path('/private/job'), Path('/private/job/input'))
        self.assertEqual(command[command.index('--user') + 1], '1000:1000')
        self.assertEqual(command[command.index('--cap-drop') + 1], 'ALL')
        self.assertEqual(command[command.index('--restart-condition') + 1], 'none')
        self.assertEqual(command[command.index('--limit-memory') + 1], '6G')
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

    def test_dispatcher_node_replacement_fails_before_packet_or_remote_create(self):
        node = dict(ID='n' * 25, Description={'Hostname': 'hoa1'}, Status={'State': 'ready'},
                    Spec={'Availability': 'active', 'Labels': {'fermat-swarm-20261007': 'true'}})
        environment = dict(FERMAT_VERIFICATION_REQUEST_ID='a' * 32,
                           FERMAT_SWARM_VERIFIER_NODE='hoa1',
                           FERMAT_SWARM_VERIFIER_EXPECTED_NODE_ID='x' * 25)
        with patch.dict(os.environ, environment, clear=True), patch.object(ADAPTER.os, 'umask'), \
                patch.object(ADAPTER, 'inspect', return_value=node), \
                patch.object(ADAPTER, 'docker') as docker, \
                patch.object(ADAPTER.Path, 'mkdir') as mkdir:
            with self.assertRaisesRegex(RuntimeError, 'durable dispatcher/readiness identity'):
                ADAPTER.execute()
            docker.assert_not_called()
            mkdir.assert_not_called()


if __name__ == '__main__':
    unittest.main()
