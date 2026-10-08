import importlib.util
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

SPEC = importlib.util.spec_from_file_location('dispatcher_provisioner',
    Path(__file__).resolve().parents[1] / 'scripts/provision-remote-verifier-dispatchers.py')
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class ProvisioningTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.config = dict(nodes=['hoa3', 'hoa4'], unit_prefix='test-verifier', reference_digest='a' * 64,
                           reference_volume='trusted-cache')
        for field in ('workflow_root', 'readiness_directory', 'packet_directory', 'reference_cache'):
            path = self.root / field
            path.mkdir(mode=0o700)
            self.config[field] = str(path)
        for field in ('python', 'database'):
            path = self.root / field
            path.touch(mode=0o600)
            self.config[field] = str(path)
        scripts = Path(self.config['workflow_root']) / 'scripts'
        scripts.mkdir()
        for name in ('swarm-dispatch-verification.py', 'swarm-verify-frozen-node.py'):
            (scripts / name).touch()
        self.units = self.root / 'units'
        self.units.mkdir(mode=0o700)
        self.loaded = False
        self.started = []
        self.systemctl = patch.object(MODULE, 'systemctl', side_effect=self.control).start()
        self.addCleanup(patch.stopall)

    def state(self, name):
        path = self.units / name
        if not self.loaded or not path.exists():
            return dict(LoadState='not-found', ActiveState='inactive', FragmentPath='', DropInPaths='')
        content = path.read_text()
        pairs = [line.split('=', 1) for line in content.splitlines() if '=' in line]
        fields = dict(pairs)
        return dict(LoadState='loaded', ActiveState='active' if name in self.started else 'inactive',
                    FragmentPath=str(path), DropInPaths='',
                    ExecStart='{ path=' + self.config['python'] + ' ; argv[]=' + fields['ExecStart'] +
                              ' ; ignore_errors=no ; start_time=[n/a] ; stop_time=[n/a] ; pid=0 ; code=(null) ; status=0/0 }',
                    Environment=' '.join(value.strip('"') for key, value in pairs if key == 'Environment'),
                    EnvironmentFiles='', Type='simple', Restart='no', KillMode='process',
                    UMask='0077', SendSIGKILL='no', TimeoutStopUSec='infinity')

    def control(self, *args):
        if args[0] == 'show':
            return '\n'.join(f'{key}={value}' for key, value in self.state(args[1]).items())
        if args[0] == 'daemon-reload':
            self.loaded = True
        elif args[0] == 'start':
            self.started.append(args[1])
        else:
            self.fail('unexpected systemd mutation: ' + str(args))
        return ''

    def provision(self, **options):
        return MODULE.provision(self.config, self.units, **options)

    def test_default_plan_does_not_write_or_start(self):
        result = self.provision()
        self.assertEqual([row['action'] for row in result], ['planned-new', 'planned-new'])
        self.assertEqual(list(self.units.iterdir()), [])
        self.assertEqual(list(Path(self.config['readiness_directory']).iterdir()), [])
        self.assertEqual(self.started, [])

    def test_initial_false_gates_and_exact_new_unit_starts(self):
        self.provision(apply=True, start_new=True)
        self.assertEqual(self.started, ['test-verifier-hoa3.service', 'test-verifier-hoa4.service'])
        for node in self.config['nodes']:
            gate = Path(self.config['readiness_directory']) / f'{node}.json'
            self.assertEqual(json.loads(gate.read_text()), dict(node=node, verifier_ready=False))
            self.assertEqual(gate.stat().st_mode & 0o777, 0o600)
            unit = (self.units / f'test-verifier-{node}.service').read_text()
            self.assertIn(f'--remote-node {node}', unit)
            self.assertIn('Restart=no', unit)
            self.assertNotIn('.codex', unit)

    def test_repeated_provision_never_restarts_active_or_inactive_units(self):
        self.provision(apply=True, start_new=True)
        self.started.clear()  # Existing inactive units must not be started either.
        result = self.provision(apply=True, start_new=True)
        self.assertTrue(all(row['action'] == 'unchanged' for row in result))
        self.assertEqual(self.started, [])

    def test_existing_true_gate_is_preserved(self):
        gate = Path(self.config['readiness_directory']) / 'hoa3.json'
        gate.write_text(json.dumps(dict(verifier_ready=True, node='hoa3', evidence='retained')))
        gate.chmod(0o600)
        before = gate.read_bytes()
        self.provision(apply=True)
        self.assertEqual(gate.read_bytes(), before)

    def test_changed_unit_or_environment_is_never_replaced(self):
        self.provision(apply=True)
        self.config['reference_digest'] = 'b' * 64
        with self.assertRaisesRegex(RuntimeError, 'differs'):
            self.provision(apply=True, start_new=True)
        self.assertEqual(self.started, [])

    def test_loaded_cached_command_mismatch_blocks_even_if_file_matches(self):
        self.provision(apply=True)
        original = self.state
        def wrong(name):
            value = original(name)
            value['ExecStart'] = value['ExecStart'].replace('--remote-node hoa3', '--remote-node hoa7')
            return value
        with patch.object(self, 'state', side_effect=wrong):
            with self.assertRaisesRegex(RuntimeError, 'command differs'):
                self.provision(apply=True)

    def test_dropins_or_foreign_runtime_units_block(self):
        for state in (dict(LoadState='loaded', ActiveState='active', DropInPaths='', FragmentPath='/foreign'),
                      dict(LoadState='not-found', ActiveState='inactive', DropInPaths='/override')):
            with self.subTest(state=state), patch.object(MODULE, 'unit_state', return_value=state):
                with self.assertRaises(RuntimeError):
                    self.provision(apply=True)
        self.assertEqual(list(self.units.iterdir()), [])

    def test_uncertain_start_is_not_retried_on_next_invocation(self):
        real = self.control
        def uncertain(*args):
            if args[0] == 'start' and args[1] == 'test-verifier-hoa3.service':
                raise TimeoutError('lost start response')
            return real(*args)
        self.systemctl.side_effect = uncertain
        result = self.provision(apply=True, start_new=True)
        self.assertEqual([row['action'] for row in result], ['needs-reconciliation', 'started-new'])
        self.assertEqual(self.started, ['test-verifier-hoa4.service'])
        self.systemctl.side_effect = real
        self.provision(apply=True, start_new=True)
        self.assertEqual(self.started, ['test-verifier-hoa4.service'])

    def test_invalid_nodes_and_systemd_injection_rejected(self):
        for change in (dict(nodes=['hoa128']), dict(nodes=['hoa3', 'hoa3']), dict(nodes=[]),
                       dict(unit_prefix='bad\nExecStart=attack'), dict(python='/bin/python%h'),
                       dict(reference_volume='bad\nEnvironment=attack')):
            with self.subTest(change=change), self.assertRaises(ValueError):
                MODULE.provision({**self.config, **change}, self.units)

    def test_symlink_or_public_packet_directory_rejected(self):
        packet = Path(self.config['packet_directory']) / 'hoa3'
        packet.symlink_to(self.root, target_is_directory=True)
        with self.assertRaises(RuntimeError):
            self.provision(apply=True)
        packet.unlink()
        Path(self.config['packet_directory']).chmod(0o755)
        with self.assertRaises(RuntimeError):
            self.provision(apply=True)

    def test_start_requires_apply(self):
        with self.assertRaisesRegex(ValueError, 'requires'):
            self.provision(start_new=True)


if __name__ == '__main__':
    unittest.main()
