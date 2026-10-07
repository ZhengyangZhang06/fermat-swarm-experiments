import contextlib
import importlib.util
import io
import json
from pathlib import Path
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch


SOURCE = Path(__file__).resolve().parents[1] / 'scripts/test-swarm-verifier-roundtrip.py'
SPEC = importlib.util.spec_from_file_location('roundtrip_fixture', SOURCE)
ROUNDTRIP = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(ROUNDTRIP)


class RoundtripFixtureTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.manifest = self.root / 'trusted-manifest.json'
        self.record = {'version': '1.2.0', 'packagesDir': '.lake/packages', 'packages': [
            {'type': 'git', 'name': 'mathlib', 'rev': 'a' * 40, 'url': 'https://example.invalid/mathlib'},
            {'type': 'git', 'name': 'batteries', 'rev': 'b' * 40}], 'name': 'trusted fixture'}
        self.encoded = (json.dumps(self.record, indent=3) + '\n\n').encode()
        self.manifest.write_bytes(self.encoded)

    def test_default_cheap_fixtures_are_unchanged(self):
        contract, fixtures, manifest = ROUNDTRIP.fixture_inputs()
        self.assertEqual(contract, 'theorem toy : True\n')
        self.assertEqual(fixtures, [
            ('valid', 'theorem toy : True := True.intro\n', 0),
            ('changed-statement', 'theorem toy : False → False := fun h => h\n', 1)])
        self.assertEqual(manifest, b'{"packages": []}')

    def test_mathlib_import_preserves_exact_positive_and_changed_type_cases(self):
        contract, fixtures, manifest = ROUNDTRIP.fixture_inputs(True, self.manifest)
        prefix = 'import Mathlib.Data.Nat.Basic\n\n'
        self.assertEqual(contract, prefix + 'theorem toy : True\n')
        self.assertEqual(fixtures, [
            ('valid', prefix + 'theorem toy : True := True.intro\n', 0),
            ('changed-statement', prefix + 'theorem toy : False → False := fun h => h\n', 1)])
        self.assertEqual(manifest, self.encoded)

    def test_flags_are_required_together(self):
        for enabled, manifest in ((True, None), (False, self.manifest)):
            with self.subTest(enabled=enabled), self.assertRaisesRegex(ValueError, 'required together'):
                ROUNDTRIP.fixture_inputs(enabled, manifest)

    def test_missing_malformed_and_duplicate_json_keys_rejected(self):
        with self.assertRaises(ValueError):
            ROUNDTRIP.fixture_inputs(True, self.root / 'missing')
        for content in (b'{', b'\xff', b'{"packages":[],"packages":[]}'):
            self.manifest.write_bytes(content)
            with self.subTest(content=content), self.assertRaises(ValueError):
                ROUNDTRIP.fixture_inputs(True, self.manifest)

    def test_non_git_unpinned_unsafe_duplicate_and_missing_mathlib_records_rejected(self):
        package = self.record['packages'][0]
        invalid = [None, [], {}, {'packages': []}, {'packages': {}},
                   {**self.record, 'packagesDir': '/outside'},
                   {'packages': [None]}, {'packages': [{**package, 'type': 'path'}]},
                   {'packages': [{**package, 'rev': 'main'}]},
                   {'packages': [{**package, 'rev': None}]},
                   {'packages': [{**package, 'name': '../mathlib'}]},
                   {'packages': [{**package, 'name': 1}]},
                   {'packages': [package, package]},
                   {'packages': [self.record['packages'][1]]}]
        for manifest in invalid:
            self.manifest.write_text(json.dumps(manifest))
            with self.subTest(manifest=manifest), self.assertRaises(ValueError):
                ROUNDTRIP.fixture_inputs(True, self.manifest)

    def arguments(self, output):
        return ['roundtrip', '--adapter', '/operator/immutable/adapter.py',
                '--directory', str(output), '--node', 'hoa127']

    def test_cli_validates_all_opt_in_inputs_before_creating_directories(self):
        variants = [['--mathlib-fixture'], ['--dependency-manifest', str(self.manifest)],
                    ['--mathlib-fixture', '--dependency-manifest', str(self.root / 'missing')]]
        for index, options in enumerate(variants):
            output = self.root / f'bad-{index}'
            with patch('sys.argv', self.arguments(output) + options), \
                    patch.object(ROUNDTRIP, 'git') as git, patch.object(ROUNDTRIP.subprocess, 'run') as run, \
                    contextlib.redirect_stderr(io.StringIO()), self.assertRaises(SystemExit) as raised:
                ROUNDTRIP.main()
            self.assertEqual(raised.exception.code, 2)
            self.assertFalse(output.exists())
            git.assert_not_called()
            run.assert_not_called()

    def test_cli_copies_manifest_exactly_into_both_frozen_fixtures(self):
        output = self.root / 'roundtrip'
        frozen = []
        invoked = []
        def git(project, *args):
            if args == ('commit', '-qm', 'Freeze toy verification contract'):
                frozen.append(((project / 'lake-manifest.json').read_bytes(),
                               (project / 'Frozen.lean').read_text(),
                               (project / 'Submission.lean').read_text()))
            return 'a' * 40
        def adapter(command, *, cwd, env, stdout, stderr):
            name = cwd.name
            invoked.append((name, (cwd / 'Submission.lean').read_text()))
            receipt = Path(env['FERMAT_SWARM_VERIFIER_DIRECTORY']) / env['FERMAT_VERIFICATION_REQUEST_ID']
            receipt.mkdir()
            success = name == 'valid'
            if not success:
                stdout.write("Challenge and solution theorem statement do not match: 'toy'\n")
            (receipt / 'operation.json').write_text(json.dumps({
                'state': 'verified' if success else 'terminal',
                'task_id': 'fixture-task', 'service_id': 'fixture-service'}))
            return SimpleNamespace(returncode=0 if success else 1)
        with patch('sys.argv', self.arguments(output) + ['--mathlib-fixture', '--dependency-manifest', str(self.manifest)]), \
                patch.object(ROUNDTRIP, 'git', side_effect=git), \
                patch.object(ROUNDTRIP.subprocess, 'run', side_effect=adapter), \
                contextlib.redirect_stdout(io.StringIO()):
            ROUNDTRIP.main()
        prefix = 'import Mathlib.Data.Nat.Basic\n\n'
        self.assertEqual(frozen, [(self.encoded, prefix + 'theorem toy : True\n',
                                  prefix + 'theorem toy : True := by sorry\n')] * 2)
        self.assertEqual(invoked, [('valid', prefix + 'theorem toy : True := True.intro\n'),
                                  ('changed-statement', prefix + 'theorem toy : False → False := fun h => h\n')])
        for name, _ in invoked:
            self.assertEqual((output / 'projects' / name / 'lake-manifest.json').read_bytes(), self.encoded)

    def test_negative_fixture_rejects_unrelated_failure_despite_terminal_exit_one(self):
        for index, diagnostic in enumerate(('I/O failure\n', 'out of memory\n',
                "Challenge and solution theorem statement do not match: 'other'\n", '')):
            output = self.root / f'wrong-reason-{index}'
            def adapter(command, *, cwd, env, stdout, stderr):
                success = cwd.name == 'valid'
                receipt = Path(env['FERMAT_SWARM_VERIFIER_DIRECTORY']) / env['FERMAT_VERIFICATION_REQUEST_ID']
                receipt.mkdir()
                (receipt / 'operation.json').write_text(json.dumps({
                    'state': 'verified' if success else 'terminal',
                    'task_id': 'fixture-task', 'service_id': 'fixture-service'}))
                if not success:
                    stdout.write(diagnostic)
                return SimpleNamespace(returncode=0 if success else 1)
            with self.subTest(diagnostic=diagnostic), \
                    patch('sys.argv', self.arguments(output)), \
                    patch.object(ROUNDTRIP, 'git', return_value='a' * 40), \
                    patch.object(ROUNDTRIP.subprocess, 'run', side_effect=adapter), \
                    contextlib.redirect_stdout(io.StringIO()), \
                    self.assertRaisesRegex(RuntimeError, 'missing actual comparator statement-mismatch evidence'):
                ROUNDTRIP.main()


if __name__ == '__main__':
    unittest.main()
