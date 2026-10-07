import hashlib
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch


class VerificationPacketTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.project = self.root / 'workers' / 'project'
        self.project.mkdir(parents=True)
        self.source = Path(__file__).resolve().parents[1] / 'scripts/verify-frozen-node.py'
        spec = importlib.util.spec_from_file_location('packet_verifier', self.source)
        self.checker = importlib.util.module_from_spec(spec)
        with patch.dict(os.environ, FERMAT_VERIFIER_PROJECT=str(self.project)):
            spec.loader.exec_module(self.checker)
        self.packet_root = self.root / 'packet'
        for side, filename in [('challenge', 'Challenge.lean'), ('solution', 'Solution.lean')]:
            self.checker.write(self.packet_root / side / filename, 'theorem toy : True := by trivial\n')
        self.evidence = dict(status='checking', candidate_commit='a' * 40,
                             checked_theorems=['toy'], dependency_revisions={},
                             verifier_sha256=hashlib.sha256(self.source.read_bytes()).hexdigest())
        self.packet = dict(schema=1, evidence=self.evidence, dependency_manifest={'packages': []},
                           source_sha256=self.checker.source_hashes(self.packet_root))
        self.save_packet()

    def save_packet(self):
        self.checker.write(self.packet_root / 'prepared.json', json.dumps(self.packet))
        self.checker.write(self.packet_root / 'evidence.json', json.dumps(self.evidence))
        self.digest = self.checker.prepared_digest(self.packet)

    def validate(self):
        return self.checker.validate_prepared(self.packet_root, self.digest)

    def test_exact_packet_validates_without_accepting_a_proof(self):
        self.assertEqual(self.validate(), self.packet)
        self.assertEqual(json.loads((self.packet_root / 'evidence.json').read_text())['status'], 'checking')

    def test_changed_contract_source_is_rejected(self):
        (self.packet_root / 'challenge/Challenge.lean').write_text('theorem toy : False := by sorry')
        with self.assertRaisesRegex(RuntimeError, 'sources differ'):
            self.validate()

    def test_added_and_missing_sources_are_rejected(self):
        extra = self.packet_root / 'solution/Extra.lean'
        extra.write_text('axiom bad : False')
        with self.assertRaisesRegex(RuntimeError, 'sources differ'):
            self.validate()
        extra.unlink()
        (self.packet_root / 'solution/Solution.lean').unlink()
        with self.assertRaisesRegex(RuntimeError, 'entrypoints are missing'):
            self.validate()

    def test_snapshot_metadata_cannot_be_rebound_to_another_revision(self):
        self.packet['evidence']['candidate_commit'] = 'b' * 40
        (self.packet_root / 'prepared.json').write_text(json.dumps(self.packet))
        with self.assertRaisesRegex(RuntimeError, 'controller digest'):
            self.validate()

    def test_evidence_file_cannot_be_rebound(self):
        (self.packet_root / 'evidence.json').write_text(json.dumps({**self.evidence, 'candidate_commit': 'b' * 40}))
        with self.assertRaisesRegex(RuntimeError, 'evidence differs'):
            self.validate()

    def test_wrong_verifier_and_premature_success_are_rejected(self):
        for key, value, message in [('verifier_sha256', '0' * 64, 'verifier identity'),
                                    ('status', 'verified', 'unverified input')]:
            original = self.evidence[key]
            self.evidence[key] = value
            self.save_packet()
            with self.assertRaisesRegex(RuntimeError, message):
                self.validate()
            self.evidence[key] = original

    def test_symlink_sources_and_packet_are_rejected(self):
        link = self.packet_root / 'solution/Escape.lean'
        link.symlink_to(self.source)
        with self.assertRaisesRegex(RuntimeError, 'symlink'):
            self.validate()
        link.unlink()
        p = self.packet_root / 'prepared.json'
        p.rename(self.root / 'outside-packet.json')
        p.symlink_to(self.root / 'outside-packet.json')
        with self.assertRaisesRegex(RuntimeError, 'symlink'):
            self.validate()

    def test_generated_lake_build_files_do_not_change_input_digest(self):
        self.checker.write(self.packet_root / 'solution/lakefile.lean', 'import Lake')
        self.checker.write(self.packet_root / 'solution/.lake/build/Generated.lean', 'generated')
        self.validate()

    def test_nested_lakefile_is_still_a_source_input(self):
        self.checker.write(self.packet_root / 'solution/Some/lakefile.lean', 'axiom bad : False')
        with self.assertRaisesRegex(RuntimeError, 'sources differ'):
            self.validate()

    def test_dependency_mismatch_stops_before_comparator(self):
        with patch.object(self.checker, 'check_dependency_sources', return_value={'changed': 'x'}), \
                patch.object(self.checker, 'compare') as compare:
            with self.assertRaisesRegex(RuntimeError, 'dependency revisions changed'):
                self.checker.verify_prepared(self.packet_root, self.digest)
            compare.assert_not_called()

    def test_comparator_failure_does_not_mark_verified(self):
        with patch.object(self.checker, 'check_dependency_sources', return_value={}), \
                patch.object(self.checker, 'compare', side_effect=subprocess.CalledProcessError(1, 'compare')):
            with self.assertRaises(subprocess.CalledProcessError):
                self.checker.verify_prepared(self.packet_root, self.digest)
        self.assertEqual(json.loads((self.packet_root / 'evidence.json').read_text())['status'], 'checking')

    def test_input_mutation_during_comparator_is_rejected(self):
        def mutate(*args):
            (self.packet_root / 'solution/Solution.lean').write_text('changed')
        with patch.object(self.checker, 'check_dependency_sources', return_value={}), \
                patch.object(self.checker, 'compare', side_effect=mutate), patch.object(self.checker, 'sandbox') as sandbox:
            with self.assertRaisesRegex(RuntimeError, 'sources differ'):
                self.checker.verify_prepared(self.packet_root, self.digest)
            sandbox.assert_not_called()

    def test_axiom_report_failure_does_not_mark_verified(self):
        with patch.object(self.checker, 'check_dependency_sources', return_value={}), \
                patch.object(self.checker, 'compare'), \
                patch.object(self.checker, 'sandbox', side_effect=subprocess.CalledProcessError(1, 'axioms')):
            with self.assertRaises(subprocess.CalledProcessError):
                self.checker.verify_prepared(self.packet_root, self.digest)
        self.assertEqual(json.loads((self.packet_root / 'evidence.json').read_text())['status'], 'checking')

    def test_success_requires_comparison_axiom_report_and_final_dependency_check(self):
        with patch.object(self.checker, 'check_dependency_sources', return_value={}) as dependencies, \
                patch.object(self.checker, 'compare') as compare, patch.object(self.checker, 'sandbox') as sandbox:
            self.checker.verify_prepared(self.packet_root, self.digest)
        compare.assert_called_once_with(self.packet_root, ['toy'])
        sandbox.assert_called_once()
        self.assertEqual(dependencies.call_count, 2)
        self.assertEqual(json.loads((self.packet_root / 'evidence.json').read_text())['status'], 'verified')

    def test_late_dependency_change_does_not_mark_verified(self):
        with patch.object(self.checker, 'check_dependency_sources', side_effect=[{}, {'changed': 'x'}]), \
                patch.object(self.checker, 'compare'), patch.object(self.checker, 'sandbox'):
            with self.assertRaisesRegex(RuntimeError, 'dependency revisions changed during verification'):
                self.checker.verify_prepared(self.packet_root, self.digest)
        self.assertEqual(json.loads((self.packet_root / 'evidence.json').read_text())['status'], 'checking')

    def test_packet_cannot_be_rebound_to_another_reference_cache(self):
        with patch.object(self.checker, 'validate_reference_cache', return_value='a' * 64):
            with self.assertRaisesRegex(RuntimeError, 'reference cache binding'):
                self.validate()

    def test_late_reference_corruption_does_not_mark_verified(self):
        count = 0
        def validate(*, contents=False):
            nonlocal count
            if contents:
                count += 1
                if count == 2:
                    raise RuntimeError('reference cache artifacts changed')
            return None
        with patch.object(self.checker, 'validate_reference_cache', side_effect=validate), \
                patch.object(self.checker, 'check_dependency_sources', return_value={}), \
                patch.object(self.checker, 'compare'), patch.object(self.checker, 'sandbox'):
            with self.assertRaisesRegex(RuntimeError, 'artifacts changed'):
                self.checker.verify_prepared(self.packet_root, self.digest)
        self.assertEqual(json.loads((self.packet_root / 'evidence.json').read_text())['status'], 'checking')


if __name__ == '__main__':
    unittest.main()
