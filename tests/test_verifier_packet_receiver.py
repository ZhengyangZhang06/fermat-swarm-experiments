import importlib.util
from pathlib import Path
import unittest
from unittest.mock import patch


SOURCE = Path(__file__).resolve().parents[1] / 'scripts/swarm-verifier-packet.py'
SPEC = importlib.util.spec_from_file_location('packet_receiver', SOURCE)
RECEIVER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(RECEIVER)


class PacketReceiverTests(unittest.TestCase):
    def test_cached_receiver_points_all_packages_to_fixed_trusted_mount(self):
        self.assertEqual(RECEIVER.reference_packages({}), RECEIVER.PACKAGES)
        self.assertEqual(RECEIVER.reference_packages({'FERMAT_VERIFIER_REFERENCE_CACHE': '/reference',
            'FERMAT_VERIFIER_REFERENCE_DIGEST': 'a' * 64}), Path('/reference/packages'))

    def test_cache_configuration_rejects_missing_digest_and_arbitrary_paths(self):
        for environment in ({'FERMAT_VERIFIER_REFERENCE_CACHE': '/reference'},
                {'FERMAT_VERIFIER_REFERENCE_DIGEST': 'a' * 64},
                {'FERMAT_VERIFIER_REFERENCE_CACHE': '/worker-writable', 'FERMAT_VERIFIER_REFERENCE_DIGEST': 'a' * 64},
                {'FERMAT_VERIFIER_REFERENCE_CACHE': '/reference', 'FERMAT_VERIFIER_REFERENCE_DIGEST': 'bad'}):
            with self.subTest(environment=environment), self.assertRaises(RuntimeError):
                RECEIVER.reference_packages(environment)

    def test_root_execution_is_refused_before_reading_input(self):
        with patch.object(RECEIVER.os, 'geteuid', return_value=0):
            with self.assertRaisesRegex(RuntimeError, 'unprivileged'):
                RECEIVER.execute(Path('/missing'), 'a' * 64, Path('/missing-output'))

    def test_digest_must_be_a_full_controller_sha256(self):
        with patch.object(RECEIVER.os, 'geteuid', return_value=1000):
            for digest in ('', 'a' * 63, 'a' * 65, 'g' * 64, '../request', 'A' * 64):
                with self.subTest(digest=digest), self.assertRaisesRegex(ValueError, 'controller packet digest'):
                    RECEIVER.execute(Path('/missing'), digest, Path('/missing-output'))


if __name__ == '__main__':
    unittest.main()
