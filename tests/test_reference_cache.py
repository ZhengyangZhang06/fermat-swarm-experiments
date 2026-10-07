import contextlib
import hashlib
import importlib.util
import io
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch


class ReferenceCacheTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.project = self.root / 'workers/project'
        self.project.mkdir(parents=True)
        self.cache = self.root / 'cache'
        self.cache.mkdir(mode=0o700)
        (self.cache / 'packages/mathlib').mkdir(parents=True)
        (self.cache / 'lean-4.33.1-linux/bin').mkdir(parents=True)
        self.artifact = self.cache / 'packages/mathlib/Artifact.olean'
        self.artifact.write_bytes(b'trusted fixture artifact')
        self.binary = self.cache / 'lean-4.33.1-linux/bin/lean'
        self.binary.write_bytes(b'fixture executable, never run')
        self.binary.chmod(0o755)
        source = Path(__file__).resolve().parents[1] / 'scripts/verify-frozen-node.py'
        spec = importlib.util.spec_from_file_location('cache_checker', source)
        self.checker = importlib.util.module_from_spec(spec)
        with patch.dict(os.environ, FERMAT_VERIFIER_PROJECT=str(self.project),
                        FERMAT_VERIFIER_REFERENCE_CACHE='', FERMAT_VERIFIER_REFERENCE_DIGEST=''):
            spec.loader.exec_module(self.checker)

    def seal(self):
        with contextlib.redirect_stdout(io.StringIO()):
            self.checker.seal_reference_cache(self.cache)
        self.checker.CACHE_ROOT = str(self.cache)
        self.checker.CACHE_DIGEST = hashlib.sha256((self.cache / 'reference.json').read_bytes()).hexdigest()

    def test_disabled_by_default(self):
        self.assertIsNone(self.checker.validate_reference_cache(contents=True))
        self.assertEqual(self.checker.compiled_packages(), self.project / '.lake/packages')

    def test_exact_controller_bound_mirror_validates(self):
        self.seal()
        self.assertEqual(self.checker.validate_reference_cache(contents=True), self.checker.CACHE_DIGEST)
        self.assertEqual(self.checker.compiled_packages(), self.cache / 'packages')

    def test_operator_environment_selects_cached_toolchain_and_packages(self):
        self.seal()
        source = Path(self.checker.__file__)
        spec = importlib.util.spec_from_file_location('configured_cache_checker', source)
        configured = importlib.util.module_from_spec(spec)
        with patch.dict(os.environ, FERMAT_VERIFIER_PROJECT=str(self.project),
                        FERMAT_VERIFIER_REFERENCE_CACHE=str(self.cache),
                        FERMAT_VERIFIER_REFERENCE_DIGEST=self.checker.CACHE_DIGEST):
            spec.loader.exec_module(configured)
        self.assertEqual(configured.LEAN, self.cache / 'lean-4.33.1-linux/bin')
        self.assertTrue(configured.ENV['PATH'].startswith(str(configured.LEAN) + ':'))
        self.assertEqual(configured.compiled_packages(), self.cache / 'packages')
        configured.validate_reference_cache(contents=True)

    def test_incomplete_operator_configuration_fails_closed(self):
        source = Path(self.checker.__file__)
        for root, digest in [(str(self.cache), ''), ('', 'a' * 64)]:
            with self.subTest(root=root, digest=digest):
                spec = importlib.util.spec_from_file_location('incomplete_cache_checker', source)
                module = importlib.util.module_from_spec(spec)
                with patch.dict(os.environ, FERMAT_VERIFIER_PROJECT=str(self.project),
                                FERMAT_VERIFIER_REFERENCE_CACHE=root,
                                FERMAT_VERIFIER_REFERENCE_DIGEST=digest):
                    with self.assertRaisesRegex(RuntimeError, 'both operator path and digest'):
                        spec.loader.exec_module(module)

    def test_manifest_self_hash_is_not_enough_without_operator_digest(self):
        self.seal()
        self.checker.CACHE_DIGEST = '0' * 64
        with self.assertRaisesRegex(RuntimeError, 'operator digest'):
            self.checker.validate_reference_cache(contents=True)

    def test_changed_added_and_removed_artifacts_are_rejected(self):
        self.seal()
        for change in ('changed', 'added', 'removed'):
            with self.subTest(change=change):
                old = self.artifact.read_bytes()
                extra = self.cache / 'packages/Extra.olean'
                if change == 'changed':
                    self.artifact.write_bytes(b'altered')
                elif change == 'added':
                    extra.write_bytes(b'extra')
                else:
                    self.artifact.unlink()
                with self.assertRaisesRegex(RuntimeError, 'artifacts changed'):
                    self.checker.validate_reference_cache(contents=True)
                self.artifact.write_bytes(old)
                if extra.exists():
                    extra.unlink()

    def test_executable_mode_change_is_rejected(self):
        self.seal()
        self.binary.chmod(0o644)
        with self.assertRaisesRegex(RuntimeError, 'artifacts changed'):
            self.checker.validate_reference_cache(contents=True)

    def test_external_symlinks_and_special_files_are_rejected(self):
        link = self.cache / 'packages/link'
        link.symlink_to(self.project)
        with self.assertRaisesRegex(RuntimeError, 'escapes'):
            self.checker.reference_inventory(self.cache)
        link.unlink()
        os.mkfifo(link)
        with self.assertRaisesRegex(RuntimeError, 'special file'):
            self.checker.reference_inventory(self.cache)

    def test_internal_symlink_is_bound_to_its_target(self):
        link = self.cache / 'packages/link'
        link.symlink_to('mathlib/Artifact.olean')
        self.seal()
        self.checker.validate_reference_cache(contents=True)
        link.unlink()
        link.symlink_to('../lean-4.33.1-linux/bin/lean')
        with self.assertRaisesRegex(RuntimeError, 'artifacts changed'):
            self.checker.validate_reference_cache(contents=True)

    def test_symlink_to_uninventoried_cache_root_file_is_rejected(self):
        unlisted = self.cache / 'unlisted.olean'
        unlisted.write_bytes(b'not inside either inventoried tree')
        (self.cache / 'packages/link').symlink_to('../unlisted.olean')
        with self.assertRaisesRegex(RuntimeError, 'inventoried'):
            self.checker.reference_inventory(self.cache)

    def test_symlink_between_inventoried_trees_is_allowed(self):
        (self.cache / 'packages/toolchain').symlink_to('../lean-4.33.1-linux')
        self.seal()
        self.checker.validate_reference_cache(contents=True)

    def test_directory_symlink_to_uninventoried_root_is_rejected(self):
        (self.cache / 'packages/root').symlink_to('..')
        with self.assertRaisesRegex(RuntimeError, 'inventoried'):
            self.checker.reference_inventory(self.cache)

    def test_manifest_symlink_and_public_cache_are_rejected(self):
        self.seal()
        manifest = self.cache / 'reference.json'
        outside = self.root / 'manifest'
        manifest.rename(outside)
        manifest.symlink_to(outside)
        with self.assertRaisesRegex(RuntimeError, 'manifest is a symlink'):
            self.checker.validate_reference_cache()
        self.cache.chmod(0o755)
        with self.assertRaisesRegex(RuntimeError, '0700'):
            self.checker.validate_reference_cache()

    def test_cache_inside_worker_area_and_resealing_are_rejected(self):
        with self.assertRaisesRegex(RuntimeError, 'outside worker'):
            self.checker.private_reference_root(self.project)
        self.seal()
        with self.assertRaises(FileExistsError):
            self.checker.seal_reference_cache(self.cache)


if __name__ == '__main__':
    unittest.main()
