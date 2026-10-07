import hashlib
import importlib.util
import io
import json
import os
from pathlib import Path
import stat
import tarfile
import tempfile
import unittest
from unittest.mock import patch


SOURCE = Path(__file__).resolve().parents[1] / 'scripts/seed-verifier-reference.py'
SPEC = importlib.util.spec_from_file_location('reference_seeder', SOURCE)
SEEDER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(SEEDER)


class ReferenceSeederTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.base = Path(temporary.name)
        self.root = self.base / 'volume'
        self.root.mkdir()
        self.archive = self.base / 'reference.tar'
        self.owner = os.getuid() or 1000
        self.files = {'packages/pkg/module.olean': (b'exact frozen bytes\x00\xff', 0o644),
                      'lean-4.33.1-linux/bin/lean': (b'pinned compiler', 0o751)}
        self.links = {'packages/pkg/alias.olean': 'module.olean'}

    def make_archive(self, *, files=None, links=None, extras=(), wrong_bytes=False, duplicate=False):
        files = self.files if files is None else files
        links = self.links if links is None else links
        entries = {name: {'sha256': hashlib.sha256(content).hexdigest(), 'mode': mode}
                   for name, (content, mode) in files.items()}
        entries.update({name: {'link': target} for name, target in links.items()})
        encoded = json.dumps({'schema': 1, 'toolchain': 'v4.33.1', 'files': entries}, sort_keys=True).encode()
        with tarfile.open(self.archive, 'w') as target:
            def regular(name, content, mode):
                member = tarfile.TarInfo(name)
                member.mode, member.size = mode, len(content)
                target.addfile(member, io.BytesIO(content))
            regular('reference.json', encoded, 0o600)
            for name in ('packages', 'packages/pkg', 'lean-4.33.1-linux', 'lean-4.33.1-linux/bin'):
                member = tarfile.TarInfo(name)
                member.type, member.mode = tarfile.DIRTYPE, 0o755
                target.addfile(member)
            for name, (content, mode) in files.items():
                regular(name, b'X' * len(content) if wrong_bytes else content, mode)
            for name, link in links.items():
                member = tarfile.TarInfo(name)
                member.type, member.linkname, member.mode = tarfile.SYMTYPE, link, 0o777
                target.addfile(member)
            if duplicate:
                name = next(iter(files))
                regular(name, *files[name])
            for member in extras:
                target.addfile(member)
        return hashlib.sha256(encoded).hexdigest(), entries

    def seed(self, digest):
        return SEEDER.seed(self.archive, self.root, digest, self.owner)

    def test_exact_inventory_modes_ownership_and_archive_digest(self):
        digest, entries = self.make_archive()
        archive_digest = hashlib.sha256(self.archive.read_bytes()).hexdigest()
        result = self.seed(digest)
        self.assertEqual(result['status'], 'seeded')
        self.assertEqual(result['archive_sha256'], archive_digest)
        self.assertEqual(result['reference_cache_digest'], digest)
        self.assertEqual(SEEDER.inventory(self.root), entries)
        self.assertEqual(stat.S_IMODE(self.root.stat().st_mode), 0o700)
        self.assertEqual(self.root.stat().st_uid, self.owner)
        self.assertEqual(self.root.stat().st_gid, self.owner)
        for name, (data, mode) in self.files.items():
            self.assertEqual((self.root / name).read_bytes(), data)
            self.assertEqual(stat.S_IMODE((self.root / name).stat().st_mode), mode)
            self.assertEqual((self.root / name).stat().st_uid, self.owner)
        self.assertEqual(os.readlink(self.root / 'packages/pkg/alias.olean'), 'module.olean')
        self.assertEqual(json.loads((self.root / SEEDER.MARKER).read_text()), result)

    def test_operator_digest_not_self_signed_manifest_is_authority(self):
        self.make_archive()
        with self.assertRaisesRegex(ValueError, 'operator digest'):
            self.seed('0' * 64)
        self.assertEqual(list(self.root.iterdir()), [])

    def test_nonempty_and_completed_volumes_never_overwritten(self):
        digest, _ = self.make_archive()
        (self.root / 'existing').write_text('preserve')
        with self.assertRaisesRegex(ValueError, 'nonempty'):
            self.seed(digest)
        self.assertEqual((self.root / 'existing').read_text(), 'preserve')
        (self.root / 'existing').unlink()
        self.seed(digest)
        with self.assertRaisesRegex(ValueError, 'nonempty'):
            self.seed(digest)

    def test_corrupt_payload_leaves_explicit_partial_volume_no_blind_retry(self):
        digest, _ = self.make_archive(wrong_bytes=True)
        with self.assertRaisesRegex(ValueError, 'file bytes'):
            self.seed(digest)
        self.assertEqual(json.loads((self.root / SEEDER.MARKER).read_text())['state'], 'incomplete')
        with self.assertRaisesRegex(ValueError, 'nonempty'):
            self.seed(digest)

    def test_traversal_absolute_special_and_hardlink_entries_rejected_before_write(self):
        for name, kind, link in (('../outside', tarfile.REGTYPE, ''), ('/absolute', tarfile.REGTYPE, ''),
                                 ('packages/../../outside', tarfile.REGTYPE, ''),
                                 ('packages/fifo', tarfile.FIFOTYPE, ''),
                                 ('packages/device', tarfile.CHRTYPE, ''),
                                 ('packages/hard', tarfile.LNKTYPE, '../outside')):
            with self.subTest(name=name):
                member = tarfile.TarInfo(name)
                member.type, member.linkname = kind, link
                digest, _ = self.make_archive(extras=[member])
                with self.assertRaises(ValueError):
                    self.seed(digest)
                self.assertEqual(list(self.root.iterdir()), [])

    def test_escaping_missing_and_cyclic_symlinks_rejected_before_write(self):
        variants = ({'packages/pkg/alias': '/etc/passwd'},
                    {'packages/pkg/alias': '../../../outside'},
                    {'packages/pkg/alias': '../../reference.json'},
                    {'packages/pkg/alias': 'missing'},
                    {'packages/pkg/a': 'b', 'packages/pkg/b': 'a'})
        for links in variants:
            with self.subTest(links=links):
                digest, _ = self.make_archive(links=links)
                with self.assertRaises(ValueError):
                    self.seed(digest)
                self.assertEqual(list(self.root.iterdir()), [])

    def test_duplicate_entries_and_writes_beneath_symlink_rejected(self):
        digest, _ = self.make_archive(duplicate=True)
        with self.assertRaisesRegex(ValueError, 'duplicate'):
            self.seed(digest)
        files = {**self.files, 'packages/alias/extra': (b'bad', 0o644)}
        digest, _ = self.make_archive(files=files, links={'packages/alias': 'pkg'})
        with self.assertRaisesRegex(ValueError, 'beneath a symlink'):
            self.seed(digest)
        self.assertEqual(list(self.root.iterdir()), [])

    def test_internal_cross_tree_relative_symlink_preserved(self):
        digest, entries = self.make_archive(links={'packages/compiler': '../lean-4.33.1-linux/bin/lean'})
        self.seed(digest)
        self.assertEqual(SEEDER.inventory(self.root), entries)

    def test_changed_second_pass_symlink_rejected_before_creation(self):
        digest, _ = self.make_archive()
        original = SEEDER.preflight
        def replace_archive(archive, expected):
            result = original(archive, expected)
            previous = self.archive.read_bytes()
            with tarfile.open(fileobj=io.BytesIO(previous), mode='r:') as source, tarfile.open(self.archive, 'w') as target:
                for member in source:
                    if member.issym():
                        member.linkname = '../../../outside'
                    target.addfile(member, source.extractfile(member) if member.isreg() else None)
            return result
        with patch.object(SEEDER, 'preflight', side_effect=replace_archive):
            with self.assertRaisesRegex(ValueError, 'headers changed'):
                self.seed(digest)
        self.assertFalse((self.root / 'packages/pkg/alias.olean').exists())
        self.assertFalse((self.base / 'outside').exists())

    def test_unsafe_root_and_invalid_owner_rejected(self):
        digest, _ = self.make_archive()
        link = self.base / 'linked-volume'
        link.symlink_to(self.root, target_is_directory=True)
        for root, owner in ((Path('/'), self.owner), (Path('relative'), self.owner),
                            (link, self.owner), (self.root, 0), (self.root, -1)):
            with self.subTest(root=root, owner=owner), self.assertRaises(ValueError):
                SEEDER.seed(self.archive, root, digest, owner)

    def test_retained_exclusive_receipt_prevents_concurrent_second_claim(self):
        digest, _ = self.make_archive()
        original = SEEDER.preflight
        once = False
        def competing_seed(archive, expected):
            nonlocal once
            result = original(archive, expected)
            if not once:
                once = True
                self.seed(digest)
            return result
        with patch.object(SEEDER, 'preflight', side_effect=competing_seed):
            with self.assertRaises(FileExistsError):
                self.seed(digest)
        self.assertEqual(json.loads((self.root / SEEDER.MARKER).read_text())['status'], 'seeded')


if __name__ == '__main__':
    unittest.main()
