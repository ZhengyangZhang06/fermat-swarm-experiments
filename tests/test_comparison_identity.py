import copy
from pathlib import Path
import subprocess
import tempfile
import unittest

from _recursive_lean.comparison_identity import capture, verify


class ComparisonIdentityTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.git("init", "-b", "main")
        self.git("config", "user.name", "Fixture")
        self.git("config", "user.email", "fixture@example.invalid")
        (self.root / ".gitignore").write_text(".humanize/\n.lake/\nIgnored.lean\n")
        (self.root / "Challenge.lean").write_text("theorem fixed : True := by sorry\n")
        (self.root / "Submission.lean").write_text("theorem fixed : True := by trivial\n")
        self.git("add", ".")
        self.git("commit", "-m", "original")
        self.source = self.git("rev-parse", "HEAD")
        self.paths = ["Submission.lean", "Challenge.lean"]

    def git(self, *args):
        return subprocess.run(["git", "-C", str(self.root), *args], capture_output=True, text=True, check=True).stdout.strip()

    def snapshot(self, **kwargs):
        return capture(self.root, self.paths, **kwargs)

    def test_exact_bytes_blobs_and_caller_metadata(self):
        metadata = {"repository": "owner/repo", "issue": 4, "node": {"name": "fixed", "type": "True"}, "source_commit": self.source, "handoff_sha256": "a" * 64}
        before = self.snapshot(metadata=metadata, frozen_contract_path="Challenge.lean", source_commit=self.source)
        self.assertEqual(before["inputs"]["Submission.lean"]["git_blob"], self.git("rev-parse", "HEAD:Submission.lean"))
        self.assertEqual(before["inputs"]["Submission.lean"]["bytes"], len((self.root / "Submission.lean").read_bytes()))
        self.assertEqual(before["metadata"], metadata)
        metadata["node"]["type"] = "False"
        self.assertEqual(before["metadata"]["node"]["type"], "True")
        verify(self.root, before)

    def test_dirty_or_deleted_tracked_file_rejected(self):
        before = self.snapshot()
        (self.root / "Submission.lean").write_text("changed\n")
        with self.assertRaises(ValueError):
            verify(self.root, before)
        (self.root / "Submission.lean").unlink()
        with self.assertRaises(ValueError):
            self.snapshot()

    def test_dirty_unrelated_tracked_file_rejected(self):
        (self.root / ".gitignore").write_text("changed\n")
        with self.assertRaisesRegex(ValueError, "tracked"):
            self.snapshot()

    def test_untracked_participant_rejected_runtime_evidence_allowed(self):
        (self.root / ".humanize").mkdir()
        (self.root / ".humanize/proof.lean").write_text("runtime evidence")
        before = self.snapshot()
        verify(self.root, before)
        (self.root / "Helper.lean").write_text("theorem bad : False := by sorry")
        with self.assertRaisesRegex(ValueError, "untracked"):
            self.snapshot()

    def test_untracked_or_ignored_configured_input_rejected(self):
        for name in ("New.lean", "Ignored.lean"):
            (self.root / name).write_text("proof")
            with self.assertRaises(ValueError):
                capture(self.root, [name])
            (self.root / name).unlink()

    def test_new_commit_same_tree_and_changed_input_commit_rejected(self):
        before = self.snapshot()
        self.git("commit", "--allow-empty", "-m", "new history")
        with self.assertRaisesRegex(ValueError, "identity changed"):
            verify(self.root, before)
        before = self.snapshot()
        (self.root / "Submission.lean").write_text("theorem fixed : True := True.intro\n")
        self.git("add", "Submission.lean")
        self.git("commit", "-m", "different proof")
        with self.assertRaisesRegex(ValueError, "identity changed"):
            verify(self.root, before)

    def test_replacement_history_rejected_with_same_head(self):
        self.git("commit", "--allow-empty", "-m", "second")
        before = self.snapshot()
        head = self.git("rev-parse", "HEAD")
        self.git("replace", "--graft", "HEAD")
        self.assertEqual(self.git("rev-parse", "HEAD"), head)
        with self.assertRaisesRegex(ValueError, "replacement"):
            verify(self.root, before)

    def test_frozen_contract_unchanged_while_proof_may_change(self):
        (self.root / "Submission.lean").write_text("theorem fixed : True := True.intro\n")
        self.git("add", "Submission.lean")
        self.git("commit", "-m", "proof")
        before = self.snapshot(frozen_contract_path="Challenge.lean", source_commit=self.source)
        verify(self.root, before)
        (self.root / "Challenge.lean").write_text("theorem fixed : False := by sorry\n")
        self.git("add", "Challenge.lean")
        self.git("commit", "-m", "weaken contract")
        with self.assertRaisesRegex(ValueError, "original contract"):
            self.snapshot(frozen_contract_path="Challenge.lean", source_commit=self.source)

    def test_paths_and_symlinks_fail_closed(self):
        for path in ("", ".", "../Submission.lean", "/etc/passwd", "a/../Submission.lean", "a//b", "a\\b", ".git/config"):
            with self.subTest(path=path), self.assertRaises(ValueError):
                capture(self.root, [path])
        (self.root / "Link.lean").symlink_to("Submission.lean")
        self.git("add", "Link.lean")
        self.git("commit", "-m", "link")
        with self.assertRaises(ValueError):
            capture(self.root, ["Link.lean"])

    def test_live_input_checked_even_when_assume_unchanged(self):
        self.git("update-index", "--assume-unchanged", "Submission.lean")
        (self.root / "Submission.lean").write_text("hidden tracked edit")
        with self.assertRaises(ValueError):
            self.snapshot()

    def test_hidden_dirty_noninput_index_flags_rejected(self):
        self.git("update-index", "--skip-worktree", ".gitignore")
        (self.root / ".gitignore").write_text("hidden change\n")
        with self.assertRaisesRegex(ValueError, "index hides"):
            self.snapshot()

    def test_serialized_identity_tampering_rejected(self):
        before = self.snapshot()
        changed = copy.deepcopy(before)
        changed["inputs"]["Submission.lean"]["sha256"] = "0" * 64
        with self.assertRaises(ValueError):
            verify(self.root, changed)
        with self.assertRaises(ValueError):
            verify(self.root, {})

    def test_contract_options_require_exact_commit(self):
        for options in ({"frozen_contract_path": "Challenge.lean"}, {"source_commit": self.source}, {"frozen_contract_path": "Challenge.lean", "source_commit": "main"}):
            with self.subTest(options=options), self.assertRaises(ValueError):
                self.snapshot(**options)


if __name__ == "__main__":
    unittest.main()
