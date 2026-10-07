"""Reusable lifecycle profiles retain policy without granting new authority."""
from pathlib import Path
import unittest

import yaml

from __init__ import GitHubTheoremConfig


class WorkflowProfileTests(unittest.TestCase):
    def profile(self, name):
        path = Path(__file__).resolve().parents[1] / name
        return GitHubTheoremConfig.model_validate(yaml.safe_load(path.read_text()))

    def test_authorized_profile_retains_polling_publication_merge_and_close(self):
        profile = self.profile('config.github-theorems.authorized.example.yaml')
        self.assertTrue(profile.local_problem)
        self.assertTrue(profile.github_auto_merge)
        self.assertTrue(profile.github_close_proved_issues)
        self.assertTrue(profile.github_status_publish)
        self.assertEqual(profile.github_worker_mode, 'poll')
        self.assertEqual(profile.github_issue_workers, 8)
        self.assertNotEqual(profile.github_status_branch, profile.github_base_branch)
        self.assertTrue(profile.comparator_command)
        resumed = GitHubTheoremConfig.model_validate_json(profile.model_dump_json())
        self.assertEqual(resumed, profile)

    def test_generic_profile_does_not_infer_merge_authority(self):
        profile = self.profile('config.github-theorems.example.yaml')
        self.assertFalse(profile.github_auto_merge)
        self.assertFalse(profile.github_close_proved_issues)
        self.assertTrue(profile.github_status_publish)
        self.assertEqual(profile.github_worker_mode, 'poll')


if __name__ == '__main__':
    unittest.main()
