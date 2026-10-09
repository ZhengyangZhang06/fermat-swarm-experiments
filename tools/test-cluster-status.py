#!/usr/bin/env python3
import importlib.util
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

spec = importlib.util.spec_from_file_location('publisher', Path(__file__).with_name('publish-cluster-status.py'))
publisher = importlib.util.module_from_spec(spec)
spec.loader.exec_module(publisher)


class ProofFeedTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        original = publisher.CAMPAIGN
        self.addCleanup(setattr, publisher, 'CAMPAIGN', original)
        publisher.CAMPAIGN = self.root
        (self.root / 'campaign.json').write_text(json.dumps({'problems': [
            dict(id='p01', theorem='Theorem', issue_url='https://github.com/o/r/issues/1')]}))
        self.project = self.root / 'project'
        self.artifacts = self.project / '.humanize/github-theorem-prover'
        self.run = self.artifacts / 'runs/one'
        self.run.mkdir(parents=True)
        self.config = dict(repository='o/r', projects=[dict(id='p01', enabled=True,
                           verification={'project': str(self.project)})])

    def dag(self, nodes):
        (self.artifacts / 'LATEST').write_text('.humanize/github-theorem-prover/runs/one')
        (self.run / 'dag.json').write_text(json.dumps({'nodes': nodes}))

    def report(self):
        return publisher.proof_records(self.config)[0]

    def test_enabled_job_is_not_a_proof(self):
        report = self.report()
        self.assertTrue(report['enabled'])
        self.assertFalse(report['root_integrated'])
        self.assertFalse(report['natural_proof_reviewed'])

    def test_merged_issue_without_proof_does_not_count(self):
        self.dag([dict(id='root', status='planning', github_pr_state='merged', github_merge_commit='abc')])
        self.assertFalse(self.report()['root_integrated'])

    def test_published_issue_state_does_not_imply_proof_acceptance(self):
        for recorded, expected in [('open', 'open'), ('closed', 'closed'),
                                   ('', 'not checked'), ('private-canary', 'not checked')]:
            with self.subTest(recorded=recorded):
                self.dag([dict(id='root', status='planning', github_issue_state=recorded)])
                report = self.report()
                self.assertEqual(report['nodes'][0]['issue_state'], expected)
                self.assertFalse(report['root_integrated'])
                self.assertFalse(report['nodes'][0]['accepted'])

    def test_verified_without_merge_does_not_count_integrated(self):
        self.dag([dict(id='root', status='proved', integrated_commit='abc')])
        self.assertTrue(self.report()['nodes'][0]['lean_verified'])
        self.assertFalse(self.report()['root_integrated'])

    def test_accepted_dependency_requires_candidate_but_does_not_imply_merge(self):
        for state, candidate, accepted in [('integrating', '', False),
                                           ('integrating', 'a' * 40, True),
                                           ('comparing', 'a' * 40, False)]:
            with self.subTest(state=state, candidate=candidate):
                self.dag([dict(id='root', status=state, candidate_commit=candidate)])
                report = self.report()
                self.assertEqual(report['nodes'][0]['accepted'], accepted)
                self.assertFalse(report['nodes'][0]['integrated'])
                self.assertFalse(report['root_integrated'])

    def test_every_retained_dependency_must_be_integrated(self):
        root = dict(id='root', status='proved', integrated_commit='abc', github_pr_state='merged',
                    github_merge_commit='def', children=['child'])
        child = dict(id='child', status='queued')
        self.dag([root, child])
        self.assertFalse(self.report()['root_integrated'])
        child.update(status='proved', integrated_commit='ghi', github_pr_state='merged', github_merge_commit='jkl')
        self.dag([root, child])
        self.assertTrue(self.report()['root_integrated'])

    def test_prose_requires_matching_consistent_review(self):
        proof = self.run / 'nodes/root/natural-proof-v1.md'
        proof.parent.mkdir(parents=True)
        proof.write_text('Proof')
        self.dag([dict(id='root', status='decomposing', natural_proof=str(proof.relative_to(self.project)))])
        self.assertFalse(self.report()['natural_proof_reviewed'])
        audit = proof.with_name('natural-audit-v1.json')
        audit.write_text(json.dumps(dict(acceptable=True, first_invalid_step='gap', required_changes=[])))
        self.assertFalse(self.report()['natural_proof_reviewed'])
        audit.write_text(json.dumps(dict(acceptable=True, first_invalid_step='', required_changes=[])))
        self.assertTrue(self.report()['natural_proof_reviewed'])

    def test_cycles_rejected_and_secrets_not_published(self):
        self.dag([dict(id='root', children=['root'], status='proved')])
        with self.assertRaises(ValueError):
            self.report()
        self.dag([dict(id='root', status='planning', worktree='/private/path', token='secret-canary',
                       github_issue_url='javascript:bad')])
        output = json.dumps(self.report())
        for forbidden in ('/private/path', 'secret-canary', 'javascript:'):
            self.assertNotIn(forbidden, output)

    def test_previous_passing_review_does_not_approve_a_revision(self):
        proof = self.run / 'nodes/root/natural-proof-v1.md'
        proof.parent.mkdir(parents=True)
        proof.write_text('Previously reviewed proof')
        proof.with_name('natural-audit-v1.json').write_text(json.dumps(
            dict(acceptable=True, first_invalid_step='', required_changes=[])))
        for stage, expected in [('natural-proof', 'revising'), ('natural-review', 'under review')]:
            with self.subTest(stage=stage):
                self.dag([dict(id='root', status=stage, natural_proof=str(proof.relative_to(self.project)))])
                report = self.report()
                self.assertFalse(report['natural_proof_reviewed'])
                self.assertEqual(report['nodes'][0]['prose_status'], expected)

    def test_root_link_retains_canonical_campaign_identity(self):
        self.dag([dict(id='root', status='decomposing', github_issue_url='https://github.com/o/r/issues/99')])
        self.assertEqual(self.report()['nodes'][0]['issue_url'], 'https://github.com/o/r/issues/1')

    def test_activity_requires_working_observation_not_prepared_stage(self):
        reports = [dict(nodes=[dict(issue_url='https://github.com/o/r/issues/1', status='decomposing'),
                              dict(issue_url='https://github.com/o/r/issues/2', status='decomposing')])]
        publisher.attach_worker_activity(reports, [dict(node='hoa3', phase='working', issue=1),
                                                  dict(node='hoa4', phase='idle', issue=2)])
        first, second = reports[0]['nodes']
        self.assertTrue(first['observed_running'])
        self.assertEqual(first['worker_node'], 'hoa3')
        self.assertFalse(second['observed_running'])
        self.assertEqual(second['worker_node'], '')


class StatusPublicationTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.worktree = self.root / 'worktree'
        self.worktree.mkdir()
        self.remote = self.root / 'remote.git'
        subprocess.run(['git', 'init', '--bare', str(self.remote)], check=True, capture_output=True)
        self.git('init', '-b', 'status-live')
        self.git('config', 'user.name', 'Status test')
        self.git('config', 'user.email', 'status@example.invalid')
        (self.worktree / 'keep.txt').write_text('original\n')
        self.git('add', 'keep.txt')
        self.git('commit', '-m', 'Initial')
        self.git('remote', 'add', 'origin', str(self.remote))
        self.git('push', 'origin', 'HEAD:status-live')
        self.content = '{"observed_at":"2026-10-08T15:40:00Z"}\n'

    def git(self, *args, remote=False):
        return subprocess.run(['git', *args], cwd=self.remote if remote else self.worktree,
                              check=True, capture_output=True, text=True).stdout.strip()

    def test_existing_index_lock_and_unrelated_staging_do_not_block_or_leak(self):
        (self.worktree / 'keep.txt').write_text('unrelated staged edit\n')
        self.git('add', 'keep.txt')
        index = self.worktree / '.git/index'
        original_index = index.read_bytes()
        lock = self.worktree / '.git/index.lock'
        lock.write_text('another index owner\n')
        publisher.publish_snapshot(self.worktree, self.content, 100)
        self.assertEqual(lock.read_text(), 'another index owner\n')
        self.assertEqual(index.read_bytes(), original_index)
        self.assertEqual(self.git('show', 'status-live:keep.txt', remote=True), 'original')
        self.assertEqual(self.git('show', 'status-live:status.json', remote=True), self.content.strip())
        self.assertEqual(self.git('show', 'status-live:ticks/101/status.json', remote=True), self.content.strip())

    def test_only_current_observation_paths_are_published(self):
        old = self.worktree / 'ticks/99/private.json'
        old.parent.mkdir(parents=True)
        old.write_text('not part of this observation')
        publisher.publish_snapshot(self.worktree, self.content, 100)
        paths = self.git('ls-tree', '-r', '--name-only', 'status-live', remote=True).splitlines()
        self.assertEqual(paths, ['keep.txt', 'status.json', 'ticks/100/status.json', 'ticks/101/status.json'])

    def test_failed_push_is_retried_without_duplicate_commit_or_new_timestamp(self):
        run = subprocess.run
        def fail_push(args, **kwargs):
            if args[3] == 'push':
                raise subprocess.CalledProcessError(128, args, stderr='private-canary')
            return run(args, **kwargs)
        with patch.object(publisher.subprocess, 'run', side_effect=fail_push):
            with self.assertRaisesRegex(RuntimeError, r'Status Git push failed \(exit 128\)') as error:
                publisher.publish_snapshot(self.worktree, self.content, 100)
        self.assertNotIn('private-canary', str(error.exception))
        pending = self.git('rev-parse', 'HEAD')
        self.assertNotEqual(self.git('rev-parse', 'status-live', remote=True), pending)
        publisher.publish_snapshot(self.worktree, self.content, 100)
        self.assertEqual(self.git('rev-parse', 'HEAD'), pending)
        self.assertEqual(self.git('rev-parse', 'status-live', remote=True), pending)
        self.assertEqual(self.git('show', 'status-live:status.json', remote=True), self.content.strip())

    def test_interrupted_private_index_does_not_poison_next_attempt(self):
        run = subprocess.run
        indexes = []
        def interrupt_add(args, **kwargs):
            if args[3] == 'add':
                index = Path(kwargs['env']['GIT_INDEX_FILE'])
                indexes.append(index)
                index.with_name('index.lock').write_text('interrupted staging')
                raise subprocess.TimeoutExpired(args, 120)
            return run(args, **kwargs)
        with patch.object(publisher.subprocess, 'run', side_effect=interrupt_add):
            with self.assertRaisesRegex(RuntimeError, 'Status Git add timed out'):
                publisher.publish_snapshot(self.worktree, self.content, 100)
        self.assertFalse(indexes[0].parent.exists())
        publisher.publish_snapshot(self.worktree, self.content, 100)
        self.assertEqual(self.git('show', 'status-live:status.json', remote=True), self.content.strip())


if __name__ == '__main__':
    unittest.main()
