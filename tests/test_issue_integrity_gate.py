"""Exact issue/candidate gates fail closed without changing proof workspaces."""
import json
from pathlib import Path
import subprocess
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import Mock, patch

from _recursive_lean.github_runtime import GitHubTheoremRuntime
from _recursive_lean.models import NodeRecord
from _recursive_lean.runtime import Runtime
from _recursive_lean.swarm_broker import Broker
from _recursive_lean.distributed_claims import ClaimLedger
from _recursive_lean.parallel import PROTOCOL


def git(root, *args):
    return subprocess.check_output(['git', '-C', str(root), *args], text=True,
                                   stderr=subprocess.DEVNULL).strip()


class IssueIntegrityTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        git(self.root, 'init', '-q')
        git(self.root, 'config', 'user.name', 'Fixture')
        git(self.root, 'config', 'user.email', 'fixture@example.invalid')
        (self.root / '.gitignore').write_text('.humanize/\n')
        self.contract = 'theorem original : True\n'
        (self.root / 'Challenge.lean').write_text(self.contract)
        (self.root / 'Submission.lean').write_text('theorem original : True := by trivial\n')
        git(self.root, 'add', '.')
        git(self.root, 'commit', '-qm', 'Frozen fixture')
        self.before = git(self.root, 'rev-parse', 'HEAD')
        (self.root / 'Submission.lean').write_text('theorem original : True := by exact True.intro\n')
        git(self.root, 'commit', '-qam', 'Candidate fixture')
        self.after = git(self.root, 'rev-parse', 'HEAD')
        self.run = self.root / '.humanize/run'
        self.run.mkdir(parents=True)
        self.runtime = runtime = GitHubTheoremRuntime.__new__(GitHubTheoremRuntime)
        runtime.project, runtime.run_root = self.root, self.run
        runtime.config = SimpleNamespace(github_repository='owner/repo',
            github_contract_file='Challenge.lean', github_root_lean_statement='True',
            github_root_lean_name='original', github_selected_issue=1,
            github_root_issue_number=1, comparator_command='checker Submission.lean',
            comparator_success='VERIFIED', huggingface_token_env='HF_TOKEN',
            wiki_dir='wiki', lean_target='Submission.lean')
        runtime.publication_context = dict(source_commit=self.before, contract=self.contract,
            root_lean_name='original', root_lean_statement='True', contract_file='Challenge.lean',
            repository='owner/repo', comparator_command='checker Submission.lean',
            comparator_success='VERIFIED')
        (self.run / 'github-workflow.json').write_text(json.dumps(runtime.publication_context))
        self.node = NodeRecord(id='root', title='Original', statement='True holds',
            lean_name='original', lean_statement='True', proof_base_commit=self.before,
            github_issue_url='https://github.com/owner/repo/issues/1')
        runtime._git_blob = lambda commit, path: subprocess.check_output(
            ['git', '-C', str(self.root), 'show', f'{commit}:{path}'], text=True)
        runtime._node_dir = Mock(return_value=self.run)
        runtime._next_json_version = Mock(return_value=1)
        runtime._review_command = lambda node, files: runtime.config.comparator_command
        self.save_node()

    def save_node(self):
        (self.run / 'dag.json').write_text(json.dumps({'nodes': [self.node.model_dump(mode='json')]}))

    def capture(self):
        return self.runtime._capture_comparison_identity(self.node, self.root, self.before,
                                                         ['Submission.lean'])

    def problem(self, identity, digest=None):
        audit = SimpleNamespace(comparison_identity=identity['digest'] if digest is None else digest)
        return self.runtime._comparison_identity_problem(self.node, self.root, self.after,
                                                          identity, audit)

    def test_unchanged_exact_packet_passes_and_wrong_review_digest_rejects(self):
        identity = self.capture()
        self.assertEqual(self.problem(identity), '')
        self.assertIn('identity', self.problem(identity, 'different-packet'))

    def test_selected_durable_dag_contract_change_rejects(self):
        identity = self.capture()
        payload = json.loads((self.run / 'dag.json').read_text())
        payload['nodes'][0]['lean_statement'] = 'False'
        (self.run / 'dag.json').write_text(json.dumps(payload))
        self.assertIn('DAG input', self.problem(identity))

    def test_frozen_workflow_context_change_rejects(self):
        identity = self.capture()
        context = dict(self.runtime.publication_context, root_lean_name='other')
        (self.run / 'github-workflow.json').write_text(json.dumps(context))
        self.assertIn('workflow context changed', self.problem(identity))

    def test_old_review_digest_cannot_approve_a_new_clean_candidate(self):
        old = self.capture()
        (self.root / 'Submission.lean').write_text('theorem original : True := True.intro\n')
        git(self.root, 'commit', '-qam', 'Another candidate')
        self.after = git(self.root, 'rev-parse', 'HEAD')
        current = self.capture()
        self.assertNotEqual(old['digest'], current['digest'])
        self.assertIn('attest', self.problem(current, old['digest']))

    def root_with_child(self):
        self.node.children = ['root.child']
        self.save_node()
        payload = json.loads((self.run / 'dag.json').read_text())
        payload['nodes'].append(NodeRecord(id='root.child', parent='root', title='Child',
            statement='True holds', lean_name='child', lean_statement='True', status='proved',
            proof_base_commit=self.before, github_issue_url='https://github.com/owner/repo/issues/2'
        ).model_dump(mode='json'))
        (self.run / 'dag.json').write_text(json.dumps(payload))
        return payload

    def test_root_comparator_dependency_contract_cannot_be_removed(self):
        payload = self.root_with_child()
        identity = self.capture()
        payload['nodes'][0]['children'] = []
        (self.run / 'dag.json').write_text(json.dumps(payload))
        self.assertTrue(self.problem(identity))

    def test_root_comparator_dependency_type_cannot_change(self):
        payload = self.root_with_child()
        identity = self.capture()
        payload['nodes'][1]['lean_statement'] = 'False'
        (self.run / 'dag.json').write_text(json.dumps(payload))
        self.assertTrue(self.problem(identity))

    def test_dependency_activity_updates_do_not_invalidate_identity(self):
        payload = self.root_with_child()
        identity = self.capture()
        payload['nodes'][1].update(status='integrating', message='Remote publication in progress')
        (self.run / 'dag.json').write_text(json.dumps(payload))
        self.assertEqual(self.problem(identity), '')

    def test_changed_comparator_command_or_marker_rejects(self):
        identity = self.capture()
        for key in ('comparator_command', 'comparator_success'):
            with self.subTest(key=key):
                original = getattr(self.runtime.config, key)
                setattr(self.runtime.config, key, 'SUBSTITUTED')
                self.assertTrue(self.problem(identity))
                setattr(self.runtime.config, key, original)

    def test_changing_both_memory_and_dag_base_rejects(self):
        identity = self.capture()
        self.node.proof_base_commit = self.after
        self.save_node()
        self.assertTrue(self.problem(identity))

    def test_wrong_root_declaration_or_selected_issue_rejects_at_capture(self):
        for key, value in [('lean_name', 'different'), ('lean_statement', 'False'),
                           ('github_issue_url', 'https://github.com/owner/repo/issues/99')]:
            with self.subTest(key=key):
                original = getattr(self.node, key)
                setattr(self.node, key, value)
                self.save_node()
                with self.assertRaises((ValueError, RuntimeError)):
                    self.capture()
                setattr(self.node, key, original)
                self.save_node()

    def test_child_statement_must_match_immutable_dispatch(self):
        self.node.parent = 'parent'
        self.node.workspace_handoff_commit = self.before
        self.node.workspace_manifest_path = 'bundle/workspace.json'
        self.save_node()
        self.runtime._parent_supplied_child_checkpoint = Mock(return_value=object())
        handoff = SimpleNamespace(child_id='root', parent_id='parent',
            subproblem=SimpleNamespace(lean_statement='False', lean_name=self.node.lean_name),
            resolved_dependencies=[])
        self.runtime._load_workspace_dispatch = Mock(return_value=SimpleNamespace(
            children=[SimpleNamespace(node_id='root', handoff=handoff)]))
        with self.assertRaisesRegex(ValueError, 'immutable child dispatch'):
            self.capture()

    def finish_runtime(self):
        runtime = Runtime.__new__(Runtime)
        runtime.project = self.root
        runtime.config = SimpleNamespace(comparator_success='VERIFIED')
        runtime.store = Mock()
        runtime.agents = SimpleNamespace(reviewer=Mock())
        runtime._lean_files = Mock(return_value=['Submission.lean'])
        runtime._compare = Mock(return_value=(True, self.run / 'comparator.log', 'VERIFIED'))
        runtime._node_dir = Mock(return_value=self.run)
        runtime._next_json_version = Mock(return_value=1)
        runtime._problem_context = Mock(return_value='')
        runtime._reference_context = Mock(return_value='')
        runtime._review_command = Mock(return_value='checker Submission.lean')
        runtime._reference_use_problem = Mock(return_value='')
        runtime._theorem_publication_problem = Mock(return_value='')
        runtime._reject_lean_audit = Mock(return_value=SimpleNamespace(ok=False))
        runtime._push_child_workspace_result = Mock(side_effect=AssertionError('must not publish mutation'))
        return runtime

    def test_comparator_mutation_rejects_before_reviewer(self):
        runtime = self.finish_runtime()
        def compare(*args):
            (self.root / 'Submission.lean').write_text('-- changed during comparison\n')
            return True, self.run / 'comparator.log', 'VERIFIED'
        runtime._compare.side_effect = compare
        with patch('_recursive_lean.runtime._structured_turn') as reviewer:
            result = runtime._finish_rlcr_candidate(self.node, self.root, self.before)
        self.assertFalse(result.ok)
        reviewer.assert_not_called()
        runtime._push_child_workspace_result.assert_not_called()

    def test_reviewer_clean_commit_mutation_rejects_old_candidate_acceptance(self):
        runtime = self.finish_runtime()
        audit = Mock(passed=True, theorems=[])
        audit.model_dump_json.return_value = '{}'
        def review(*args):
            (self.root / 'Submission.lean').write_text('-- review changed candidate\n')
            git(self.root, 'commit', '-qam', 'Reviewer mutation')
            return audit
        with patch('_recursive_lean.runtime._structured_turn', side_effect=review):
            result = runtime._finish_rlcr_candidate(self.node, self.root, self.before)
        self.assertFalse(result.ok)
        self.assertNotEqual(git(self.root, 'rev-parse', 'HEAD'), self.after)
        self.assertEqual(git(self.root, 'status', '--porcelain'), '')
        runtime._push_child_workspace_result.assert_not_called()


class CatalogCommandSwitchTests(unittest.TestCase):
    def test_existing_attempt_retains_old_runner_new_attempt_gets_new_runner(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            path = root / 'catalog.json'
            config = dict(repository='owner/repo', projects=[dict(id='p', root_issue=1,
                issue_numbers=[1, 2], issue_runtime_protocol=PROTOCOL, enabled=True,
                cwd='/trusted/project', command=['/immutable/v3/runner'], environment={},
                log_directory='/private/logs')])
            path.write_text(json.dumps(config))
            broker = Broker(path, ClaimLedger(root / 'claims.sqlite'), 'fixture-token-' * 4,
                            root / 'snapshot.json', 'gh')
            broker.github = Mock(return_value={'state': 'open'})
            first = dict(node='hoa0', task='task00000', boot='boot00000', project='p',
                         issue=1, attempt='attempt0000')
            old = broker.claim(first)
            config['projects'][0]['command'] = ['/immutable/v4/runner']
            path.write_text(json.dumps(config))
            self.assertEqual(broker.claim(first), old)
            second = broker.claim(dict(first, node='hoa1', issue=2, attempt='attempt0001'))
            self.assertEqual(second['job']['command'], ['/immutable/v4/runner'])
            self.assertEqual(old['job']['command'], ['/immutable/v3/runner'])


if __name__ == '__main__':
    unittest.main()
