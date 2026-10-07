"""Interrupted reviewed splits recover publication, never restart mathematical work."""
import json
import os
from pathlib import Path
import tempfile
import threading
from types import SimpleNamespace
import unittest
from unittest.mock import Mock, patch

from _recursive_lean.github import PublicationError
from _recursive_lean.github_runtime import GitHubTheoremRuntime
from _recursive_lean.issue_workers import ChildrenQueued, IssueWorkerPool
from _recursive_lean.models import Decomposition, DecompositionAudit, NodeRecord
from _recursive_lean.parallel import PROTOCOL, child_publication_checkpoint
from _recursive_lean.store import Store, slug
from _recursive_lean.swarm_broker import Broker


class PublicationRecoveryTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.project = Path(self.temporary.name)
        self.run = self.project / '.humanize/github-theorem-prover/runs/test'
        self.store = Store(self.run, self.project / 'wiki', 'Recovery fixture')
        self.runtime = runtime = GitHubTheoremRuntime.__new__(GitHubTheoremRuntime)
        runtime.project, runtime.run_root, runtime.store = self.project, self.run, self.store
        runtime.config = SimpleNamespace(github_shared_issue_runtime=True, github_worker_mode='poll',
            github_repository='example/proofs', github_selected_issue=1, github_root_issue_number=1,
            github_issue_workers=1, github_issue_poll_interval=0.01)
        runtime._graph_lock = threading.RLock()
        runtime._publication_lock = threading.RLock()
        runtime._publication_abort = None
        runtime._accepted_checkpoint = lambda n: n.status == 'proved'
        runtime._accepted_decomposition_audits = {}
        self.parent = self.store.ensure('root', parent=None, depth=0, title='Root', statement='True proposition')
        self.parent.github_issue_url = 'https://github.com/example/proofs/issues/1'
        references = [dict(source='local-project', queries=['True'], files=['Challenge.lean'], conclusion='Exact fixture')]
        self.decomposition = Decomposition.model_validate(dict(reference_use=references, should_split=True,
            rationale='Independent fixture children', subproblems=[dict(key=key, title=f'Child {key}',
                statement='The true proposition holds.', lean_statement='True', lean_name=f'child_{key}',
                depends_on=[], natural_proof='Apply the introduction constructor for the true proposition.',
                proof_key_steps=['Use True.intro.']) for key in ('left', 'right')]))
        self.audit = DecompositionAudit.model_validate(dict(reference_use=references, acceptable=True,
            nodes=[dict(key=key, acceptable=True, natural_proof_acceptable=True, reason='Exact constructor proof')
                   for key in ('left', 'right')], required_changes=[]))
        self.children = []
        for subproblem, audit in zip(self.decomposition.subproblems, self.audit.nodes):
            child = self.store.ensure(f'root.{subproblem.key}-a1', parent='root', depth=1,
                title=subproblem.title, statement=subproblem.statement, lean_name=subproblem.lean_name,
                lean_statement=subproblem.lean_statement, depends_on=[])
            runtime._install_parent_supplied_child_handoff(self.parent, child, subproblem, audit,
                                                         self.decomposition.reference_use, [])
            self.children.append(child)
        self.parent.children = [child.id for child in self.children]
        self.store.render()
        self.node_dir = runtime._node_dir(self.parent)
        (self.node_dir / 'decomposition-v1.json').write_text(self.decomposition.model_dump_json())
        (self.node_dir / 'decomposition-audit-v1.json').write_text(self.audit.model_dump_json())
        (self.run.parent.parent / 'LATEST').write_text(str(self.run.relative_to(self.project)))
        self.catalog = dict(root_issue=1, verification={'project': str(self.project)},
                            issue_runtime_protocol=PROTOCOL)
        self.syncs = []
        def sync(nodes):
            self.syncs.append([node.id for node in nodes])
            for node in nodes:
                if not node.github_issue_url:
                    node.github_issue_url = f'https://github.com/example/proofs/issues/{2 + self.children.index(node)}'
            self.store.render()
        runtime._sync_issues = Mock(side_effect=sync)
        runtime._github_workspace_remote = Mock(return_value='origin')
        runtime._workspace_dispatch_branch = Mock(return_value='handoff/root')
        runtime._workspace_payload = Mock(return_value=(Path('bundle'), Path('bundle/workspace.json'), {}, []))
        self.dispatch = SimpleNamespace(children=[SimpleNamespace(node_id=child.id,
            bundle_path=f'bundle/{slug(child.id)}', result_branch=f'proof/{slug(child.id)}') for child in self.children])
        runtime._publish_workspace_branch = Mock(return_value=('a' * 40, self.dispatch))
        runtime._solve = Mock(side_effect=AssertionError('must not solve'))
        runtime._formalize_checkpoint_parent = Mock(side_effect=AssertionError('must not formalize'))
        runtime._adopt_issue_work = Mock(side_effect=AssertionError('must not adopt'))
        self.environment = patch.dict(os.environ, HUMANIZE_SWARM_ATTEMPT='recovery-fixture')
        self.environment.start()
        self.addCleanup(self.environment.stop)

    def test_parent_is_available_only_for_exact_reviewed_publication_recovery(self):
        self.assertEqual(Broker.project_issues(self.catalog, 'example/proofs'), [1])
        self.assertTrue(IssueWorkerPool(self.runtime).eligible(self.parent))
        self.assertFalse(IssueWorkerPool(self.runtime).eligible(self.children[0]))
        self.catalog.pop('issue_runtime_protocol')
        self.assertEqual(Broker.project_issues(self.catalog, 'example/proofs'), [])

    def test_missing_audit_fails_closed_before_any_publication(self):
        (self.node_dir / 'decomposition-audit-v1.json').unlink()
        self.assertEqual(Broker.project_issues(self.catalog, 'example/proofs'), [])
        self.assertFalse(IssueWorkerPool(self.runtime).eligible(self.parent))
        with self.assertRaises(PublicationError):
            self.runtime._recover_decomposition_publication(self.parent)
        self.runtime._sync_issues.assert_not_called()
        self.runtime._publish_workspace_branch.assert_not_called()

    def test_mismatched_child_contract_and_handoff_fail_closed(self):
        self.children[0].lean_statement = 'False'
        self.store.render()
        self.assertEqual(Broker.project_issues(self.catalog, 'example/proofs'), [])
        with self.assertRaises(PublicationError):
            self.runtime._recover_decomposition_publication(self.parent)
        self.runtime._sync_issues.assert_not_called()

    def test_wrong_audit_version_cannot_authorize_split(self):
        (self.node_dir / 'decomposition-audit-v1.json').rename(self.node_dir / 'decomposition-audit-v2.json')
        with self.assertRaises(ValueError):
            child_publication_checkpoint(self.project, self.run, self.parent, self.store.nodes)

    def test_child_identity_must_match_frozen_handoff(self):
        old = self.children[0]
        replacement = old.model_copy(update={'id': 'root.replacement-a1'})
        self.store.nodes[replacement.id] = replacement
        self.parent.children[0] = replacement.id
        self.store.render()
        self.assertEqual(Broker.project_issues(self.catalog, 'example/proofs'), [])
        with self.assertRaises(PublicationError):
            self.runtime._recover_decomposition_publication(self.parent)
        self.runtime._sync_issues.assert_not_called()

    def test_failed_independent_audit_cannot_authorize_split(self):
        audit = self.audit.model_dump()
        audit['nodes'][0]['natural_proof_acceptable'] = False
        (self.node_dir / 'decomposition-audit-v1.json').write_text(json.dumps(audit))
        self.assertEqual(Broker.project_issues(self.catalog, 'example/proofs'), [])
        self.assertFalse(IssueWorkerPool(self.runtime).eligible(self.parent))

    def test_published_children_leave_parent_blocked_until_proved(self):
        with self.assertRaises(ChildrenQueued):
            self.runtime._recover_decomposition_publication(self.parent)
        self.assertFalse(IssueWorkerPool(self.runtime).eligible(self.parent))
        self.assertEqual(Broker.project_issues(self.catalog, 'example/proofs'), [2, 3])

    def test_modified_proof_file_cannot_recover_even_with_matching_models(self):
        (self.project / self.children[0].natural_proof).write_text('Unreviewed replacement proof')
        with self.assertRaises(PublicationError):
            self.runtime._recover_decomposition_publication(self.parent)
        self.runtime._sync_issues.assert_not_called()

    def test_recovery_publishes_children_and_yields_without_any_proof_stage(self):
        handoffs = [(self.project / child.parent_handoff).read_bytes() for child in self.children]
        with self.assertRaises(ChildrenQueued):
            self.runtime._recover_decomposition_publication(self.parent)
        self.assertEqual(self.parent.status, 'waiting-children')
        self.assertEqual(Broker.project_issues(self.catalog, 'example/proofs'), [2, 3])
        self.assertEqual([child.workspace_handoff_commit for child in self.children], ['a' * 40] * 2)
        self.assertEqual(handoffs, [(self.project / child.parent_handoff).read_bytes() for child in self.children])
        self.runtime._solve.assert_not_called()
        self.runtime._formalize_checkpoint_parent.assert_not_called()
        self.runtime._adopt_issue_work.assert_not_called()

    def test_existing_active_sibling_is_not_rebased_or_republished(self):
        active = self.children[0]
        active.github_issue_url = 'https://github.com/example/proofs/issues/2'
        active.workspace_remote = 'origin'
        active.workspace_manifest_path = 'bundle/workspace.json'
        active.workspace_bundle_path = self.dispatch.children[0].bundle_path
        active.workspace_handoff_branch = 'handoff/root'
        active.workspace_handoff_commit = 'a' * 40
        active.workspace_result_branch = self.dispatch.children[0].result_branch
        active.proof_branch = 'ongoing-proof'
        active.proof_base_commit = 'b' * 40
        active.worktree = '/fixture/active-worktree'
        active.status = 'rlcr-lean'
        before = active.model_dump()
        with self.assertRaises(ChildrenQueued):
            self.runtime._recover_decomposition_publication(self.parent)
        self.assertEqual(active.model_dump(), before)
        self.assertNotIn(active.id, [key for call in self.syncs for key in call])

    def test_wrong_selected_issue_cannot_recover_parent(self):
        self.runtime.config.github_selected_issue = 2
        self.assertFalse(IssueWorkerPool(self.runtime).eligible(self.parent))
        with self.assertRaises(RuntimeError):
            self.runtime._recover_decomposition_publication(self.parent)
        self.runtime._sync_issues.assert_not_called()

    def test_actual_poller_routes_recovery_before_adoption_or_formalization(self):
        runtime = self.runtime
        runtime._marker = lambda node, kind: f'<!-- {node.id} -->'
        issue = dict(number=1, html_url=self.parent.github_issue_url, state='open', body='<!-- root -->')
        runtime.github = SimpleNamespace(request=lambda method, resource, **kwargs:
                                        [issue] if '?' in resource else issue)
        pool = IssueWorkerPool(runtime)
        self.assertTrue(pool.poll_once('recovery-fixture'))
        self.assertEqual(pool.records['recovery-fixture']['state'], 'children-published')
        runtime._adopt_issue_work.assert_not_called()
        runtime._formalize_checkpoint_parent.assert_not_called()


if __name__ == '__main__':
    unittest.main()
