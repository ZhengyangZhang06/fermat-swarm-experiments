"""Exercise actual shared runtime construction/polling in separate processes."""
import json
import multiprocessing
import os
from pathlib import Path
import subprocess
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import Mock, patch

from __init__ import GitHubTheoremConfig
from _recursive_lean.github_runtime import GitHubTheoremRuntime
from _recursive_lean.issue_workers import IssueWorkerPool
from _recursive_lean.models import SolveResult
from _recursive_lean.models import NodeRecord
from _recursive_lean.runtime import Runtime
from _recursive_lean.shared_lock import SharedLock
from _recursive_lean.parallel import PROTOCOL
from _recursive_lean.store import Store


def configuration(issue):
    return GitHubTheoremConfig(github_repository='example/proofs', github_root_lean_name='Submission.root',
        github_root_lean_statement='True', github_root_issue_number=1, github_poll_once=True,
        github_issue_workers=1, github_selected_issue=issue, github_shared_issue_runtime=True,
        local_problem=True, github_status_publish=False)


def run_leaf(project, run, issue, barrier):
    os.chdir(project)
    os.environ.update(HUMANIZE_SWARM_PROTOCOL=PROTOCOL, HUMANIZE_SWARM_ATTEMPT=f'attempt-{issue}',
                      HUMANIZE_SWARM_CLAIM_TOKEN='test-only')
    runtime = GitHubTheoremRuntime(None, 'Parallel fixture', configuration(issue), {'run_dir': run})
    try:
        runtime._marker = lambda node, kind: f'<!-- {node.id} -->'
        issues = [{'number': i, 'html_url': f'https://github.com/example/proofs/issues/{i}',
                   'state': 'open', 'body': f'<!-- leaf-{i} -->'} for i in (2, 3)]
        runtime.github = SimpleNamespace(request=lambda method, resource, **kw:
            issues if '?' in resource else next(r for r in issues if str(r['number']) == resource.split('/')[-1]))
        def solve(node):
            runtime.store.update(node.id, 'decomposing', f'process-{issue}-active')
            barrier.wait(timeout=20)  # Both distinct leaf proofs must overlap.
            runtime.store.update(node.id, 'failed', f'fixture-{issue}-finished; not a proof')
            return SolveResult(ok=False, node_id=node.id, feedback='test-only worker')
        runtime._solve = solve
        with runtime._execution_guard():
            IssueWorkerPool(runtime).run(runtime.store.nodes['root'])
    finally:
        runtime._integration_executor.shutdown()
        runtime._speculation_executor.shutdown()


class SharedRuntimeTests(unittest.TestCase):
    def test_two_actual_runtimes_overlap_on_independent_leaves(self):
        with tempfile.TemporaryDirectory() as directory:
            project = Path(directory)
            subprocess.run(['git', 'init', '-q', str(project)], check=True)
            (project / 'Challenge.lean').write_text('theorem root : True := by sorry\n')
            subprocess.run(['git', '-C', directory, 'add', 'Challenge.lean'], check=True)
            subprocess.run(['git', '-C', directory, '-c', 'user.name=Test', '-c', 'user.email=test@example.invalid',
                            'commit', '-qm', 'fixture'], check=True)
            old = Path.cwd()
            try:
                os.chdir(project)
                with patch.dict(os.environ, HUMANIZE_SWARM_PROTOCOL=PROTOCOL,
                                HUMANIZE_SWARM_ATTEMPT='seed', HUMANIZE_SWARM_CLAIM_TOKEN='test-only'):
                    runtime = GitHubTheoremRuntime(None, 'Parallel fixture', configuration(2), {})
                root = runtime.store.ensure('root', parent=None, depth=0, title='Root', statement='True')
                root.github_issue_url = 'https://github.com/example/proofs/issues/1'
                for i in (2, 3):
                    node = runtime.store.ensure(f'leaf-{i}', parent='root', depth=1, title=f'Leaf {i}',
                                                statement='True', lean_name=f'leaf{i}')
                    node.github_issue_url = f'https://github.com/example/proofs/issues/{i}'
                    node.workspace_handoff_commit = 'test-handoff'
                    node.workspace_bundle_path = 'test-bundle'
                    node.parent_handoff = 'test-handoff-record'
                runtime.store.render()
                root_before = root.model_dump()
                run = str(runtime.run_root.relative_to(project))
                runtime._integration_executor.shutdown()
                runtime._speculation_executor.shutdown()
            finally:
                os.chdir(old)
            ctx = multiprocessing.get_context('spawn')
            barrier = ctx.Barrier(2)
            jobs = [ctx.Process(target=run_leaf, args=(directory, run, i, barrier)) for i in (2, 3)]
            try:
                for job in jobs:
                    job.start()
                for job in jobs:
                    job.join(30)
                    self.assertEqual(job.exitcode, 0)
            finally:
                for job in jobs:
                    if job.is_alive():
                        job.terminate()
                        job.join()
            store = Store(project / run, project / '.humanize/math-wiki', 'Parallel fixture', shared=True)
            self.assertEqual(store.nodes['root'].model_dump(), root_before)
            self.assertEqual([store.nodes[f'leaf-{i}'].status for i in (2, 3)], ['failed', 'failed'])
            roster = json.loads((project / run / 'issue-workers.json').read_text())
            self.assertEqual(set(roster['workers']), {'attempt-2', 'attempt-3'})

    def test_reconciliation_only_publishes_owned_issue(self):
        runtime = GitHubTheoremRuntime.__new__(GitHubTheoremRuntime)
        runtime.config = configuration(2)
        from _recursive_lean.models import NodeRecord
        nodes = {str(i): NodeRecord(id=str(i), title='Proof', statement='True', status='proved',
                 github_issue_url=f'https://github.com/example/proofs/issues/{i}') for i in (1, 2, 3)}
        runtime.store = SimpleNamespace(nodes=nodes, refresh=Mock())
        runtime._publish_solution = Mock()
        runtime._reconcile_publications()
        runtime._publish_solution.assert_called_once_with(nodes['2'])

    def test_unchanged_candidate_on_noncanonical_handoff_is_not_integrated(self):
        with tempfile.TemporaryDirectory() as directory:
            runtime = Runtime.__new__(Runtime)
            runtime.project = Path(directory)
            runtime.config = configuration(2)
            runtime._promoted_commits = {}
            runtime._integration_lock = SharedLock(Path(directory) / 'integration.lock')
            runtime._git_head = Mock(return_value='canonical')
            node = NodeRecord(id='leaf', title='Leaf', statement='True')
            with patch('_recursive_lean.runtime.subprocess.run', return_value=SimpleNamespace(returncode=1)):
                ok, _ = runtime._integrate_candidate(Path(directory), 'handoff', 'handoff', node=node)
            self.assertFalse(ok)
            self.assertEqual(runtime._promoted_commits, {})

    def test_receipt_retains_exact_promotion_when_sibling_advances_head(self):
        with tempfile.TemporaryDirectory() as directory:
            runtime = Runtime.__new__(Runtime)
            runtime.project = Path(directory)
            runtime.config = configuration(2)
            runtime._promoted_commits = {}
            runtime._integration_lock = SharedLock(Path(directory) / 'integration.lock')
            runtime._git_head = Mock(return_value='before')
            runtime._git_clean = Mock(return_value=True)
            runtime.store = SimpleNamespace(update=Mock())
            runtime._publish_checkpoint = Mock()
            node = NodeRecord(id='leaf', title='Leaf', statement='True',
                              status='integrating', candidate_commit='after')
            def integrate(*args, **kwargs):
                with patch('_recursive_lean.runtime.subprocess.run', side_effect=[
                    SimpleNamespace(returncode=0, stdout='after\n'),
                    SimpleNamespace(returncode=1), SimpleNamespace(returncode=0),
                ]):
                    result = runtime._integrate_candidate(Path(directory), 'before', 'after', node=node)
                runtime._git_head.return_value = 'later-sibling-promotion'
                return result
            runtime._integrate_reviewed_candidate = integrate
            result = runtime._complete_accepted_integration(node, Path(directory), 'before', 'after', [])
            self.assertTrue(result.ok)
            self.assertTrue(all(call.kwargs['integrated_commit'] == 'after'
                                for call in runtime.store.update.call_args_list))


if __name__ == '__main__':
    unittest.main()
