"""Shared issue-runtime protocol and short state-refresh critical sections."""
from __future__ import annotations

from pathlib import Path

from .models import ChildProofHandoff, Decomposition, DecompositionAudit
from .store import slug

PROTOCOL = 'shared-theorem-issues-v1'


def _record(node):
    return node if isinstance(node, dict) else node.model_dump(mode='json')


def child_publication_pending(parent, nodes):
    """A scheduling hint only: unpublished children need their parent's identity.

    This is not permission to formalize a parent with unsolved dependencies.
    The paired audit and immutable handoffs must be revalidated before publishing.
    """
    parent = _record(parent)
    for key in parent.get('children', []):
        if key not in nodes:
            continue
        child = _record(nodes[key])
        if child.get('parent') == parent['id'] and not all(child.get(field) for field in (
                'github_issue_url', 'workspace_handoff_commit', 'workspace_bundle_path')):
            return True
    return False


def child_publication_checkpoint(project, run_root, parent, nodes):
    """Load an exact, already accepted split without generating or changing proofs.

    Both the broker hint and issue runtime fail closed on missing/mismatched audit
    artifacts. Runtime additionally checks the complete parent-supplied proof files
    and accepted reused children before doing any external publication.
    """
    project = Path(project).resolve()
    parent = _record(parent)
    children = [_record(nodes[key]) for key in parent.get('children', [])]
    directory = Path(run_root) / 'nodes' / slug(parent['id'])
    for path in sorted(directory.glob('decomposition-v*.json'), reverse=True):
        version = path.stem.rsplit('v', 1)[-1]
        try:
            decomposition = Decomposition.model_validate_json(path.read_text())
            audit = DecompositionAudit.model_validate_json(
                (directory / f'decomposition-audit-v{version}.json').read_text())
            if not decomposition.should_split or not audit.passed:
                continue
            if [one.key for one in audit.nodes] != [one.key for one in decomposition.subproblems]:
                continue
            if len(children) != len(decomposition.subproblems):
                continue
            ids = {}
            for child, subproblem in zip(children, decomposition.subproblems):
                if any(child.get(field) != getattr(subproblem, field) for field in (
                        'title', 'statement', 'lean_name', 'lean_statement')):
                    raise ValueError('current child differs from reviewed decomposition')
                ids[subproblem.key] = child['id']
            for child, subproblem, verdict in zip(children, decomposition.subproblems, audit.nodes):
                dependencies = [ids[key] for key in subproblem.depends_on]
                if child.get('depends_on', []) != dependencies:
                    raise ValueError('current child dependencies differ from reviewed decomposition')
                if child.get('parent') != parent['id']:
                    if child.get('status') != 'proved':
                        raise ValueError('unproved child belongs to another parent')
                    continue
                handoff_path = (project / child.get('parent_handoff', '')).resolve()
                if not handoff_path.is_relative_to(project):
                    raise ValueError('child handoff is outside registered project')
                handoff = ChildProofHandoff.model_validate_json(handoff_path.read_text())
                if (handoff.parent_id != parent['id'] or handoff.child_id != child['id']
                        or handoff.subproblem != subproblem or handoff.audit != verdict
                        or handoff.reference_use != decomposition.reference_use
                        or handoff.resolved_dependencies != dependencies
                        or handoff.plan_path != child.get('plan')
                        or handoff.natural_proof_path != child.get('natural_proof')):
                    raise ValueError('child handoff differs from exact paired decomposition audit')
            return decomposition, audit, ids
        except (OSError, ValueError, KeyError):
            continue
    raise ValueError('no exact passing decomposition/audit pair matches current child handoffs')


def enabled(config):
    return getattr(config, 'github_shared_issue_runtime', False) is True


def selected(config, node):
    if not enabled(config):
        return True
    if node.id == 'root' and not node.github_issue_url:
        return config.github_selected_issue == config.github_root_issue_number
    return node.github_issue_url == (
        f'https://github.com/{config.github_repository}/issues/{config.github_selected_issue}'
    )


class RefreshLock:
    """Serialize an operation and refresh its graph before inspecting aliases."""

    def __init__(self, lock, store):
        self.lock, self.store = lock, store

    def __enter__(self):
        self.lock.__enter__()
        try:
            self.store.refresh()
            return self
        except BaseException:
            self.lock.__exit__(None, None, None)
            raise

    def __exit__(self, *exc):
        return self.lock.__exit__(*exc)
