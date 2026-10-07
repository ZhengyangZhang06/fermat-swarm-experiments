"""Fail-closed three-way merge for independently owned theorem-node writers."""
from __future__ import annotations

from copy import deepcopy

from .models import NodeRecord


class StateConflict(RuntimeError):
    """An observation is stale in a way that cannot safely be merged."""


# Changes to any of these bindings invalidate the accepted proof's evidence.
# Integration receipts and GitHub observations can advance independently.
ACCEPTANCE_FIELDS = (
    'id', 'parent', 'depth', 'statement', 'lean_statement', 'lean_name',
    'plan', 'natural_proof', 'parent_handoff', 'children', 'depends_on',
    'candidate_commit', 'proof_base_commit', 'proof_branch', 'worktree',
    'lean_files', 'theorems', 'workspace_remote', 'workspace_manifest_path',
    'workspace_bundle_path', 'workspace_handoff_branch', 'workspace_handoff_commit',
    'workspace_result_branch', 'workspace_result_commit',
    'workspace_dispatch_branch', 'workspace_dispatch_commit',
)


def _field(base, local, remote, path):
    if local == remote or remote == base:
        return deepcopy(local)
    if local == base:
        return deepcopy(remote)
    if path.endswith('.updated_at'):
        return max(local, remote)
    # Independent children can be appended to the same parent. Deletion/revision
    # is not commutative and requires a fresh, explicitly serialized decision.
    if path.endswith('.children') and set(base) <= set(local) & set(remote):
        return list(dict.fromkeys([*remote, *local]))
    raise StateConflict(f'concurrent DAG changes conflict at {path}')


def merge_nodes(baseline: dict, local: dict, remote: dict) -> dict:
    """Merge nonoverlapping changes, never guess between conflicting evidence."""
    merged = {}
    for node_id in sorted(baseline.keys() | local.keys() | remote.keys()):
        before, ours, theirs = (d.get(node_id) for d in (baseline, local, remote))
        if before is None:
            if ours is not None and theirs is not None and ours != theirs:
                raise StateConflict(f'concurrent node creation: {node_id}')
            merged[node_id] = deepcopy(ours if ours is not None else theirs)
            continue
        if ours is None or theirs is None:
            raise StateConflict(f'node deletion is not supported: {node_id}')
        made = {key: _field(before[key], ours[key], theirs[key], f'{node_id}.{key}')
                for key in before}
        # Accepted checkpoint invariants also apply to direct field mutations,
        # not just Store.update(). Never silently discard a concurrent result.
        for accepted in (before, ours, theirs):
            if accepted['status'] == 'proved' and made['status'] != 'proved':
                raise StateConflict(f'proved checkpoint regression: {node_id}')
            if (accepted['status'] == 'integrating' and accepted['candidate_commit']
                    and made['status'] not in {'integrating', 'proved'}):
                raise StateConflict(f'accepted candidate regression: {node_id}')
            if accepted['status'] in {'proved', 'integrating'} and accepted['candidate_commit']:
                for key in ACCEPTANCE_FIELDS:
                    if made[key] != accepted[key]:
                        raise StateConflict(f'accepted evidence changed: {node_id}.{key}')
        merged[node_id] = made
    validate_nodes(merged)
    return merged


def validate_nodes(nodes: dict, *, complete: bool = False):
    """Validate identity, declaration uniqueness and all currently known edges.

    ``complete`` is required at dispatch: construction may temporarily reference
    the next sibling while a serialized decomposition is being assembled.
    """
    names = {}
    edges = {}
    for node_id, raw in nodes.items():
        node = NodeRecord.model_validate(raw)
        if node.id != node_id:
            raise StateConflict('DAG key differs from node identity')
        if node.lean_name:
            other = names.setdefault(node.lean_name, node.id)
            if other != node.id:
                raise StateConflict(f'duplicate Lean declaration: {node.lean_name}')
        dependencies = set(node.children) | set(node.depends_on)
        if complete and dependencies - nodes.keys():
            raise StateConflict(f'missing dependency for {node.id}')
        edges[node_id] = dependencies & nodes.keys()
        for child in node.children:
            if (child in nodes and nodes[child]['parent'] != node_id
                    and nodes[child]['status'] not in {'integrating', 'proved'}):
                raise StateConflict(f'inconsistent child ownership: {child}')
        if complete and node.parent and node.parent not in nodes:
            raise StateConflict(f'missing parent for {node.id}')
    active, done = set(), set()

    def visit(node_id):
        if node_id in active:
            raise StateConflict(f'cyclic theorem dependencies at {node_id}')
        if node_id in done:
            return
        active.add(node_id)
        for dependency in edges[node_id]:
            visit(dependency)
        active.remove(node_id)
        done.add(node_id)

    for node_id in edges:
        visit(node_id)
