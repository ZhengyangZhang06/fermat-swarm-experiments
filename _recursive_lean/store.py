"""Atomic DAG and wiki persistence for an observable long-running flow."""

from __future__ import annotations

import datetime as dt
from copy import deepcopy
import hashlib
import json
import os
import re
import tempfile
import threading
from typing import TYPE_CHECKING, Any

from .models import NodeRecord, NodeStatus, ProvedTheorem
from .shared_dag import StateConflict, merge_nodes, validate_nodes
from .shared_lock import SharedLock

if TYPE_CHECKING:
    from collections.abc import Callable
    from pathlib import Path


def now() -> str:
    """Return one stable UTC timestamp for status records."""
    return dt.datetime.now(dt.UTC).strftime("%Y-%m-%dT%H:%M:%SZ")


def slug(value: str, *, fallback: str = "theorem") -> str:
    """Turn a model-provided name into a bounded, collision-resistant component."""
    made = re.sub(r"[^a-z0-9]+", "-", value.casefold()).strip("-")
    if not made:
        return fallback
    if len(made) <= 80:
        return made
    digest = hashlib.sha256(made.encode()).hexdigest()[:10]
    return f"{made[:69].rstrip('-')}-{digest}"


def atomic_text(path: Path, content: str) -> None:
    """Replace one small control artifact without exposing a partial write."""
    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor, temporary_name = tempfile.mkstemp(
        prefix=f".{path.name}.",
        suffix=".tmp",
        dir=path.parent,
        text=True,
    )
    temporary = path.parent / os.path.basename(temporary_name)
    try:
        with os.fdopen(descriptor, "w", encoding="utf-8") as output:
            output.write(content)
            output.flush()
            os.fsync(output.fileno())
        temporary.replace(path)
    finally:
        temporary.unlink(missing_ok=True)


class Store:
    """The single writer of node state, rendered DAGs, and theorem wiki pages."""

    def __init__(self, root: Path, wiki: Path, task: str, *, shared: bool = False) -> None:
        self.root = root
        self.wiki = wiki
        self.task = task
        self.problem_artifact = ""
        self.reference_manifest = ""
        self.required_references = ["TauCeti", "lean-pool", "mathlib-internal"]
        self.nodes: dict[str, NodeRecord] = {}
        self.on_render: Callable[[dict[str, Any]], None] | None = None
        self.shared = shared
        self._lock = SharedLock(root / "dag-state.lock") if shared else threading.RLock()
        self._baseline: dict[str, dict] = {}
        self._metadata_baseline: dict[str, Any] = {}
        self.root.mkdir(parents=True, exist_ok=True)
        self.wiki.mkdir(parents=True, exist_ok=True)
        with self._lock:
            self._load()
            self._checkpoint()

    def _metadata(self):
        return {key: deepcopy(getattr(self, key)) for key in (
            'task', 'problem_artifact', 'reference_manifest', 'required_references')}

    @staticmethod
    def _validate_metadata(payload):
        if not isinstance(payload, dict) or not isinstance(payload.get('nodes'), list):
            raise ValueError('invalid DAG document')
        if not all(isinstance(payload.get(key), str) for key in (
                'task', 'problem_artifact', 'reference_manifest')):
            raise ValueError('invalid DAG metadata')
        references = payload.get('required_references')
        if not isinstance(references, list) or not all(isinstance(r, str) for r in references):
            raise ValueError('invalid DAG reference metadata')

    def _checkpoint(self):
        self._baseline = {key: node.model_dump(mode='json') for key, node in self.nodes.items()}
        self._metadata_baseline = self._metadata()

    def refresh(self) -> None:
        """Merge the latest disk observation without invalidating node aliases."""
        if not self.shared:
            return
        with self._lock:
            path = self.root / 'dag.json'
            if not path.exists():
                if self._baseline:
                    raise StateConflict('persisted DAG disappeared')
                return
            try:
                payload = json.loads(path.read_text(encoding='utf-8'))
                self._validate_metadata(payload)
                records = payload['nodes']
                remote = {raw['id']: NodeRecord.model_validate(raw).model_dump(mode='json')
                          for raw in records}
                if len(remote) != len(records):
                    raise ValueError('duplicate node identities')
                merged = merge_nodes(self._baseline,
                                     {key: n.model_dump(mode='json') for key, n in self.nodes.items()},
                                     remote)
                metadata = {}
                for key, ours in self._metadata().items():
                    before, theirs = self._metadata_baseline[key], payload[key]
                    if ours != theirs and ours != before and theirs != before:
                        raise StateConflict(f'conflicting DAG metadata: {key}')
                    metadata[key] = theirs if ours == before else ours
            except (OSError, ValueError, TypeError, KeyError) as error:
                raise StateConflict('cannot read the shared DAG; refusing to overwrite it') from error
            # Validate/merge everything before mutating any live object.
            for key, raw in merged.items():
                made = NodeRecord.model_validate(raw)
                if key in self.nodes:
                    for field in type(made).model_fields:
                        setattr(self.nodes[key], field, deepcopy(getattr(made, field)))
                else:
                    self.nodes[key] = made
            for key, value in metadata.items():
                setattr(self, key, deepcopy(value))
            # The baseline is what DISK contains, not our merged unsaved changes.
            self._baseline = deepcopy(remote)
            self._metadata_baseline = {key: deepcopy(payload[key]) for key in metadata}

    def _load(self) -> None:
        path = self.root / "dag.json"
        if not path.is_file():
            return
        try:
            held = json.loads(path.read_text(encoding="utf-8"))
            if self.shared:
                self._validate_metadata(held)
            records = held.get("nodes", [])
            self.nodes = {
                record.id: record
                for one in records
                for record in [NodeRecord.model_validate(one)]
            }
            if self.shared:
                if len(self.nodes) != len(records):
                    raise ValueError('duplicate node identities')
                self._validate_metadata(held)
                validate_nodes({key: n.model_dump(mode='json') for key, n in self.nodes.items()})
                for key in self._metadata():
                    setattr(self, key, held[key])
        except (OSError, ValueError, TypeError, KeyError):
            if self.shared:
                raise StateConflict('cannot load the shared DAG; refusing to replace it')
            self.nodes = {}

    def ensure(
        self,
        node_id: str,
        *,
        parent: str | None,
        depth: int,
        title: str,
        statement: str,
        lean_statement: str = "",
        lean_name: str = "",
        depends_on: list[str] | None = None,
    ) -> NodeRecord:
        """Return an existing node or durably add it to the graph."""
        with self._lock:
            self.refresh()
            found = self.nodes.get(node_id)
            if found is not None:
                return found
            record = NodeRecord(
                id=node_id,
                parent=parent,
                depth=depth,
                title=title,
                statement=statement,
                lean_statement=lean_statement,
                lean_name=lean_name,
                depends_on=depends_on or [],
                updated_at=now(),
            )
            self.nodes[node_id] = record
            if parent and parent in self.nodes:
                parent_record = self.nodes[parent]
                if node_id not in parent_record.children:
                    parent_record.children.append(node_id)
            self.render()
            return record

    def update(
        self, node_id: str, status: NodeStatus, message: str = "", **fields: Any
    ) -> None:
        """Persist one status transition and immediately redraw the live DAG."""
        with self._lock:
            self.refresh()
            record = self.nodes[node_id]
            # Comparator + independent reviewer approval is a permanent checkpoint.
            # A later integration conflict is about composing Git histories; it must
            # never send accepted mathematics back through planning, prose, splitting,
            # or Lean proving.  Keep this invariant here at the persistence boundary so
            # stale supervisors cannot accidentally erase it.
            if record.status == "proved" and status != "proved":
                print(
                    f"[DAG] {node_id}: proved — ignored regressive transition to {status}"
                )
                return
            if (
                record.status == "integrating"
                and record.candidate_commit
                and status not in {"integrating", "proved"}
            ):
                print(
                    f"[DAG] {node_id}: integrating — retained accepted candidate; "
                    f"ignored regressive transition to {status}"
                )
                return
            record.status = status
            record.message = message
            record.updated_at = now()
            for name, value in fields.items():
                setattr(record, name, value)
            self.render()
            print(f"[DAG] {node_id}: {status}" + (f" — {message}" if message else ""))

    def render(self) -> None:
        """Write machine-readable state, Mermaid, and a compact Markdown status view."""
        with self._lock:
            self.refresh()
            if self.shared:
                validate_nodes({key: n.model_dump(mode='json') for key, n in self.nodes.items()})
            ordered = sorted(self.nodes.values(), key=lambda one: (one.depth, one.id))
            payload = {
                "updated_at": now(),
                "task": self.task,
                "problem_artifact": self.problem_artifact,
                "reference_manifest": self.reference_manifest,
                "required_references": self.required_references,
                "nodes": [one.model_dump(mode="json") for one in ordered],
            }
            atomic_text(
                self.root / "dag.json",
                json.dumps(payload, ensure_ascii=False, indent=2) + "\n",
            )
            self._checkpoint()
            mermaid = [
                "flowchart TD",
                (
                    '  legend["Every solid arrow A --&gt; B means A depends on B<br/>'
                    'B must be proved before A can finish"]'
                ),
            ]
            for record in ordered:
                label = self._label(record, self._scheduling(record))
                mermaid.append(f'  {self._mermaid_id(record.id)}["{label}"]')
            # Use one direction and one line style everywhere: the arrow starts at
            # the dependent theorem and points toward what it needs. A parent
            # depends on every decomposition child; a node depends on every
            # explicit prerequisite in ``depends_on``.
            edges: set[tuple[str, str]] = set()
            for record in ordered:
                edges.update(
                    (record.id, child)
                    for child in record.children
                    if child in self.nodes
                )
                if (
                    record.parent
                    and record.parent in self.nodes
                    and record.id not in self.nodes[record.parent].children
                ):
                    edges.add((record.parent, record.id))
                edges.update(
                    (record.id, dependency)
                    for dependency in record.depends_on
                    if dependency in self.nodes
                )
            mermaid.extend(
                f"  {self._mermaid_id(dependent)} --> {self._mermaid_id(dependency)}"
                for dependent, dependency in sorted(edges)
            )
            diagram = "\n".join(mermaid) + "\n"
            atomic_text(self.root / "dag.mmd", diagram)
            rows = [
                "# Recursive Lean proof DAG",
                "",
                f"Updated: {payload['updated_at']}",
                f"Fetched problem: `{self.problem_artifact or 'preflight pending'}`",
                (
                    "Mandatory references for every stage: "
                    + ", ".join(self.required_references)
                ),
                f"Reference manifest: `{self.reference_manifest or 'preflight pending'}`",
                "",
                "```mermaid",
                diagram.rstrip(),
                "```",
                "",
                "| Node | Depth | Status | Scheduling | Theorem | Message |",
                "| --- | ---: | --- | --- | --- | --- |",
            ]
            rows.extend(
                (
                    (
                        "| {node} | {depth} | {status} | {scheduling} | "
                        "{theorem} | {message} |"
                    ).format(
                        node=self._cell(record.id),
                        depth=record.depth,
                        status=record.status,
                        scheduling=self._cell(self._scheduling(record)),
                        theorem=self._cell(record.lean_name or "—"),
                        message=self._cell(record.message or "—"),
                    )
                )
                for record in ordered
            )
            published = [record for record in ordered if record.github_issue_url]
            if published:
                rows.extend(
                    [
                        "",
                        "## GitHub theorem review",
                        "",
                        "Local `proved` means verified and integrated locally, not merged on GitHub.",
                        "",
                        "| Node | Issue | Solution PR |",
                        "| --- | --- | --- |",
                        *[
                            f"| {record.id} | {record.github_issue_url} | "
                            f"{record.github_pr_url or 'Pending'} |"
                            for record in published
                        ],
                    ]
                )
            atomic_text(self.root / "DAG.md", "\n".join(rows) + "\n")
            if self.on_render is not None:
                self.on_render(payload)

    def publish(
        self,
        node: NodeRecord,
        theorem: ProvedTheorem,
        *,
        plan: str,
        natural: str,
        comparator_log: str,
    ) -> Path:
        """Write or update one theorem page and rebuild the wiki index."""
        page = self.wiki / f"{slug(theorem.name)}.md"
        content = f"""# `{theorem.name}`

- Status: comparator-approved and independently reviewed
- DAG node: `{node.id}`
- Recursion depth: {node.depth}
- Parent: `{node.parent or "none"}`
- Lean source: `{theorem.lean_file}`
- Isolated proof worktree: `{node.worktree or "not recorded"}`
- Proof branch: `{node.proof_branch or "not recorded"}`
- Proof base commit: `{node.proof_base_commit or "not recorded"}`
- Reviewed candidate commit: `{node.candidate_commit or "not recorded"}`
- Integrated problem commit: `{node.integrated_commit or "not recorded"}`
- GitHub workspace remote: `{node.workspace_remote or "not configured"}`
- Parent dispatch branch: `{node.workspace_handoff_branch or "not recorded"}`
- Parent dispatch commit: `{node.workspace_handoff_commit or "not recorded"}`
- Child result branch: `{node.workspace_result_branch or "not recorded"}`
- Pushed child result commit: `{node.workspace_result_commit or "not recorded"}`
- Fetched problem artifact: `{self.problem_artifact or "not recorded"}`
- Reference snapshot manifest: `{self.reference_manifest or "not recorded"}`
- Mandatory reference corpora: {", ".join(self.required_references)}
- Updated: {now()}

## Statement

{theorem.statement}

## Mathematical summary

{theorem.natural_summary}

## Node problem

{node.statement}

## Natural-language proof

{natural}

## Accepted plan

{plan}

## Comparator evidence

```text
{comparator_log.rstrip()}
```
"""
        # The wiki directory can be shared by different runs as well as workers.
        # Use its own stable lock; do not call back into DAG/publication locks.
        with SharedLock(self.wiki / '.wiki-index.lock'):
            atomic_text(page, content)
            self._wiki_index()
        return page

    def _wiki_index(self) -> None:
        pages = sorted(one for one in self.wiki.glob("*.md") if one.name != "README.md")
        rows = [
            "# Comparator-approved theorem wiki",
            "",
            "Every page here was emitted only after the configured comparator and a fresh",
            "Lean reviewer both passed.",
            "",
        ]
        rows.extend(f"- [{one.stem}]({one.name})" for one in pages)
        atomic_text(self.wiki / "README.md", "\n".join(rows) + "\n")

    @staticmethod
    def _mermaid_id(node_id: str) -> str:
        return "n_" + re.sub(r"[^A-Za-z0-9_]", "_", node_id)

    @staticmethod
    def _cell(value: str) -> str:
        return value.replace("|", "\\|").replace("\n", " ")

    def _scheduling(self, record: NodeRecord) -> str:
        """Explain decomposition shape separately from dependency readiness."""
        shape = "decomposition leaf" if not record.children else "decomposed node"
        unfinished_children = [
            child
            for child in record.children
            if child in self.nodes and self.nodes[child].status != "proved"
        ]
        if record.status in {"speculative-lean", "speculative-ready"}:
            phase = (
                "parent Lean coding active"
                if record.status == "speculative-lean"
                else "parent Lean draft ready"
            )
            return (
                f"{shape}; speculative {phase}; "
                f"{len(unfinished_children)} real child gate(s) in flight"
            )
        blocked = [
            dependency
            for dependency in record.depends_on
            if dependency in self.nodes and self.nodes[dependency].status != "proved"
        ]
        if blocked:
            return f"{shape}; blocked by: {', '.join(blocked)}"
        if unfinished_children:
            return f"{shape}; waiting for {len(unfinished_children)} child theorem(s)"
        if record.status == "proved":
            return f"{shape}; proved"
        return f"{shape}; dependency-ready"

    @staticmethod
    def _label(record: NodeRecord, scheduling: str) -> str:
        compact = record.title.replace('"', "'").replace("\n", " ")[:46]
        compact_schedule = scheduling.replace('"', "'")[:84]
        return f"{record.id}\\n{compact}\\n[{record.status}]\\n{compact_schedule}"
