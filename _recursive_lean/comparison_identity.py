"""Read-only, byte-exact Git identities for theorem comparison/review gates.

Mathematical identity metadata belongs to the caller: this module never guesses
an issue, theorem statement, or handoff from a filename or a Git revision.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path, PurePosixPath
import subprocess
from typing import Any, Iterable, Mapping


def _git(worktree: Path, *arguments: str) -> bytes:
    try:
        result = subprocess.run(
            ["git", "--no-optional-locks", "-C", str(worktree), *arguments],
            capture_output=True, check=False, timeout=60,
        )
    except (OSError, subprocess.TimeoutExpired) as error:
        raise ValueError("cannot inspect comparison Git identity") from error
    if result.returncode:
        raise ValueError("cannot inspect comparison Git identity")
    return result.stdout


def _path(value: str) -> str:
    if not isinstance(value, str) or not value or any(c in value for c in ("\0", "\n", "\r", "\\")):
        raise ValueError("unsafe comparison input path")
    path = PurePosixPath(value)
    if path.is_absolute() or any(part in {"", ".", ".."} for part in value.split("/")):
        raise ValueError("unsafe comparison input path")
    if path.parts[0] == ".git":
        raise ValueError("Git control files are not comparison inputs")
    return path.as_posix()


def _bytes(worktree: Path, name: str) -> bytes:
    path = worktree
    for component in PurePosixPath(name).parts:
        path /= component
        if path.is_symlink():
            raise ValueError(f"comparison input is a symlink: {name}")
    if not path.is_file():
        raise ValueError(f"comparison input is missing or not a regular file: {name}")
    try:
        return path.read_bytes()
    except OSError as error:
        raise ValueError(f"cannot read comparison input: {name}") from error


def _blob(worktree: Path, revision: str, name: str) -> tuple[str, bytes]:
    record = _git(worktree, "ls-tree", "-z", revision, "--", name)
    try:
        header, actual_name = record.removesuffix(b"\0").split(b"\t", 1)
        mode, kind, identity = header.decode("ascii").split()
        if actual_name.decode("utf-8") != name or kind != "blob" or mode not in {"100644", "100755"}:
            raise ValueError
    except (UnicodeError, ValueError) as error:
        raise ValueError(f"comparison input is not a regular committed file: {name}") from error
    return identity, _git(worktree, "cat-file", "blob", identity)


def _clean(worktree: Path) -> None:
    for entry in _git(worktree, "ls-files", "-v", "-z").split(b"\0"):
        if entry and (entry[:1].islower() or entry[:1] == b"S"):
            raise ValueError("comparison index hides tracked files with assume-unchanged or skip-worktree")
    if _git(worktree, "status", "--porcelain=v1", "--untracked-files=no"):
        raise ValueError("comparison worktree has changed tracked files")
    untracked = _git(worktree, "ls-files", "--others", "--exclude-standard", "-z")
    for raw in untracked.split(b"\0"):
        if not raw:
            continue
        name = raw.decode("utf-8", errors="surrogateescape")
        if name.endswith(".lean") and PurePosixPath(name).parts[0] not in {".humanize", ".lake"}:
            raise ValueError(f"comparison worktree has an untracked Lean participant: {name}")


def _revision(worktree: Path) -> dict[str, str]:
    # Replace refs can silently change the interpretation of otherwise identical
    # object IDs. They are not accepted as theorem history.
    if _git(worktree, "replace", "-l"):
        raise ValueError("comparison repository uses replacement Git objects")
    commit = _git(worktree, "rev-parse", "--verify", "HEAD^{commit}").decode("ascii").strip()
    tree = _git(worktree, "rev-parse", "--verify", "HEAD^{tree}").decode("ascii").strip()
    history = _git(worktree, "rev-list", "--parents", "HEAD")
    return {"commit": commit, "tree": tree, "history_sha256": hashlib.sha256(history).hexdigest()}


def capture(
    worktree: str | Path,
    input_paths: Iterable[str],
    *,
    metadata: Mapping[str, Any] | None = None,
    frozen_contract_path: str | None = None,
    source_commit: str | None = None,
) -> dict[str, Any]:
    """Pin candidate/history and exact live/committed bytes without writing Git.

    ``metadata`` carries caller-supplied repository, issue, frozen node name/type,
    original source, and immutable handoff identity. It is copied verbatim as
    JSON, not derived here. The optional contract/source pair additionally pins
    an unchanged original contract, while ordinary proof inputs may legitimately
    differ from that original source.
    """
    root = Path(worktree).resolve()
    if not root.is_dir() or Path(_git(root, "rev-parse", "--show-toplevel").decode().strip()).resolve() != root:
        raise ValueError("comparison worktree must be the Git worktree root")
    if isinstance(input_paths, (str, bytes)):
        raise ValueError("comparison input paths must be a collection")
    names = sorted({_path(name) for name in input_paths})
    if not names:
        raise ValueError("comparison requires explicit input files")
    if (frozen_contract_path is None) != (source_commit is None):
        raise ValueError("frozen contract requires both its path and source commit")
    try:
        supplied = json.loads(json.dumps(dict(metadata or {}), sort_keys=True, allow_nan=False))
    except (TypeError, ValueError) as error:
        raise ValueError("comparison metadata must be JSON serializable") from error
    _clean(root)
    revision = _revision(root)
    inputs = {}
    for name in names:
        blob, committed = _blob(root, revision["commit"], name)
        live = _bytes(root, name)
        if live != committed:
            raise ValueError(f"comparison input differs from candidate Git blob: {name}")
        inputs[name] = {"git_blob": blob, "sha256": hashlib.sha256(live).hexdigest(), "bytes": len(live)}
    frozen = None
    if frozen_contract_path is not None:
        name = _path(frozen_contract_path)
        # Require an immutable object ID rather than a branch whose resolution
        # could move between capture and verification.
        if not isinstance(source_commit, str) or len(source_commit) not in {40, 64} or any(c not in "0123456789abcdef" for c in source_commit):
            raise ValueError("frozen source must be an immutable Git commit ID")
        resolved = _git(root, "rev-parse", "--verify", source_commit + "^{commit}").decode("ascii").strip()
        if resolved != source_commit:
            raise ValueError("frozen source is not an exact commit object")
        original_blob, original = _blob(root, source_commit, name)
        candidate_blob, candidate = _blob(root, revision["commit"], name)
        if candidate != original or _bytes(root, name) != original:
            raise ValueError("frozen original contract changed in candidate or live worktree")
        frozen = {"path": name, "source_commit": source_commit, "source_blob": original_blob,
                  "candidate_blob": candidate_blob, "sha256": hashlib.sha256(original).hexdigest(), "bytes": len(original)}
    _clean(root)
    if _revision(root) != revision:
        raise ValueError("comparison Git identity changed during capture")
    return {"schema": 1, "worktree": str(root), **revision, "inputs": inputs,
            "frozen_contract": frozen, "metadata": supplied}


def verify(worktree: str | Path, identity: Mapping[str, Any]) -> None:
    """Reject any before/after identity difference, never repair or reset it."""
    try:
        if identity.get("schema") != 1 or not isinstance(identity.get("inputs"), dict):
            raise ValueError("invalid comparison identity")
        frozen = identity["frozen_contract"]
        current = capture(worktree, identity["inputs"], metadata=identity["metadata"],
                          frozen_contract_path=frozen["path"] if frozen else None,
                          source_commit=frozen["source_commit"] if frozen else None)
    except (KeyError, TypeError, AttributeError) as error:
        raise ValueError("invalid comparison identity") from error
    if current != identity:
        raise ValueError("comparison candidate, history, tree, input, or metadata identity changed")
