#!/usr/bin/env python3
"""Controller-only proposal: export a terminal failure for diagnosis, never acceptance.

Run only against trusted controller originals after operator review. This does not
execute checker code, launch jobs, change verdicts, or write the private ledger.
It supports the cached Swarm adapter's terminal nonzero-result receipt format.
"""

import argparse
import fcntl
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import shutil
import sqlite3
import stat
import tempfile


CHECKERS = {
    "verify-frozen-node.py", "swarm-verifier-packet.py", "swarm-verifier-selftest.py"
}
GENERATED = (
    "config.json", "challenge/lakefile.lean", "challenge/lake-manifest.json",
    "challenge/lean-toolchain", "solution/lakefile.lean",
    "solution/lake-manifest.json", "solution/lean-toolchain",
)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def canonical_digest(value):
    return sha256(json.dumps(value, sort_keys=True, separators=(",", ":")).encode())


def regular(path):
    """Read a regular file without accepting links in any path component."""
    path = Path(path).absolute()
    require(".." not in path.parts, "parent traversal in controller path")
    require(not any(p.is_symlink() for p in (path, *path.parents)), "symlink in artifact path")
    require(stat.S_ISREG(path.stat().st_mode), "artifact is not a regular file")
    return path.read_bytes()


def source_name(name):
    p = PurePosixPath(name)
    require(name == p.as_posix() and not p.is_absolute() and ".." not in p.parts,
            "noncanonical source path")
    require(len(p.parts) > 1 and p.parts[0] in {"challenge", "solution"}
            and ".lake" not in p.parts and p.suffix == ".lean"
            and p.parts[1:] != ("lakefile.lean",), "unexpected source artifact")
    return p


def source_inventory(root):
    names = set()
    for side in ("challenge", "solution"):
        directory = root / side
        require(directory.is_dir() and not directory.is_symlink(), "missing source tree")
        for path in directory.rglob("*"):
            relative = path.relative_to(root)
            if ".lake" in relative.parts:
                continue
            require(not path.is_symlink(), "symlink in source tree")
            if (path.is_file() and path.suffix == ".lean"
                    and path.relative_to(directory) != Path("lakefile.lean")):
                names.add(relative.as_posix())
    return names


def collect(database, operation_root, request_id, candidate, packet_digest, reference_manifest):
    """Validate private bindings and return an allowlisted diagnostic copy in memory."""
    require(re.fullmatch(r"[a-f0-9]{32}", request_id), "invalid request identity")
    require(re.fullmatch(r"[a-f0-9]{40}", candidate), "invalid candidate identity")
    require(re.fullmatch(r"[a-f0-9]{64}", packet_digest), "invalid packet digest")
    database = Path(database).absolute()
    # Inspect the database's path without copying or publishing database contents.
    require(not any(p.is_symlink() for p in (database, *database.parents)), "symlink in database path")
    require(database.is_file(), "missing controller ledger")
    with sqlite3.connect(database.as_uri() + "?mode=ro", uri=True) as db:
        db.row_factory = sqlite3.Row
        row = db.execute(
            "SELECT id,state,returncode,request,log FROM verifications WHERE id=?", (request_id,)
        ).fetchone()
    require(row is not None and row["state"] == "finished" and row["returncode"] == 1,
            "request is not a terminal failed adapter invocation")
    request = json.loads(row["request"])
    require(request["revision"] == candidate, "ledger candidate mismatch")

    root = Path(operation_root).absolute()
    require(root.name == request_id, "operation directory request mismatch")
    operation_bytes = regular(root / "operation.json")
    operation = json.loads(operation_bytes)
    # The registered adapter maps every terminal nonzero container exit to 1.
    code = operation.get("returncode")
    require(operation.get("state") == "terminal" and type(code) is int and code > 0,
            "operation is not a terminal failure")
    require(operation.get("request_id") == request_id
            and operation.get("candidate_commit") == candidate
            and operation.get("packet_digest") == packet_digest, "operation identity mismatch")
    for key in ("service_id", "task_id", "node_id"):
        require(re.fullmatch(r"[a-z0-9]{25}", operation.get(key, "")), "missing remote identity")
    status = operation.get("task_status", {})
    require(status.get("State") == "failed"
            and status.get("ContainerStatus", {}).get("ExitCode") == code
            and status.get("ContainerStatus", {}).get("PID", 0) == 0,
            "receipt lacks consistent terminal container status")

    prepared_root = Path(operation["packet"])
    require(prepared_root.is_absolute() and prepared_root.is_relative_to(root / "prepared")
            and ".." not in prepared_root.parts, "packet is outside the private operation")
    result_root = root / "output/result"
    packet_bytes = regular(prepared_root / "prepared.json")
    packet = json.loads(packet_bytes)
    require(packet.get("schema") == 1 and canonical_digest(packet) == packet_digest,
            "prepared packet digest mismatch")
    require(regular(result_root / "prepared.json") == packet_bytes, "remote packet changed")
    evidence = packet["evidence"]
    require(evidence.get("status") == "checking"
            and evidence.get("candidate_commit") == candidate
            and evidence.get("node") == request["node_id"]
            and evidence.get("root_contract_commit") == request["source_commit"],
            "packet/request identity mismatch")
    evidence_bytes = regular(result_root / "evidence.json")
    require(json.loads(evidence_bytes) == evidence
            and json.loads(regular(prepared_root / "evidence.json")) == evidence,
            "failed result evidence changed or was relabeled")

    artifacts = {"operation.json": operation_bytes, "prepared.json": packet_bytes,
                 "evidence.json": evidence_bytes}
    sources = packet["source_sha256"]
    require({"challenge/Challenge.lean", "solution/Solution.lean"} <= sources.keys(),
            "missing comparator entrypoints")
    require(source_inventory(prepared_root) == source_inventory(result_root) == set(sources),
            "source inventory mismatch")
    for name, expected in sources.items():
        source_name(name)
        original = regular(prepared_root / name)
        data = regular(result_root / name)
        require(sha256(original) == sha256(data) == expected, "source digest mismatch")
        artifacts[name] = data

    hashes = operation.get("code_sha256", {})
    require(set(hashes) == CHECKERS, "unsupported executed checker inventory")
    for name, expected in hashes.items():
        data = regular(root / "code" / name)
        require(sha256(data) == expected, "executed checker digest mismatch")
        artifacts["code/" + name] = data
    require(hashes["verify-frozen-node.py"] == evidence.get("verifier_sha256"),
            "packet/checker identity mismatch")

    reference = regular(reference_manifest)
    cache_digest = sha256(reference)
    require(cache_digest == operation.get("reference_cache_digest")
            == evidence.get("reference_cache_digest"), "reference-cache digest mismatch")
    inventory = json.loads(reference)
    require(inventory.get("schema") == 1
            and inventory.get("toolchain") == evidence.get("lean_toolchain") == "v4.33.1",
            "reference toolchain mismatch")
    artifacts["reference.json"] = reference
    artifacts["terminal.log"] = regular(row["log"])

    # Generated configuration is captured for inspection, never called receipt-bound.
    captured, absent = [], []
    for name in GENERATED:
        path = result_root / name
        if path.exists() or path.is_symlink():
            artifacts[name] = regular(path)
            captured.append(name)
        else:
            absent.append(name)
    # Export only these ledger fields; never publish the private request/job or credentials.
    projection = {"request_id": request_id, "revision": candidate, "node_id": request["node_id"],
                  "source_commit": request["source_commit"], "state": row["state"],
                  "returncode": row["returncode"]}
    artifacts["request.json"] = (json.dumps(projection, indent=2) + "\n").encode()
    manifest = {"schema": 1, "purpose": "failed-request diagnosis only", "acceptance": False,
                **projection, "packet_digest": packet_digest, "remote_returncode": code,
                "generated_configuration_captured_not_receipt_bound": captured,
                "generated_configuration_absent": absent,
                "reference_inventory_contents_rechecked": False,
                "authority": "Controller private originals and operator publication remain authoritative.",
                "files": {name: sha256(data) for name, data in sorted(artifacts.items())}}
    artifacts["diagnostic-export.json"] = (json.dumps(manifest, indent=2) + "\n").encode()
    return artifacts


def publish(artifacts, destination, request_id):
    """Publish under a separate diagnostic namespace, with no log/ledger mutation."""
    destination = Path(destination).absolute()
    require(destination.is_dir() and not any(p.is_symlink() for p in (destination, *destination.parents)),
            "diagnostic destination must be an existing real directory")
    require(re.fullmatch(r"[a-f0-9]{32}", request_id), "invalid publication request")
    target = destination / request_id
    lock_path = destination / ".diagnostic-export.lock"
    descriptor = os.open(lock_path, os.O_CREAT | os.O_RDWR | os.O_NOFOLLOW, 0o600)
    with os.fdopen(descriptor, "a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        if target.exists() or target.is_symlink():
            require(target.is_dir() and not target.is_symlink(), "existing export is not a directory")
            paths = list(target.rglob("*"))
            for path in (target, *paths):
                mode = path.lstat().st_mode
                require(stat.S_ISREG(mode) or stat.S_ISDIR(mode),
                        "existing export contains a link or special file")
                expected_mode = 0o555 if stat.S_ISDIR(mode) else 0o444
                require(stat.S_IMODE(mode) == expected_mode, "existing export permissions differ")
            require({p.relative_to(target).as_posix() for p in paths if p.is_file()} == set(artifacts),
                    "existing export inventory differs")
            require(all(regular(target / name) == data for name, data in artifacts.items()),
                    "existing export bytes differ")
            return target
        temporary = Path(tempfile.mkdtemp(prefix=".diagnostic-", dir=destination))
        try:
            for name, data in artifacts.items():
                path = temporary / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(data)
                path.chmod(0o444)
            for path in sorted(temporary.rglob("*"), reverse=True):
                if path.is_dir():
                    path.chmod(0o555)
            temporary.chmod(0o555)
            temporary.rename(target)
        finally:
            if temporary.exists():
                temporary.chmod(0o700)
                for path in temporary.rglob("*"):
                    if path.is_dir():
                        path.chmod(0o700)
                shutil.rmtree(temporary)
    return target


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("database", "operation-root", "reference-manifest", "destination"):
        parser.add_argument("--" + name, required=True, type=Path)
    for name in ("request-id", "candidate", "packet-digest"):
        parser.add_argument("--" + name, required=True)
    args = parser.parse_args()
    artifacts = collect(args.database, args.operation_root, args.request_id, args.candidate,
                        args.packet_digest, args.reference_manifest)
    target = publish(artifacts, args.destination, args.request_id)
    print(json.dumps({"diagnostic_export": str(target), "request_id": args.request_id,
                      "verdict_changed": False, "acceptance": False}))


if __name__ == "__main__":
    main()
