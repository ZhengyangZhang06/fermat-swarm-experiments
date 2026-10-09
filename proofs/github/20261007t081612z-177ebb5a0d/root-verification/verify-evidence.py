#!/usr/bin/env python3
"""Audit an existing controller result offline; never run Lean or a comparator."""

import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import subprocess
import tarfile


ROOT = Path(__file__).resolve().parent
REQUEST = "5e4f5b622c094d1ba9ffe7cbe598dd1c"
CANDIDATE = "e03397c0ce0433baff5ac5cc10567afbbabd7667"
PACKET_DIGEST = "5650377b5c3128581f8dfc57783aea07bedb52608ee5b0a5e49df602eaed0ad9"
FROZEN_SOURCE = "1f74c284b125d4c45f527f2d621597fcf1e103a9"
EXPORT_PATH = "/runtime/review-evidence-extra-v3/" + REQUEST


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def git_file(revision, name):
    require(re.fullmatch(r"[a-f0-9]{40}", revision), "invalid Git revision")
    return subprocess.check_output(["git", "show", f"{revision}:{name}"], cwd=ROOT)


def main():
    packet = json.loads((ROOT / "prepared.json").read_bytes())
    result = json.loads((ROOT / "evidence.json").read_bytes())
    receipt = json.loads((ROOT / "review-export.json").read_bytes())
    response = json.loads((ROOT / "broker-result.json").read_bytes())
    canonical = json.dumps(packet, sort_keys=True, separators=(",", ":")).encode()
    require(packet["schema"] == 1 and sha(canonical) == PACKET_DIGEST, "packet digest mismatch")
    for record in (receipt, response):
        require(record["request_id"] == REQUEST, "request mismatch")
    require(receipt["packet_digest"] == PACKET_DIGEST, "export packet mismatch")
    require(receipt["candidate_commit"] == CANDIDATE, "export candidate mismatch")
    require(receipt["node_id"] == "root" and receipt["transport"] == "remote", "export identity mismatch")
    require(response["revision"] == CANDIDATE, "response candidate mismatch")
    require(response["state"] == "finished", "request is not finished")
    require(type(response["returncode"]) is int and response["returncode"] == 0, "nonzero return code")
    require("Your solution is okay!" in response["output"], "missing success marker")
    require(f"Controller review-artifact export {REQUEST}: {EXPORT_PATH}" in response["output"],
            "broker did not identify the controller export")
    stages = [json.loads(line) for line in response["output"].splitlines()
              if line.startswith('{"stage":')]
    require(any(s.get("stage") == "packet-verified" and s.get("digest") == PACKET_DIGEST
                for s in stages), "missing matching completed packet marker")
    require(result == {**packet["evidence"], "status": "verified"}, "completed result mismatch")
    require(packet["evidence"]["status"] == "checking", "unexpected prepared status")
    require(result["candidate_commit"] == CANDIDATE and result["node"] == "root", "result identity mismatch")
    require(result["root_contract_commit"] == FROZEN_SOURCE, "frozen source mismatch")
    require(result["theorem"] == "HeckeEis.eichlerShimuraMap_injective", "root name mismatch")
    require(len(set(result["checked_theorems"])) == len(result["checked_theorems"]) == 57,
            "unexpected checked declaration set")
    require(set(result["permitted_axioms"]) == {"propext", "Quot.sound", "Classical.choice"},
            "unexpected permitted axioms")
    require(sha((ROOT / "checker-source.py.txt").read_bytes()) == result["verifier_sha256"],
            "checker source identity mismatch")
    sources = packet["source_sha256"]
    require(set(receipt["files"]) == set(sources) | {"prepared.json", "evidence.json"},
            "export file set mismatch")
    for name in ("prepared.json", "evidence.json"):
        require(sha((ROOT / name).read_bytes()) == receipt["files"][name], f"export hash mismatch: {name}")
    revision_matches = 0
    with tarfile.open(ROOT / "inputs.tar.gz", "r:gz") as archive:
        members = archive.getmembers()
        require(len(members) == len(sources) and {m.name for m in members} == set(sources),
                "archive file set mismatch")
        for member in members:
            parts = PurePosixPath(member.name).parts
            require(member.isfile() and len(parts) > 1 and parts[0] in {"challenge", "solution"}
                    and not any(p in {"..", ".lake"} for p in parts)
                    and member.name.endswith(".lean") and parts[-1] != "lakefile.lean",
                    "unexpected archive member")
            data = archive.extractfile(member).read()  # Read bytes; do not extract into the worktree.
            require(sha(data) == sources[member.name] == receipt["files"][member.name],
                    f"input hash mismatch: {member.name}")
            side, relative = member.name.split("/", 1)
            if member.name == "challenge/Challenge.lean":
                frozen = git_file(FROZEN_SOURCE, "Fermat/Thm_HeckeEis_eichlerShimuraMap_injective.lean")
                require(data.startswith(frozen.rstrip()), "root challenge contract mismatch")
            elif member.name == "solution/Solution.lean":
                require(data == b"import Submission\n", "solution entrypoint mismatch")
            else:
                revision = result["base_commit"] if side == "challenge" else CANDIDATE
                require(data == git_file(revision, relative), f"Git source mismatch: {member.name}")
                revision_matches += 1
    print(json.dumps({
        "audit": "existing evidence integrity only; no comparator rerun or proof acceptance",
        "request_id": REQUEST, "verified_candidate": CANDIDATE, "returncode": response["returncode"],
        "packet_digest": PACKET_DIGEST, "source_files_checked": len(sources),
        "source_files_matched_to_git": revision_matches,
        "checker_sha256": result["verifier_sha256"],
        "reference_cache_digest": result["reference_cache_digest"],
        "checked_declarations": len(result["checked_theorems"]),
    }, indent=2))


if __name__ == "__main__":
    main()
