#!/usr/bin/env python3
"""Credential-free readiness probe, NOT an issue resolver or proof check.

Run once per node as a Swarm global-job with only the toolchain and benchmark
directories mounted read-only. No authentication or Docker socket is needed.
"""
from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess


def probe() -> dict:
    benchmark = Path("/benchmark")
    lean = Path("/toolchain/bin/lean")
    result = {
        "kind": "readiness-only",
        "node": os.environ.get("PREFLIGHT_NODE", "unknown"),
        "model_started": False,
        "credentials_mounted": False,
        "python": shutil.which("python3"),
        "git": shutil.which("git"),
        "node_binary": shutil.which("node"),
        "codex": shutil.which("codex"),
    }
    try:
        manifest = (benchmark / "manifest.json").read_bytes()
        problems = json.loads(manifest)["problems"]
        result["manifest_sha256"] = hashlib.sha256(manifest).hexdigest()
        result["problem_count"] = len(problems)
        result["contracts_present"] = all(
            (benchmark / problem["file"]).is_file() for problem in problems
        )
        check = subprocess.run(
            [str(lean), "--version"], capture_output=True, text=True, timeout=30
        )
        result["lean_exit"] = check.returncode
        result["lean_version"] = check.stdout.strip()[:300]
        result["lean_error"] = check.stderr.strip()[:300]
        result["ready_for_bootstrap"] = bool(
            result["contracts_present"] and check.returncode == 0
        )
    except (OSError, ValueError, KeyError, subprocess.TimeoutExpired) as exc:
        result["ready_for_bootstrap"] = False
        result["error"] = type(exc).__name__
    return result


if __name__ == "__main__":
    report = probe()
    print(json.dumps(report, sort_keys=True), flush=True)
    raise SystemExit(0 if report["ready_for_bootstrap"] else 1)
