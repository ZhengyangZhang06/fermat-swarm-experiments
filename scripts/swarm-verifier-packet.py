#!/usr/bin/env python3
"""Verify a controller-prepared packet in a credential-free container.

This receiver is not connected to the broker or to proof acceptance yet. The
operator must supply the expected digest from their private preparation record,
never trust a worker-provided packet merely because it hashes to itself.
"""
from __future__ import annotations

import argparse
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import tempfile


PACKAGES = Path("/mnt/data/zhengyang-workspace/fermat-example/.lake/packages")


def execute(packet_root, expected_digest, output):
    if os.geteuid() == 0:
        raise RuntimeError("packet verification requires an unprivileged user")
    if not re.fullmatch(r"[a-f0-9]{64}", expected_digest):
        raise ValueError("invalid controller packet digest")
    source = Path(__file__).with_name("swarm-verifier-selftest.py")
    spec = importlib.util.spec_from_file_location("container_verifier_launcher", source)
    launcher = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(launcher)
    with tempfile.TemporaryDirectory(prefix="registered-verifier-project-") as tmp:
        project = Path(tmp)
        (project / ".lake").mkdir()
        (project / ".lake/packages").symlink_to(PACKAGES)
        os.environ["FERMAT_VERIFIER_PROJECT"] = str(project)
        verifier = launcher.load_verifier(source.with_name("verify-frozen-node.py"))
        verifier.sandbox = lambda directory, args, **kw: launcher.isolated_command(
            verifier, directory, args, **kw)
        # Validate before copying or running any Lean code. Only the exact
        # source allowlist is copied, never unlisted config/build artifacts.
        packet = verifier.validate_prepared(packet_root, expected_digest)
        output.mkdir(parents=True, exist_ok=False)
        for name in [*packet["source_sha256"], "prepared.json", "evidence.json"]:
            destination = output / name
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(packet_root / name, destination)
        print(json.dumps({"stage": "packet-validated", "digest": expected_digest,
                          "candidate_commit": packet["evidence"]["candidate_commit"],
                          "node": packet["evidence"]["node"]}), flush=True)
        verifier.verify_prepared(output, expected_digest)
        # The controller must correlate this with a successful terminal task,
        # the immutable packet and trusted result evidence, not stdout alone.
        print(json.dumps({"stage": "packet-verified", "digest": expected_digest}), flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--packet", type=Path, required=True)
    parser.add_argument("--digest", required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    execute(args.packet, args.digest, args.output)
