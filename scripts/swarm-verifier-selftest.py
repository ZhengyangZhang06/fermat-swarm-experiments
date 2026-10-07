#!/usr/bin/env python3
"""Credential-free, fixed-fixture verifier feasibility test for an idle node.

This is NOT a proof worker or an acceptance endpoint. It accepts no candidate
input and has no broker/runtime callers. Run in a disposable unprivileged
container with only the pinned tools and these two scripts mounted read-only.
The ten existing comparator fixtures are reused without changing their gates.
"""

from __future__ import annotations

import ctypes
import errno
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import platform
import subprocess
import sys
import tempfile
import time


def deny_sockets():
    """Install an inherited seccomp filter; fail closed if unsupported.

    Landlock on older kernels does not mediate pathname Unix sockets. Unlike
    the manager's systemd AF_UNIX filter, this diagnostic denies ALL creation
    of sockets. No network or IPC is needed by these local verifier fixtures.
    libseccomp's default bad-architecture action also prevents ABI escapes.
    """
    if platform.machine() != "x86_64":
        raise RuntimeError("diagnostic seccomp policy is tested only on x86_64")
    seccomp = ctypes.CDLL("libseccomp.so.2", use_errno=True)
    seccomp.seccomp_init.argtypes = [ctypes.c_uint32]
    seccomp.seccomp_init.restype = ctypes.c_void_p
    seccomp.seccomp_syscall_resolve_name.argtypes = [ctypes.c_char_p]
    seccomp.seccomp_syscall_resolve_name.restype = ctypes.c_int
    seccomp.seccomp_rule_add.argtypes = [
        ctypes.c_void_p, ctypes.c_uint32, ctypes.c_int, ctypes.c_uint,
    ]
    seccomp.seccomp_rule_add.restype = ctypes.c_int
    seccomp.seccomp_load.argtypes = [ctypes.c_void_p]
    seccomp.seccomp_load.restype = ctypes.c_int
    seccomp.seccomp_release.argtypes = [ctypes.c_void_p]
    context = seccomp.seccomp_init(0x7FFF0000)  # SCMP_ACT_ALLOW
    if not context:
        raise RuntimeError("seccomp_init failed")
    try:
        for name in (b"socket", b"socketpair"):
            number = seccomp.seccomp_syscall_resolve_name(name)
            if number < 0 or seccomp.seccomp_rule_add(
                context, 0x00050000 | errno.EPERM, number, 0,
            ) != 0:
                raise RuntimeError("cannot install socket-denial rule")
        if seccomp.seccomp_load(context) != 0:
            raise RuntimeError("seccomp_load failed")
    finally:
        seccomp.seccomp_release(context)


def load_verifier(path):
    spec = importlib.util.spec_from_file_location("frozen_verifier", path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def isolated_command(verifier, directory, args, *, lean_path="", capture=False):
    environment = {**verifier.ENV, "LEAN_PATH": lean_path,
                   "LEAN_ABORT_ON_PANIC": "1"}
    command = [
        str(verifier.TOOLS / "landrun"), "--best-effort",
        "--ro", "/etc", "--rox", "/usr", "--ro", str(directory),
        "--rox", str(verifier.TOOLS), "--rw", "/dev", "-ldd", "-add-exec",
        "--rwx", str(directory / ".lake"), "--rox", str(verifier.LEAN.parent),
    ]
    for key in ("PATH", "HOME", "LEAN_PATH", "LEAN_ABORT_ON_PANIC", "LEAN_NUM_THREADS"):
        command.extend(["--env", key])
    command.extend(["--", *map(str, args)])
    return subprocess.run(command, cwd=directory, env=environment, check=True,
                          text=True, close_fds=True, preexec_fn=deny_sockets,
                          stdout=subprocess.PIPE if capture else None)


def isolation_tests(verifier, root):
    candidate = root / "canary-candidate"
    verifier.configure(candidate, mathlib=False)
    outside = root / "private-canary"
    verifier.write(outside, "must not be visible to candidate code")
    probe = (
        "import errno,pathlib,socket,sys\n"
        "try: pathlib.Path(sys.argv[1]).read_text()\n"
        "except PermissionError: pass\n"
        "else: raise SystemExit('private file exposed')\n"
        "for op in [lambda: socket.socket(socket.AF_UNIX),"
        "lambda: socket.socket(socket.AF_INET),lambda: socket.socketpair()]:\n"
        " try: op()\n"
        " except OSError as e: assert e.errno == errno.EPERM, repr(e)\n"
        " else: raise SystemExit('socket creation allowed')\n"
        "print('PRIVATE_FILE_AND_SOCKETS_DENIED')\n"
    )
    result = verifier.sandbox(candidate, [sys.executable, "-c", probe, outside], capture=True)
    if result.stdout.strip() != "PRIVATE_FILE_AND_SOCKETS_DENIED":
        raise RuntimeError("missing isolation test evidence")
    print(result.stdout.strip(), flush=True)


def main():
    if len(sys.argv) != 1:
        raise SystemExit("Fixed self-test only; candidate arguments are forbidden")
    if os.geteuid() == 0:
        raise SystemExit("Run this diagnostic as an unprivileged container user")
    started = time.monotonic()
    source = Path(__file__).with_name("verify-frozen-node.py")
    with tempfile.TemporaryDirectory(prefix="fermat-verifier-node-selftest-") as tmp:
        root = Path(tmp)
        os.environ["FERMAT_VERIFIER_PROJECT"] = str(root)
        verifier = load_verifier(source)
        verifier.sandbox = lambda directory, args, **kw: isolated_command(
            verifier, directory, args, **kw)
        print(json.dumps({"stage": "diagnostic-start", "kernel": platform.release(),
                          "uid": os.geteuid(), "verifier_sha256": hashlib.sha256(source.read_bytes()).hexdigest()}), flush=True)
        isolation_tests(verifier, root)
        verifier.self_test()
        print(json.dumps({"stage": "diagnostic-passed", "comparator_cases": 10,
                          "elapsed_seconds": round(time.monotonic() - started, 2),
                          "production_acceptance_enabled": False}), flush=True)


if __name__ == "__main__":
    main()
