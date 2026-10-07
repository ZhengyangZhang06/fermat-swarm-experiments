import ctypes.util
import importlib.util
from pathlib import Path
import platform
import subprocess
import sys
import unittest
from unittest.mock import patch


SOURCE = Path(__file__).resolve().parents[1] / "scripts/swarm-verifier-selftest.py"
SPEC = importlib.util.spec_from_file_location("swarm_verifier_selftest", SOURCE)
PROBE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(PROBE)


class VerifierProbeTests(unittest.TestCase):
    def test_candidate_arguments_are_rejected_before_loading_verifier(self):
        with patch.object(sys, "argv", [str(SOURCE), "/tmp/candidate"]):
            with self.assertRaisesRegex(SystemExit, "candidate arguments are forbidden"):
                PROBE.main()

    def test_root_execution_is_rejected_before_loading_verifier(self):
        with patch.object(sys, "argv", [str(SOURCE)]), patch.object(PROBE.os, "geteuid", return_value=0):
            with self.assertRaisesRegex(SystemExit, "unprivileged"):
                PROBE.main()

    def test_unsupported_architecture_fails_closed(self):
        with patch.object(PROBE.platform, "machine", return_value="unsupported"):
            with self.assertRaisesRegex(RuntimeError, "only on x86_64"):
                PROBE.deny_sockets()

    @unittest.skipUnless(platform.system() == "Linux" and platform.machine() == "x86_64"
                         and ctypes.util.find_library("seccomp"), "requires Linux x86_64 libseccomp")
    def test_inherited_filter_denies_unix_inet_and_socketpair(self):
        code = (
            "import errno,socket\n"
            "for op in [lambda:socket.socket(socket.AF_UNIX),"
            "lambda:socket.socket(socket.AF_INET),lambda:socket.socketpair()]:\n"
            " try: op()\n"
            " except OSError as e: assert e.errno == errno.EPERM\n"
            " else: raise SystemExit('socket unexpectedly allowed')\n"
        )
        subprocess.run([sys.executable, "-c", code], check=True, timeout=10,
                       preexec_fn=PROBE.deny_sockets)


if __name__ == "__main__":
    unittest.main()
