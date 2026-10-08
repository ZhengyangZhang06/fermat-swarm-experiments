"""Synthetic transport tests only: no Lean proof or real verifier is executed."""

import copy
import importlib.util
import json
import os
from pathlib import Path
import sqlite3
import stat
import tempfile
import unittest


SPEC = importlib.util.spec_from_file_location(
    "failed_export", Path(__file__).with_name("export_failed_request.py")
)
exporter = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(exporter)


def encoded(value):
    return (json.dumps(value, indent=2) + "\n").encode()


class FailedExportTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name)
        self.request_id = "1" * 32
        self.candidate = "2" * 40
        self.operation_root = self.root / "operations" / self.request_id
        self.prepared = self.operation_root / "prepared/packet"
        self.result = self.operation_root / "output/result"
        self.destination = self.root / "diagnostic-exports"
        self.destination.mkdir()
        self.reference = self.root / "reference.json"
        self.reference.write_bytes(encoded({"schema": 1, "toolchain": "v4.33.1", "files": {}}))
        codes = {}
        for name in exporter.CHECKERS:
            path = self.operation_root / "code" / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text("# synthetic checker identity: " + name + "\n")
            codes[name] = exporter.sha256(path.read_bytes())
        sources = {}
        for name in ("challenge/Challenge.lean", "solution/Solution.lean"):
            data = b"-- synthetic transport fixture, not a Lean proof\n"
            for side in (self.prepared, self.result):
                path = side / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(data)
            sources[name] = exporter.sha256(data)
        cache = exporter.sha256(self.reference.read_bytes())
        self.packet = {
            "schema": 1,
            "evidence": {"status": "checking", "candidate_commit": self.candidate,
                         "node": "root.fixture", "root_contract_commit": "3" * 40,
                         "lean_toolchain": "v4.33.1", "reference_cache_digest": cache,
                         "verifier_sha256": codes["verify-frozen-node.py"]},
            "source_sha256": sources,
            "dependency_manifest": {},
        }
        self.operation = {
            "state": "terminal", "returncode": 1, "request_id": self.request_id,
            "candidate_commit": self.candidate, "packet": str(self.prepared),
            "service_id": "s" * 25, "task_id": "t" * 25, "node_id": "n" * 25,
            "task_status": {"State": "failed", "ContainerStatus": {"ExitCode": 1, "PID": 0}},
            "code_sha256": codes, "reference_cache_digest": cache,
        }
        self.seal()
        self.log = self.root / "terminal.log"
        self.log.write_text("synthetic challenge build failure\n")
        self.database = self.root / "claims.sqlite"
        self.request = {"revision": self.candidate, "node_id": "root.fixture",
                        "source_commit": "3" * 40,
                        "claim_token": "SYNTHETIC_PRIVATE_FIELD_DO_NOT_EXPORT"}
        with sqlite3.connect(self.database) as db:
            db.execute("CREATE TABLE verifications (id TEXT PRIMARY KEY, state TEXT, "
                       "returncode INTEGER, request TEXT, log TEXT)")
            db.execute("INSERT INTO verifications VALUES (?, ?, ?, ?, ?)",
                       (self.request_id, "finished", 1, json.dumps(self.request), str(self.log)))

    def tearDown(self):
        for path in self.root.rglob("*"):
            if path.is_dir() and not path.is_symlink():
                path.chmod(0o700)
        self.temp.cleanup()

    def seal(self):
        self.digest = exporter.canonical_digest(self.packet)
        self.operation["packet_digest"] = self.digest
        for root in (self.prepared, self.result):
            (root / "prepared.json").write_bytes(encoded(self.packet))
            (root / "evidence.json").write_bytes(encoded(self.packet["evidence"]))
        (self.operation_root / "operation.json").write_bytes(encoded(self.operation))

    def collect(self):
        return exporter.collect(self.database, self.operation_root, self.request_id,
                                self.candidate, self.digest, self.reference)

    def test_failed_export_preserves_private_bytes_and_verdict(self):
        originals = {p: p.read_bytes() for p in self.root.rglob("*") if p.is_file()}
        (self.result / "unlisted-private.txt").write_text("DO_NOT_COPY_AUXILIARY")
        artifacts = self.collect()
        manifest = json.loads(artifacts["diagnostic-export.json"])
        self.assertFalse(manifest["acceptance"])
        self.assertEqual(manifest["returncode"], 1)
        self.assertEqual(json.loads(artifacts["evidence.json"])["status"], "checking")
        self.assertEqual(artifacts["operation.json"], originals[self.operation_root / "operation.json"])
        self.assertIn("config.json", manifest["generated_configuration_absent"])
        self.assertFalse(manifest["reference_inventory_contents_rechecked"])
        for name, digest in manifest["files"].items():
            self.assertEqual(exporter.sha256(artifacts[name]), digest)
        for marker in (b"SYNTHETIC_PRIVATE_FIELD_DO_NOT_EXPORT", b"DO_NOT_COPY_AUXILIARY"):
            self.assertNotIn(marker, b"".join(artifacts.values()))
        self.assertNotIn("review-export.json", artifacts)
        self.assertTrue(all(p.read_bytes() == data for p, data in originals.items()))

    def test_nonterminal_and_successful_requests_are_rejected(self):
        for state, code in (("queued", None), ("running", None), ("uncertain", 75), ("finished", 0)):
            with self.subTest(state=state, code=code):
                with sqlite3.connect(self.database) as db:
                    db.execute("UPDATE verifications SET state=?,returncode=?", (state, code))
                with self.assertRaises(ValueError):
                    self.collect()

    def test_operation_identity_mismatches_are_rejected(self):
        original = copy.deepcopy(self.operation)
        for key, value in (("request_id", "9" * 32), ("candidate_commit", "9" * 40),
                           ("packet_digest", "9" * 64), ("state", "verified"), ("returncode", 0)):
            with self.subTest(key=key):
                changed = {**original, key: value}
                (self.operation_root / "operation.json").write_bytes(encoded(changed))
                with self.assertRaises(ValueError):
                    self.collect()

    def test_terminal_status_mismatch_is_rejected(self):
        self.operation["task_status"]["ContainerStatus"]["PID"] = 42
        self.seal()
        with self.assertRaisesRegex(ValueError, "terminal container"):
            self.collect()

    def test_hash_tampering_is_rejected(self):
        paths = [self.prepared / "challenge/Challenge.lean", self.result / "solution/Solution.lean",
                 self.result / "prepared.json", self.operation_root / "code/verify-frozen-node.py",
                 self.reference]
        for path in paths:
            with self.subTest(path=path):
                original = path.read_bytes()
                path.write_bytes(original + b" ")
                with self.assertRaises(ValueError):
                    self.collect()
                path.write_bytes(original)

    def test_packet_cannot_change_frozen_identity_even_when_rehashed(self):
        original = copy.deepcopy(self.packet)
        for key, value in (("node", "root.other"), ("root_contract_commit", "9" * 40),
                           ("candidate_commit", "9" * 40), ("verifier_sha256", "9" * 64)):
            with self.subTest(key=key):
                self.packet = copy.deepcopy(original)
                self.packet["evidence"][key] = value
                self.seal()
                with self.assertRaises(ValueError):
                    self.collect()

    def test_result_cannot_be_relabeled_verified(self):
        (self.result / "evidence.json").write_bytes(encoded({**self.packet["evidence"], "status": "verified"}))
        with self.assertRaisesRegex(ValueError, "relabeled"):
            self.collect()

    def test_unlisted_lean_source_is_rejected(self):
        for name in ("challenge/Extra.lean", "challenge/Nested/lakefile.lean"):
            with self.subTest(name=name):
                path = self.result / name
                path.parent.mkdir(exist_ok=True)
                path.write_text("-- extra\n")
                with self.assertRaisesRegex(ValueError, "inventory mismatch"):
                    self.collect()
                path.unlink()

    def test_links_and_traversal_are_rejected(self):
        for name in ("../secret.lean", "/secret.lean", "challenge/../secret.lean",
                     "challenge//X.lean", "challenge/.lake/X.lean", "challenge/lakefile.lean"):
            with self.subTest(name=name), self.assertRaises(ValueError):
                exporter.source_name(name)
        source = self.result / "solution/Solution.lean"
        source.unlink()
        source.symlink_to(self.prepared / "solution/Solution.lean")
        with self.assertRaisesRegex(ValueError, "symlink"):
            self.collect()

    def test_checker_inventory_cannot_export_arbitrary_files(self):
        self.operation["code_sha256"]["private.key"] = "0" * 64
        self.seal()
        with self.assertRaisesRegex(ValueError, "checker inventory"):
            self.collect()

    def test_configuration_is_distinguished_from_receipt_bound_sources(self):
        data = b"-- generated configuration fixture\n"
        (self.result / "challenge/lakefile.lean").write_bytes(data)
        artifacts = self.collect()
        manifest = json.loads(artifacts["diagnostic-export.json"])
        self.assertEqual(artifacts["challenge/lakefile.lean"], data)
        self.assertIn("challenge/lakefile.lean", manifest["generated_configuration_captured_not_receipt_bound"])

    def test_readonly_publication_is_idempotent_and_refuses_overwrite(self):
        artifacts = self.collect()
        target = exporter.publish(artifacts, self.destination, self.request_id)
        self.assertEqual(exporter.publish(artifacts, self.destination, self.request_id), target)
        for name, data in artifacts.items():
            self.assertEqual((target / name).read_bytes(), data)
            self.assertEqual(stat.S_IMODE((target / name).stat().st_mode), 0o444)
        self.assertEqual(stat.S_IMODE(target.stat().st_mode), 0o555)
        changed = {**artifacts, "terminal.log": b"changed verdict"}
        with self.assertRaisesRegex(ValueError, "bytes differ"):
            exporter.publish(changed, self.destination, self.request_id)
        self.assertEqual((target / "terminal.log").read_bytes(), artifacts["terminal.log"])

    def test_existing_export_with_writable_file_is_rejected(self):
        artifacts = self.collect()
        target = exporter.publish(artifacts, self.destination, self.request_id)
        (target / "terminal.log").chmod(0o644)
        with self.assertRaisesRegex(ValueError, "permissions differ"):
            exporter.publish(artifacts, self.destination, self.request_id)

    def test_existing_export_with_special_file_is_rejected(self):
        artifacts = self.collect()
        target = exporter.publish(artifacts, self.destination, self.request_id)
        target.chmod(0o755)
        os.mkfifo(target / "unlisted-fifo")
        target.chmod(0o555)
        with self.assertRaisesRegex(ValueError, "special file"):
            exporter.publish(artifacts, self.destination, self.request_id)


if __name__ == "__main__":
    unittest.main()
