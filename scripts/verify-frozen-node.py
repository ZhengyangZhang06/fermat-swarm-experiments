"""Verify a frozen theorem using isolated exports and the official Lean comparator.

Challenge and candidate sources live in separate sandboxes so a candidate cannot
change declarations shared by the frozen contract. The comparator's existing
verifyMatch performs statement/context equality, axiom checks and kernel replay.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import subprocess
import tempfile
from pathlib import Path

PROJECT = Path(os.environ["FERMAT_VERIFIER_PROJECT"]).resolve()
# These are controller-owned pinned binaries, never candidate-provided paths.
VERIFIER_BASE = Path("/mnt/data/zhengyang-workspace/fermat-example/.humanize")
TOOLS = VERIFIER_BASE / "verifier"
LEAN = VERIFIER_BASE / "toolchains/lean-4.33.1-linux/bin"
AXIOMS = ["propext", "Quot.sound", "Classical.choice"]
PRIMITIVES = [
    "Nat.add",
    "Nat.sub",
    "Nat.mul",
    "Nat.pow",
    "Nat.gcd",
    "Nat.div",
    "Nat.mod",
    "Nat.beq",
    "Nat.ble",
    "Nat.land",
    "Nat.lor",
    "Nat.xor",
    "Nat.shiftLeft",
    "Nat.shiftRight",
    "String.ofList",
    "Char.ofNat",
    "List",
    "eagerReduce",
]
ENV = {**os.environ, "PATH": f"{LEAN}:{os.environ['PATH']}", "LEAN_NUM_THREADS": "2"}


def run(args, cwd, *, capture=False):
    return subprocess.run(
        list(map(str, args)),
        cwd=cwd,
        env=ENV,
        text=True,
        check=True,
        stdout=subprocess.PIPE if capture else None,
    )


def git(repo, *args):
    return run(["git", "-C", repo, *args], repo, capture=True).stdout


def write(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(value, encoding="utf-8")


def copy_revision(repo, revision, target):
    for name in git(repo, "ls-tree", "-r", "--name-only", revision).splitlines():
        if name.endswith(".lean") and name != "lakefile.lean":
            write(target / name, git(repo, "show", f"{revision}:{name}"))


def check_dependency_sources(packages_dir, manifest):
    """Check pinned source revisions; generated ignored build artifacts are allowed."""
    revisions = {}
    for package in manifest["packages"]:
        name = package["name"]
        if package["type"] != "git" or not re.fullmatch(r"[A-Za-z0-9_-]+", name):
            raise RuntimeError(f"unsupported frozen dependency: {name}")
        checkout = packages_dir / name
        actual = git(checkout, "rev-parse", "HEAD").strip()
        if actual != package["rev"]:
            raise RuntimeError(f"dependency revision changed: {name}")
        if git(checkout, "status", "--porcelain").strip():
            raise RuntimeError(f"dependency source checkout is not clean: {name}")
        revisions[name] = actual
    return revisions


def configure(directory, *, mathlib=True):
    roots = sorted(
        {
            p.relative_to(directory).parts[0].removesuffix(".lean")
            for p in directory.rglob("*.lean")
            if ".lake" not in p.parts
        }
    )
    if any(not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", root) for root in roots):
        raise RuntimeError("unsupported Lean module name in verifier input")
    write(
        directory / "lakefile.lean",
        # These are the frozen project's elaboration options, not candidate input.
        "import Lake\nopen Lake DSL\npackage verification where\n"
        "  leanOptions := #[\n"
        "    ⟨`autoImplicit, false⟩,\n"
        "    ⟨`maxHeartbeats, (4000000 : Nat)⟩,\n"
        "    ⟨`synthInstance.maxHeartbeats, (400000 : Nat)⟩,\n"
        "    ⟨`backward.isDefEq.respectTransparency.types, false⟩\n"
        "  ]\n\n" + "".join(f"lean_lib {root}\n" for root in roots),
    )
    write(directory / "lean-toolchain", "leanprover/lean4:v4.33.1\n")
    write(
        directory / "lake-manifest.json",
        json.dumps(
            {
                "version": "1.2.0",
                "packagesDir": ".lake/packages",
                "packages": [],
                "name": "verification",
                "lakeDir": ".lake",
            }
        ),
    )
    lib = directory / ".lake/build/lib/lean"
    lib.mkdir(parents=True, exist_ok=True)
    if mathlib:
        build_roots = [PROJECT / ".lake/packages/mathlib/.lake/build/lib/lean"]
        build_roots += sorted(
            (PROJECT / ".lake/packages").glob("*/.lake/build/lib/lean")
        )
        for root in build_roots:
            for child in root.iterdir():
                if not (lib / child.name).exists():
                    (lib / child.name).symlink_to(child.resolve())


def sandbox(directory, args, *, lean_path="", capture=False):
    command = [
        "systemd-run",
        "--user",
        "--quiet",
        "--wait",
        "--pipe",
        "--collect",
        "--property=RestrictAddressFamilies=~AF_UNIX",
        f"--working-directory={directory}",
        f"--setenv=PATH={ENV['PATH']}",
        "--setenv=LEAN_ABORT_ON_PANIC=1",
        "--setenv=LEAN_NUM_THREADS=2",
    ]
    if lean_path:
        command.append(f"--setenv=LEAN_PATH={lean_path}")
    command += [
        str(TOOLS / "landrun"),
        "--best-effort",
        "--ro",
        "/etc",
        "--rox",
        "/usr",
        "--ro",
        str(directory),
        "--rox",
        str(TOOLS),
        "--rox",
        str((PROJECT / ".lake/packages").resolve()),
        "--rw",
        "/dev",
        "-ldd",
        "-add-exec",
        "--rwx",
        str(directory / ".lake"),
        "--rox",
        str(LEAN.parent),
        "--env",
        "PATH",
        "--env",
        "HOME",
        "--env",
        "LEAN_PATH",
        "--env",
        "LEAN_ABORT_ON_PANIC",
        "--env",
        "LEAN_NUM_THREADS",
        "--",
        *map(str, args),
    ]
    return run(command, directory, capture=capture)


def export(directory, module, name, destination):
    names = [name] if isinstance(name, str) else name
    sandbox(directory, ["lake", "--no-cache", "build", module])
    lean_path = run(
        ["lake", "env", "printenv", "LEAN_PATH"], directory, capture=True
    ).stdout.strip()
    exporter = TOOLS / "lean4export/.lake/build/bin/lean4export"
    exported = sandbox(
        directory,
        [exporter, module, "--", *names, *AXIOMS, *PRIMITIVES],
        lean_path=lean_path,
        capture=True,
    ).stdout
    write(destination, exported)


def compare(root, name, *, mathlib=True):
    names = [name] if isinstance(name, str) else name
    challenge, solution = root / "challenge", root / "solution"
    configure(challenge, mathlib=mathlib)
    configure(solution, mathlib=mathlib)
    export(challenge, "Challenge", name, root / "challenge.export")
    export(solution, "Solution", name, root / "solution.export")
    config = {
        "challenge_module": "Challenge",
        "solution_module": "Solution",
        "theorem_names": names,
        "permitted_axioms": AXIOMS,
        "enable_nanoda": False,
    }
    write(root / "config.json", json.dumps(config, indent=2))
    run(
        [
            TOOLS / "comparator/.lake/build/bin/comparator",
            root / "config.json",
            "--exports",
            root / "challenge.export",
            root / "solution.export",
        ],
        solution,
    )


def self_test():
    ordinary_challenge = "theorem toy : True := by sorry\n"
    for title, challenge, candidate, accepted in [
        ("valid", ordinary_challenge, "theorem toy : True := True.intro", True),
        (
            "changed-type",
            ordinary_challenge,
            "theorem toy : False → False := fun h => h",
            False,
        ),
        ("sorry", ordinary_challenge, "theorem toy : True := by sorry", False),
        (
            "extra-axiom",
            ordinary_challenge,
            "axiom assumed : True\ntheorem toy : True := assumed",
            False,
        ),
        (
            "shared-definition",
            "def ContractProp : Prop := True\ntheorem toy : ContractProp := by sorry",
            "def ContractProp : Prop := True\ntheorem toy : ContractProp := True.intro",
            True,
        ),
        (
            "changed-definition",
            "def ContractProp : Prop := False\ntheorem toy : ContractProp := by sorry",
            "def ContractProp : Prop := True\ntheorem toy : ContractProp := True.intro",
            False,
        ),
    ]:
        with tempfile.TemporaryDirectory(prefix="deuring-comparator-test-") as tmp:
            root = Path(tmp)
            write(root / "challenge/Challenge.lean", challenge + "\n")
            write(root / "solution/Solution.lean", candidate + "\n")
            try:
                compare(root, "toy", mathlib=False)
                result = True
            except subprocess.CalledProcessError:
                result = False
            if result != accepted:
                raise RuntimeError(f"comparator self-test failed: {title}")
            print(
                f"SELF-TEST {title}: {'accepted' if result else 'rejected'}", flush=True
            )
    # A valid root cannot hide a missing/renamed or unproved child interface.
    for title, child, accepted in [
        ("combined-valid", "theorem Child : True := True.intro", True),
        ("combined-renamed", "theorem Wrong.Child : True := True.intro", False),
        ("combined-sorry", "theorem Child : True := by sorry", False),
        ("combined-changed-type", "theorem Child : False → False := fun h => h", False),
    ]:
        with tempfile.TemporaryDirectory(prefix="deuring-combined-test-") as tmp:
            root = Path(tmp)
            write(root / "challenge/Challenge.lean", ordinary_challenge + "theorem Child : True := by sorry\n")
            write(root / "solution/Solution.lean", "theorem toy : True := True.intro\n" + child + "\n")
            try:
                compare(root, ["toy", "Child"], mathlib=False)
                result = True
            except subprocess.CalledProcessError:
                result = False
            if result != accepted:
                raise RuntimeError(f"comparator self-test failed: {title}")
            print(f"SELF-TEST {title}: {'accepted' if result else 'rejected'}", flush=True)


def sandbox_self_test():
    """Prove the checker cannot read a file outside its explicit sandbox roots."""
    with tempfile.TemporaryDirectory(prefix="fermat-sandbox-test-") as tmp:
        root = Path(tmp)
        outside = root / "private-canary"
        write(outside, "must not be visible to candidate code")
        candidate = root / "candidate"
        configure(candidate, mathlib=False)
        command = ["/usr/bin/python3", "-c",
                   "import pathlib,sys\n"
                   "try: pathlib.Path(sys.argv[1]).read_text()\n"
                   "except PermissionError: print('SANDBOX_CANARY_DENIED'); sys.exit(0)\n"
                   "raise SystemExit('sandbox exposed private canary')\n", str(outside)]
        result = sandbox(candidate, command, capture=True)
        if "SANDBOX_CANARY_DENIED" not in result.stdout:
            raise RuntimeError("sandbox canary check did not produce rejection evidence")
        print("SELF-TEST private-files: denied", flush=True)


def root_child_contracts(dag, root_id):
    """Collect the frozen interfaces of every retained prerequisite in the DAG."""
    nodes = {one["id"]: one for one in dag["nodes"]}
    found = {}
    pending = [root_id]
    visited = set()
    while pending:
        node_id = pending.pop()
        if node_id in visited:
            continue
        visited.add(node_id)
        record = nodes[node_id]
        pending.extend(record.get("children", []))
        pending.extend(record.get("depends_on", []))
        if node_id == root_id:
            continue
        if record["status"] not in ("proved", "integrating"):
            raise RuntimeError(f"root prerequisite is not accepted: {node_id}")
        name = f"Submission.{record['lean_name']}"
        if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_'.]*", name):
            raise RuntimeError("invalid frozen child Lean name")
        if name in found:
            raise RuntimeError(f"duplicate child interface: {name}")
        found[name] = record["lean_statement"]
    return dict(sorted(found.items()))


def child_challenge(contract, name, statement):
    """Restore declared universe names, which do not cross Lean import boundaries.

    Use only declarations from the controller-validated frozen source, never
    candidate options or assumptions. This does not normalize build directives.
    """
    universes = []
    for line in contract.splitlines():
        if line.startswith("universe "):
            if not re.fullmatch(r"universe(?: [A-Za-z_][A-Za-z0-9_']*)+\s*", line):
                raise RuntimeError("unsupported frozen universe declaration")
            universes.append(line.strip())
    prefix = "import Submission\n"
    if universes:
        prefix += "\n".join(universes) + "\n"
    return prefix + f"theorem {name} : {statement} := by\n  sorry"


def source_hashes(root):
    """Hash the complete prepared Lean source trees, before generated build files.

    Preparation writes regular files only. Refuse links instead of following
    them across the controller's input boundary. Build outputs are deliberately
    not an input to this digest and must not be accepted as source evidence.
    """
    result = {}
    for side in ("challenge", "solution"):
        directory = root / side
        if directory.is_symlink() or not directory.is_dir():
            raise RuntimeError("prepared source directory is missing or a link")
        for path in sorted(directory.rglob("*")):
            relative = path.relative_to(directory)
            if ".lake" in relative.parts:
                continue
            if path.is_symlink():
                raise RuntimeError("prepared source contains a symlink")
            if path.is_file() and path.suffix == ".lean" and relative != Path("lakefile.lean"):
                result[path.relative_to(root).as_posix()] = hashlib.sha256(path.read_bytes()).hexdigest()
    if "challenge/Challenge.lean" not in result or "solution/Solution.lean" not in result:
        raise RuntimeError("prepared theorem entrypoints are missing")
    return result


def prepared_digest(packet):
    return hashlib.sha256(json.dumps(packet, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def validate_prepared(root, expected_digest):
    """Validate a controller-pinned packet; a digest supplied by a worker is not trust.

    This checks transport integrity only, not proof correctness. The caller must
    still run compare(), axiom reporting, and dependency/tool integrity checks.
    """
    root = Path(root)
    packet_path = root / "prepared.json"
    if packet_path.is_symlink():
        raise RuntimeError("prepared packet is a symlink")
    packet = json.loads(packet_path.read_text())
    if packet.get("schema") != 1 or prepared_digest(packet) != expected_digest:
        raise RuntimeError("prepared packet differs from controller digest")
    if source_hashes(root) != packet["source_sha256"]:
        raise RuntimeError("prepared sources differ from controller snapshot")
    if hashlib.sha256(Path(__file__).read_bytes()).hexdigest() != packet["evidence"]["verifier_sha256"]:
        raise RuntimeError("prepared verifier identity changed")
    if packet["evidence"]["status"] != "checking":
        raise RuntimeError("prepared packet is not an unverified input")
    evidence_path = root / "evidence.json"
    if evidence_path.is_symlink() or json.loads(evidence_path.read_text()) != packet["evidence"]:
        raise RuntimeError("prepared evidence differs from controller snapshot")
    return packet


def prepare_verification():
    """Freeze controller-validated inputs without compiling or accepting a proof.

    The existing local entrypoint immediately verifies this packet. A future
    dispatcher may transport it with its controller-retained digest; nothing
    calls that remote path yet. Original contract text is never normalized here.
    """
    run_root = Path(os.environ["HUMANIZE_RUN_DIR"]).resolve()
    if not run_root.is_relative_to(PROJECT / ".humanize"):
        raise RuntimeError("run directory is outside the registered project")
    node_id = os.environ["HUMANIZE_NODE_ID"]
    context = json.loads((run_root / "github-workflow.json").read_text())
    # The service supplies these from its private operator-owned registry, not
    # from a worker request or editable problem config. They pin the original goal.
    if context["source_commit"] != os.environ["FERMAT_FROZEN_SOURCE"]:
        raise RuntimeError("original frozen source revision changed")
    if context["root_lean_name"] != os.environ["FERMAT_ROOT_NAME"]:
        raise RuntimeError("original theorem identity changed")
    expected_contract = git(PROJECT, "show", f"{context['source_commit']}:{os.environ['FERMAT_CONTRACT_FILE']}")
    if context["contract"].strip() != expected_contract.strip():
        raise RuntimeError("original frozen Lean contract changed")
    manifest = json.loads(
        git(PROJECT, "show", f"{context['source_commit']}:lake-manifest.json")
    )
    dependencies = check_dependency_sources(PROJECT / ".lake/packages", manifest)
    verifier_digest = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    dag = json.loads((run_root / "dag.json").read_text())
    node = next(n for n in dag["nodes"] if n["id"] == node_id)
    candidate = Path.cwd()
    revision = git(candidate, "rev-parse", "HEAD").strip()
    if revision != os.environ["FERMAT_CANDIDATE_REVISION"]:
        raise RuntimeError("candidate HEAD differs from the requested immutable revision")
    run(["git", "merge-base", "--is-ancestor", context["source_commit"], revision], candidate)
    if git(candidate, "status", "--porcelain", "--untracked-files=no").strip():
        raise RuntimeError("commit the candidate before verification")
    base = node.get("proof_base_commit") or context["source_commit"]
    name = (
        context["root_lean_name"]
        if node_id == "root"
        else f"Submission.{node['lean_name']}"
    )
    if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_'.]*", name):
        raise RuntimeError("invalid frozen Lean name")
    # Candidates may write their own project worktree, never the verifier's
    # challenge/candidate snapshots or controller evidence while checking.
    output = Path(os.environ["FERMAT_VERIFIER_OUTPUT"]).resolve()
    if output.is_relative_to(PROJECT.parent):
        raise RuntimeError("verifier output must be outside worker-writable projects")
    output.mkdir(parents=True, exist_ok=True)
    root = Path(tempfile.mkdtemp(prefix=f"{node_id.replace('.', '-')}-", dir=output))
    copy_revision(PROJECT, base, root / "challenge")
    copy_revision(candidate, revision, root / "solution")
    if node_id == "root":
        # The exact supplied source ends at the conclusion, without a proof body.
        contract = context["contract"].rstrip()
        if ":=" not in contract:
            contract += " := by\n  sorry"
        children = root_child_contracts(dag, node_id)
        for child_name, child_statement in children.items():
            contract += f"\n\ntheorem {child_name} : {child_statement} := by\n  sorry"
    else:
        contract = child_challenge(context["contract"], name, node['lean_statement'])
    names = [name, *children] if node_id == "root" else [name]
    write(root / "challenge/Challenge.lean", contract + "\n")
    write(root / "solution/Solution.lean", "import Submission\n")
    write(
        root / "evidence.json",
        json.dumps(
            {
                "node": node_id,
                "theorem": name,
                "checked_theorems": names,
                "candidate_commit": revision,
                "base_commit": base,
                "root_contract_commit": context["source_commit"],
                "lean_toolchain": "v4.33.1",
                "permitted_axioms": AXIOMS,
                "dependency_revisions": dependencies,
                "verifier_sha256": verifier_digest,
                "status": "checking",
            },
            indent=2,
        ),
    )
    evidence = json.loads((root / "evidence.json").read_text())
    packet = {"schema": 1, "evidence": evidence, "dependency_manifest": manifest,
              "source_sha256": source_hashes(root)}
    write(root / "prepared.json", json.dumps(packet, sort_keys=True, indent=2))
    # Detect dependency/checker changes during snapshot creation as well as
    # during the later compiler/comparator run.
    if check_dependency_sources(PROJECT / ".lake/packages", manifest) != dependencies:
        raise RuntimeError("dependency revisions changed during preparation")
    digest = prepared_digest(packet)
    validate_prepared(root, digest)
    return root, digest


def verify_prepared(root, digest):
    """Run the original proof gates on the exact controller-prepared input."""
    root = Path(root)
    packet = validate_prepared(root, digest)
    evidence = packet["evidence"]
    manifest, dependencies = packet["dependency_manifest"], evidence["dependency_revisions"]
    if check_dependency_sources(PROJECT / ".lake/packages", manifest) != dependencies:
        raise RuntimeError("prepared dependency revisions changed")
    names = evidence["checked_theorems"]
    compare(root, names)
    # configure() generates only lakefile.lean and .lake content, excluded from
    # source_hashes. Original Lean inputs must still be byte-exact afterward.
    validate_prepared(root, digest)
    write(
        root / "solution/AxiomReport.lean",
        "import Solution\n" + "".join(f"#print axioms {one}\n" for one in names),
    )
    sandbox(root / "solution", ["lake", "env", "lean", "AxiomReport.lean"])
    if check_dependency_sources(PROJECT / ".lake/packages", manifest) != dependencies:
        raise RuntimeError("dependency revisions changed during verification")
    if hashlib.sha256(Path(__file__).read_bytes()).hexdigest() != evidence["verifier_sha256"]:
        raise RuntimeError("verifier source changed during verification")
    evidence = json.loads((root / "evidence.json").read_text())
    evidence["status"] = "verified"
    write(root / "evidence.json", json.dumps(evidence, indent=2))
    print(f"Verification evidence: {root}")


def verify():
    root, digest = prepare_verification()
    verify_prepared(root, digest)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument("--sandbox-self-test", action="store_true")
    args = parser.parse_args()
    if args.sandbox_self_test:
        sandbox_self_test()
    elif args.self_test:
        self_test()
    else:
        verify()
