"""Reproduce this node's build without changing frozen compiler inputs in Git.

This is a local diagnostic, never a proof-acceptance certificate.
"""
import hashlib
import json
import re
import subprocess
import sys
import tempfile
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
OUT = Path(__file__).resolve().parent
POLICY = Path('/runtime/operator-header-policy-v1/policy.json')
LAKE = Path('/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lake')
SELECTED = 'Submission.p09_af497904fe_ff_cyclotomic_supply'
APPROVED = {
    'Submission.p09_af497904fe_cfs_counting_mellin_continuation',
    'Submission.p09_af497904fe_cfs_bounded_euler_logarithm',
    'Submission.p09_af497904fe_cfs_cyclic_weighted_infinitude',
}

def sha(data):
    return hashlib.sha256(data).hexdigest()

def prepare():
    raw = (ROOT / 'Submission.lean').read_bytes()
    source = raw.decode()
    policy_raw = POLICY.read_bytes()
    assert sha(policy_raw) == '96fc18eb6b8cbdad1beec37ca318ab2cf08ac1dda8ebf7cbfe1d6d51abf32f96'
    policy = json.loads(policy_raw)
    entries = next(value for value in policy.values() if isinstance(value, list))
    entry = next(item for item in entries if
                 item['source_commit'] == '20574e45daf714e745af8e649c7b61b21eed5644'
                 and item['contract_file'] == 'Fermat/Thm_GaloisRepAdic_exists_quadraticRelation_forall_of_frobenius.lean')
    assert source.startswith(entry['header'])
    assert sha((ROOT / entry['contract_file']).read_bytes()) == entry['contract_sha256']
    lines = source.splitlines(keepends=True)
    omitted = [{'number': n, 'text': lines[n - 1]} for n in entry['remove_lines']]
    build = ''.join(line for n, line in enumerate(lines, 1) if n not in entry['remove_lines'])
    restored = build.splitlines(keepends=True)
    for item in omitted:
        restored.insert(item['number'] - 1, item['text'])
    assert ''.join(restored).encode() == raw
    scratch = Path(tempfile.mkdtemp(prefix='p09-selected-125510-'))
    (scratch / 'CompilerCopy.lean').write_text(build)
    imports = 'import Mathlib\nimport Definitions.Def_GaloisRep_Adic\n'
    targets = [name for item in omitted for name in item['text'].split('] ', 1)[1].split()]
    probe = imports + 'open Lean in\nrun_cmd do\n  let env ← getEnv\n'
    for target in targets:
        probe += f'  if env.contains `{target} then throwError "policy target unexpectedly present: {target}"\n'
    (scratch / 'HeaderAbsence.lean').write_text(probe)
    declarations = list(re.finditer(r'^theorem (\S+)', build, re.M))
    blocks = {}
    for i, match in enumerate(declarations):
        end = declarations[i + 1].start() if i + 1 < len(declarations) else len(build)
        block = build[match.start():end]
        block = block.removesuffix('open scoped nonZeroDivisors in\nopen Filter Topology Ideal Asymptotics UniqueFactorizationMonoid in\n/-- Speculative parent draft. The arithmetic input obligation at the end is still open. -/\n')
        blocks[match.group(1)] = block
    direct = set(re.findall(r'Submission\.p09_\w+', blocks[SELECTED])) - {SELECTED}
    assert direct <= APPROVED, direct - APPROVED
    closure = {SELECTED}
    while True:
        found = {name for decl in closure for name in re.findall(r'Submission\.p09_\w+', blocks[decl])}
        if found <= closure:
            break
        closure |= found
    options = '''set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open IsLocalRing Filter Topology Ideal Asymptotics UniqueFactorizationMonoid
open scoped nonZeroDivisors
'''
    selected = imports + options + '\n'.join(blocks[name] for name in blocks if name in closure)
    (scratch / 'SelectedNode.lean').write_text(selected)
    receipt = {
        'kind': 'local diagnostic only; not a trusted verifier receipt',
        'revision': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
        'policy_sha256': sha(policy_raw),
        'matching_policy_entry': entry,
        'source_sha256': sha(raw),
        'compiler_copy_sha256': sha(build.encode()),
        'reconstruction_byte_exact': True,
        'omitted_lines': omitted,
        'direct_dependencies': sorted(direct),
        'declaration_closure': sorted(closure),
        'scratch': str(scratch),
        'inputs': {p.name: sha(p.read_bytes()) for p in scratch.glob('*.lean')},
    }
    (OUT / 'local-diagnostic.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(receipt, indent=2))

def run(kind):
    assert kind in ('HeaderAbsence', 'SelectedNode')
    receipt = json.loads((OUT / 'local-diagnostic.json').read_text())
    assert sha((ROOT / 'Submission.lean').read_bytes()) == receipt['source_sha256']
    path = Path(receipt['scratch']) / (kind + '.lean')
    before = sha(path.read_bytes())
    assert before == receipt['inputs'][path.name]
    cmd = [str(LAKE), 'env', 'lean', '-DwarningAsError=true', str(path)]
    log = OUT / (kind + '.log')
    start = time.monotonic()
    with log.open('w') as stream:
        result = subprocess.run(cmd, cwd=ROOT, stdout=stream, stderr=subprocess.STDOUT)
    assert sha(path.read_bytes()) == before
    evidence = {'kind': 'local diagnostic only', 'command': cmd,
                'input_sha256': before, 'exit_code': result.returncode,
                'seconds': time.monotonic() - start, 'log_sha256': sha(log.read_bytes())}
    (OUT / (kind + '-result.json')).write_text(json.dumps(evidence, indent=2) + '\n')
    print(json.dumps(evidence, indent=2))
    print(log.read_text())
    raise SystemExit(result.returncode)

if __name__ == '__main__':
    if sys.argv[1] == 'prepare':
        prepare()
    else:
        run(sys.argv[1])
