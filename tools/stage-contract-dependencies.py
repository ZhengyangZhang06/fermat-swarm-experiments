#!/usr/bin/env python3
"""Mechanically copy the frozen contracts' upstream import closure, with provenance.

This stages dependencies only, not the ten upstream target proof files. It never
alters a copied source byte. Definitions may themselves import upstream lemmas.
"""
import hashlib
import json
from pathlib import Path
import re
import subprocess

PROJECT = Path(__file__).resolve().parents[1]
SOURCE = Path('/mnt/data/zhengyang-workspace/fermats-last-theorem')
REVISION = '6e837e75355538c7f80bab5b956861e86c4eacc2'


def imports(source):
    return [module for line in source.decode().splitlines()
            if line.startswith('import ')
            for module in line.split('--', 1)[0].split()[1:]
            if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_'.]*", module)]


def main():
    manifest = json.loads((PROJECT / 'Fermat/manifest.json').read_text())
    forbidden = {p['source_path'] for p in manifest['problems']}
    tree = subprocess.check_output(['git', '-C', str(SOURCE), 'ls-tree', '-r', REVISION], text=True)
    blobs = {}
    for line in tree.splitlines():
        info, path = line.split('\t', 1)
        if path.endswith('.lean'):
            blobs[path] = info.split()[2]
    pending = []
    for problem in manifest['problems']:
        pending += imports((PROJECT / 'Fermat' / problem['file']).read_bytes())
    seen, records = set(), []
    while pending:
        module = pending.pop()
        if module in seen:
            continue
        seen.add(module)
        relative = module.replace('.', '/') + '.lean'
        if relative not in blobs:
            if module.split('.')[0] not in {'Mathlib', 'Lean', 'Init', 'Batteries', 'Aesop', 'Qq', 'ImportGraph', 'Plausible', 'ProofWidgets'}:
                raise RuntimeError(f'Unknown external import: {module}')
            continue
        if relative in forbidden:
            raise RuntimeError(f'Target proof unexpectedly appears in its statement import closure: {relative}')
        content = subprocess.check_output(['git', '-C', str(SOURCE), 'cat-file', 'blob', blobs[relative]])
        target = PROJECT / relative
        if target.exists() and target.read_bytes() != content:
            raise RuntimeError(f'Refusing to overwrite a changed source: {relative}')
        if not target.exists():
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(content)
        pending += imports(content)
        records.append({'module': module, 'path': relative, 'git_blob': blobs[relative],
                        'sha256': hashlib.sha256(content).hexdigest()})
    destination = PROJECT / 'third_party/contract-imports.json'
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text(json.dumps({'source_repository': manifest['source_repository'],
                                      'source_commit': REVISION,
                                      'modules': sorted(records, key=lambda r: r['path'])}, indent=2) + '\n')
    # The first bootstrap may have unpacked the complete Definitions directory.
    # Keep the executable baseline minimal; retain unrelated pristine copies in
    # an ignored, recoverable reference directory rather than deleting them.
    selected = {record['path'] for record in records}
    moved = 0
    for path in (PROJECT / 'Definitions').rglob('*.lean'):
        relative = path.relative_to(PROJECT).as_posix()
        if relative in selected:
            continue
        data = path.read_bytes()
        digest = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
        if blobs.get(relative) != digest:
            raise RuntimeError(f'Refusing to move a changed/unrecognized definition: {relative}')
        backup = PROJECT / '.humanize/unused-definition-reference' / relative
        backup.parent.mkdir(parents=True, exist_ok=True)
        if backup.exists():
            raise RuntimeError(f'Refusing to overwrite an existing backup: {backup}')
        path.rename(backup)
        moved += 1
    print(json.dumps({'staged_contract_dependencies': len(records), 'target_proofs_copied': 0,
                      'unneeded_pristine_definitions_moved_to_reference': moved}), flush=True)


if __name__ == '__main__':
    main()
