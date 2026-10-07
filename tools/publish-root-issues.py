#!/usr/bin/env python3
"""Idempotently publish the ten frozen root specifications, never fake proofs."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import subprocess

PROJECT = Path(__file__).resolve().parents[1]
REPO = 'ZhengyangZhang06/fermat-swarm-experiments'
CONTRACT_REVISION = 'cc45347'
GH = '/home/ubuntu/.local/bin/gh'


def gh(*args, payload=None):
    command = [GH, 'api', *args]
    if payload is not None:
        command += ['--input', '-']
    return json.loads(subprocess.run(
        command, input=json.dumps(payload) if payload is not None else None,
        capture_output=True, text=True, check=True,
    ).stdout)


def main():
    revision = subprocess.check_output(
        ['git', '-C', str(PROJECT), 'rev-parse', CONTRACT_REVISION], text=True,
    ).strip()
    manifest = json.loads((PROJECT / 'Fermat/manifest.json').read_text())
    issues = gh(f'repos/{REPO}/issues?state=all&per_page=100', '--paginate', '--slurp')
    issues = [issue for page in issues for issue in page if not issue.get('pull_request')]
    records = []
    for index, problem in enumerate(manifest['problems'], 1):
        problem_id = f'fermat-p{index:02}'
        marker = f'<!-- theorem-id: {problem_id}/root -->'
        relative = f"Fermat/{problem['file']}"
        contract = subprocess.check_output(
            ['git', '-C', str(PROJECT), 'show', f'{revision}:{relative}'], text=True,
        )
        if (PROJECT / relative).read_text() != contract:
            raise RuntimeError(f'Frozen contract changed: {relative}')
        matches = [issue for issue in issues if marker in (issue.get('body') or '')]
        if len(matches) > 1:
            raise RuntimeError(f'Duplicate root records: {problem_id}')
        if matches:
            issue = matches[0]  # Never overwrite later proof progress on resume.
        else:
            body = f'''{marker}

## Theorem and source

Lean declaration: `{problem['theorem']}`.
Root problem: this issue. Parent: none (root theorem).
The exact statement, including all hypotheses, is the frozen Lean contract below.
Contract: [{relative}](https://github.com/{REPO}/blob/{revision}/{relative}).
Benchmark revision: `d8c69c0aae9dadbb9d0b4817ffc99ea07c2f7e99`.
Formalization/definition revision: `{manifest['source_commit']}`.
Toolchain: `leanprover/lean4:v4.33.1`.

## Lean problem

```lean
{contract.rstrip()}
```

Formalization status: frozen unsolved goal; project validation is pending.
The `sorry` placeholder is part of the specification, not a solution.

## Natural-language proof

Proof status: pending; no complete argument has been accepted.
The resolver must establish the displayed conclusion under exactly the displayed
hypotheses. No decomposition or proposed argument has yet been reviewed.
Remaining gap: the entire proof, including any required new helper lemmas.
This section must be replaced with the complete reviewed natural-language proof
before acceptance; an outline or a worker report alone is not proof evidence.

## Dependencies and decomposition

Children: none published yet. Prerequisite theorem issues: none yet identified.
Pinned definition/library imports are in the contract. New named helpers require
their own issues, proofs, and PRs, with explicit acyclic prerequisite links.

## Acceptance

- [ ] Exact frozen statement, context, and dependency revisions preserved.
- [ ] Every newly introduced named helper has an issue and verified solution PR.
- [ ] Complete natural-language proof committed and independently reviewed.
- [ ] Pinned Lean build, real comparator, and transitive axiom checks pass.
- [ ] No sorryAx, added assumptions, circular dependencies, or verification bypass.
- [ ] Root and every retained prerequisite interface verified together.
- [ ] Verification evidence identifies the exact candidate and integrated revisions.
- [ ] Exact verified solution PR merged; only then close this issue as completed.

Solution PR: not opened.
Current state: open, deployment preparation. No resolver is claimed running yet.
'''
            issue = gh(f'repos/{REPO}/issues', payload={
                'title': f"[{problem_id}/root] {problem['theorem']}", 'body': body,
            })
            issues.append(issue)
        record = {
            'id': problem_id, 'theorem': problem['theorem'], 'contract': relative,
            'contract_revision': revision,
            'contract_sha256': hashlib.sha256(contract.encode()).hexdigest(),
            'issue_number': issue['number'], 'issue_url': issue['html_url'],
        }
        records.append(record)
        directory = PROJECT / 'proofs' / problem_id
        directory.mkdir(parents=True, exist_ok=True)
        path = directory / 'index.md'
        if not path.exists():
            path.write_text(
                f"# {problem_id}\n\nTheorem: `{problem['theorem']}`.\n\n"
                f"Root issue: {issue['html_url']}\n\n"
                f"Frozen contract: `{relative}` at `{revision}`.\n\n"
                "Status: unsolved; no proof has been verified.\n\n"
                "Natural-language proof: pending. No reviewed decomposition yet.\n\n"
                "Children/prerequisites: none published. Solution PR: not opened.\n\n"
                "Acceptance evidence: none. Follow the root issue's full verification checklist.\n",
            )
        print(f"{problem_id}: {issue['html_url']}", flush=True)
    (PROJECT / 'campaign.json').write_text(json.dumps({
        'repository': REPO, 'benchmark_revision': 'd8c69c0aae9dadbb9d0b4817ffc99ea07c2f7e99',
        'source_revision': manifest['source_commit'], 'problems': records,
    }, indent=2) + '\n')


if __name__ == '__main__':
    main()
