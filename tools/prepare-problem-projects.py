#!/usr/bin/env python3
"""Mechanically stage isolated, unsolved projects from frozen campaign contracts.

No model is called. Existing directories are checked and never reset. Each project
has an integration branch in the campaign repository; the main campaign preserves
the original benchmark contracts. --push publishes only these initial branches.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

CAMPAIGN = Path(__file__).resolve().parents[1]
SSH = 'ssh -F /dev/null -o BatchMode=yes -o IdentitiesOnly=yes -o StrictHostKeyChecking=yes -i /mnt/data/zhengyang-workspace/.ssh/fermat-example.aeaAzs/id_ed25519'


def git(root, *args):
    return subprocess.check_output(['git', '-c', 'core.sshCommand=' + SSH, '-C', str(root), *args], text=True).strip()


def statement(source, name):
    """Extract binders/conclusion without altering the supplied Lean syntax."""
    tail = source.split('theorem ' + name, 1)[1].strip()
    depth, separator = 0, None
    for i, char in enumerate(tail):
        if char in '([{':
            depth += 1
        elif char in ')]}':
            depth -= 1
        elif char == ':' and depth == 0:
            separator = i
            break
    if separator is None:
        raise ValueError('no declaration type separator')
    binders, result = tail[:separator].strip(), tail[separator + 1:].strip()
    # The benchmark's only top-level proof suffix is := by sorry. Named
    # arguments in the conclusion are preserved by anchoring to that suffix.
    result = re.sub(r'\s*:=\s*by\s+sorry\s*$', '', result)
    if not result or result == tail[separator + 1:].strip():
        raise ValueError('unexpected frozen proof suffix')
    return ' '.join((f'∀ {binders}, {result}' if binders else result).split())


def prepare(parent, baseline, push):
    data = json.loads((CAMPAIGN / 'campaign.json').read_text())
    registrations = []
    parent.mkdir(parents=True, exist_ok=True)
    for problem in data['problems']:
        ident = problem['id']
        project = parent / ident
        branch = 'experiments/' + ident
        contract = git(CAMPAIGN, 'show', f"{baseline}:{problem['contract']}") + '\n'
        if hashlib.sha256(contract.encode()).hexdigest() != problem['contract_sha256']:
            raise ValueError('frozen benchmark contract changed')
        if not project.exists():
            subprocess.run(['git', 'clone', '--no-hardlinks', '--no-checkout', str(CAMPAIGN), str(project)], check=True)
            git(project, 'checkout', '-b', branch, baseline)
            git(project, 'remote', 'set-url', 'origin', f"git@github.com:{data['repository']}.git")
            (project / 'Submission.lean').write_text(contract)
            lake = project / 'lakefile.lean'
            lake.write_text(lake.read_text().replace('@[default_target]\nlean_lib Fermat', 'lean_lib Fermat')
                            + '\n@[default_target]\nlean_lib Submission\n')
            config = dict(
                github_repository=data['repository'], github_worker_mode='poll', github_issue_workers=1,
                github_poll_once=True, github_selected_issue=problem['issue_number'],
                github_root_issue_number=problem['issue_number'], github_issue_poll_interval=30,
                github_auto_merge=True, github_close_proved_issues=True, local_problem=True,
                github_workspace_remote='origin', github_base_branch=branch,
                github_root_lean_name=problem['theorem'], github_root_lean_statement=statement(contract, problem['theorem']),
                github_contract_file=problem['contract'], github_workspace_branch_prefix='proof-workspace',
                github_status_publish=False, problem_id=ident, lean_target='Submission.lean',
                comparator_command='python3 /runtime/flows/math-lean-flow/scripts/swarm-compare.py',
                comparator_success='Your solution is okay!', artifact_dir='.humanize/github-theorem-prover',
                max_depth=6, max_children=8, max_nodes=200, max_parallel_children=1, rlcr_rounds=20,
            )
            (project / 'swarm-project.json').write_text(json.dumps(config, ensure_ascii=False, indent=2) + '\n')
            (project / 'PROBLEM.md').write_text(
                f"Prove `{problem['theorem']}` for `{ident}` using the exact frozen contract "
                f"in `{problem['contract']}`. Write the Lean solution in Submission.lean. "
                "Use the issue/PR workflow: complete and independently review the natural-language proof, "
                "publish every new named helper as an issue, and require the controller comparator and "
                "independent review before a solution PR is merged and its issue closed. "
                "Workers independently poll issues; do not dispatch or notify other workers. "
                "No web search. Do not import the original upstream solution of this target. "
                "Pinned unchanged libraries may be reused with exact provenance and axiom checks.\n")
            git(project, 'add', 'Submission.lean', 'lakefile.lean', 'swarm-project.json', 'PROBLEM.md')
            git(project, '-c', 'user.name=Fermat Experiment', '-c', 'user.email=fermat-experiment@example.invalid',
                'commit', '-m', f'Freeze executable unsolved project for {ident}')
        if git(project, 'status', '--porcelain'):
            raise ValueError(f'existing project is not clean: {ident}')
        config = json.loads((project / 'swarm-project.json').read_text())
        if config['github_root_lean_name'] != problem['theorem'] or config['github_base_branch'] != branch:
            raise ValueError('existing project identity differs')
        if (project / problem['contract']).read_text() != contract:
            raise ValueError('existing original contract changed')
        packages = project / '.lake/packages'
        packages.parent.mkdir(exist_ok=True)
        if not packages.exists():
            packages.symlink_to((CAMPAIGN / '.lake/packages').resolve(), target_is_directory=True)
        if push:
            git(project, 'push', '-u', 'origin', f'HEAD:refs/heads/{branch}')
        registrations.append(dict(id=ident, root_issue=problem['issue_number'], enabled=False,
            command=['python3', '/runtime/flows/math-lean-flow/scripts/swarm-run-issue.py'],
            cwd=str(project), environment={}, log_directory=str(project / '.humanize/swarm-logs'),
            verification=dict(project=str(project), source_commit=git(project, 'rev-parse', 'HEAD'),
                              root_name=problem['theorem'], contract_file=problem['contract'])))
        print(json.dumps({'project': ident, 'branch': branch, 'prepared': True, 'pushed': push}), flush=True)
    destination = CAMPAIGN / '.humanize/prepared-projects.json'
    destination.parent.mkdir(exist_ok=True)
    destination.write_text(json.dumps({'repository': data['repository'], 'verifier_ready': False,
                                     'projects': registrations}, indent=2) + '\n')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--parent', type=Path, required=True)
    parser.add_argument('--baseline', required=True)
    parser.add_argument('--push', action='store_true')
    args = parser.parse_args()
    prepare(args.parent.resolve(), args.baseline, args.push)
