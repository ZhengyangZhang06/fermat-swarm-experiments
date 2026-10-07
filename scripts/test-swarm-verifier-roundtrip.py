#!/usr/bin/env python3
"""Opt-in real Swarm roundtrip test; no campaign issues, claims or PRs are touched.

Creates two disposable local Git fixtures and verifies both with the actual
controller adapter. The valid fixture must pass; a changed statement must fail.
Keep the private receipt directories and terminal services for audit.
"""
import argparse
import json
import os
from pathlib import Path
import subprocess
import sys
import uuid


def git(project, *args):
    return subprocess.check_output(['git', '-c', 'user.name=Verifier Self Test',
                                    '-c', 'user.email=verifier-test@example.invalid',
                                    '-C', str(project), *args], text=True).strip()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--adapter', required=True, type=Path)
    parser.add_argument('--directory', required=True, type=Path)
    parser.add_argument('--node', required=True)
    args = parser.parse_args()
    root = args.directory.resolve()
    root.mkdir(mode=0o700, exist_ok=False)
    jobs = root / 'jobs'
    jobs.mkdir(mode=0o700)
    for name, source, expected in [
        ('valid', 'theorem toy : True := True.intro\n', 0),
        ('changed-statement', 'theorem toy : False → False := fun h => h\n', 1),
    ]:
        project = root / 'projects' / name
        project.mkdir(parents=True)
        git(project, 'init', '-q')
        contract = 'theorem toy : True\n'
        (project / 'Frozen.lean').write_text(contract)
        (project / 'Submission.lean').write_text(contract.rstrip() + ' := by sorry\n')
        (project / 'lake-manifest.json').write_text(json.dumps({'packages': []}))
        (project / '.gitignore').write_text('.lake/\n.humanize/\n')
        git(project, 'add', '.')
        git(project, 'commit', '-qm', 'Freeze toy verification contract')
        frozen = git(project, 'rev-parse', 'HEAD')
        (project / 'Submission.lean').write_text(source)
        git(project, 'add', 'Submission.lean')
        git(project, 'commit', '-qm', 'Record toy candidate')
        revision = git(project, 'rev-parse', 'HEAD')
        run = project / '.humanize/run'
        run.mkdir(parents=True)
        (run / 'github-workflow.json').write_text(json.dumps(dict(source_commit=frozen, root_lean_name='toy', contract=contract)))
        (run / 'dag.json').write_text(json.dumps({'nodes': [dict(id='root', status='rlcr-lean', children=[], depends_on=[], proof_base_commit=frozen)]}))
        (project / '.lake').mkdir()
        (project / '.lake/packages').symlink_to('/mnt/data/zhengyang-workspace/fermat-example/.lake/packages')
        request_id = uuid.uuid4().hex
        environment = {**os.environ, 'FERMAT_VERIFICATION_REQUEST_ID': request_id,
                       'FERMAT_SWARM_VERIFIER_DIRECTORY': str(jobs), 'FERMAT_SWARM_VERIFIER_NODE': args.node,
                       'FERMAT_VERIFIER_PROJECT': str(project), 'FERMAT_FROZEN_SOURCE': frozen,
                       'FERMAT_ROOT_NAME': 'toy', 'FERMAT_CONTRACT_FILE': 'Frozen.lean',
                       'FERMAT_CANDIDATE_REVISION': revision, 'HUMANIZE_RUN_DIR': str(run), 'HUMANIZE_NODE_ID': 'root'}
        print(json.dumps(dict(stage='roundtrip-start', fixture=name, request_id=request_id)), flush=True)
        with (root / f'{name}.log').open('w') as log:
            result = subprocess.run([sys.executable, str(args.adapter.resolve())], cwd=project,
                                    env=environment, stdout=log, stderr=subprocess.STDOUT)
        operation = json.loads((jobs / request_id / 'operation.json').read_text())
        expected_state = 'verified' if expected == 0 else 'terminal'
        if result.returncode != expected or operation['state'] != expected_state:
            raise RuntimeError(f'{name}: unexpected code/state {result.returncode}/{operation["state"]}; inspect {root / (name + ".log")}')
        if not operation.get('task_id') or not operation.get('service_id'):
            raise RuntimeError('roundtrip lacks authoritative remote identities')
        print(json.dumps(dict(stage='roundtrip-passed', fixture=name, request_id=request_id,
                              returncode=result.returncode, service_id=operation['service_id'], task_id=operation['task_id'])), flush=True)


if __name__ == '__main__':
    main()
