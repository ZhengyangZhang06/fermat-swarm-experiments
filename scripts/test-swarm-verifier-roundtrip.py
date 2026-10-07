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
import re
import subprocess
import sys
import uuid


def git(project, *args):
    return subprocess.check_output(['git', '-c', 'user.name=Verifier Self Test',
                                    '-c', 'user.email=verifier-test@example.invalid',
                                    '-C', str(project), *args], text=True).strip()


def unique_manifest_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError('duplicate dependency manifest key')
        result[key] = value
    return result


def fixture_inputs(mathlib_fixture=False, dependency_manifest=None):
    """Freeze operator CLI input once; never source dependencies from a worker.

    Structural validation is not provenance: the operator must select the trusted
    pinned manifest. The unchanged verifier checks its actual source revisions.
    Return original bytes, without normalizing or resealing the manifest.
    """
    if bool(mathlib_fixture) != (dependency_manifest is not None):
        raise ValueError('--mathlib-fixture and --dependency-manifest are required together')
    encoded = json.dumps({'packages': []}).encode()
    prefix = ''
    if mathlib_fixture:
        try:
            encoded = Path(dependency_manifest).read_bytes()
            manifest = json.loads(encoded, object_pairs_hook=unique_manifest_object)
        except (OSError, UnicodeError, ValueError) as error:
            raise ValueError('cannot read a valid operator dependency manifest') from error
        if (not isinstance(manifest, dict) or not isinstance(manifest.get('packages'), list)
                or not manifest['packages']
                or manifest.get('packagesDir', '.lake/packages') != '.lake/packages'):
            raise ValueError('dependency manifest must list pinned Git packages')
        names = set()
        for package in manifest['packages']:
            if (not isinstance(package, dict) or package.get('type') != 'git'
                    or not isinstance(package.get('name'), str)
                    or not re.fullmatch(r'[A-Za-z0-9_-]+', package['name'])
                    or not isinstance(package.get('rev'), str)
                    or not re.fullmatch(r'[a-f0-9]{40}', package['rev'])
                    or package['name'] in names):
                raise ValueError('dependency records require unique safe names and full pinned Git revisions')
            names.add(package['name'])
        if 'mathlib' not in names:
            raise ValueError('mathlib fixture requires a pinned mathlib dependency')
        prefix = 'import Mathlib.Data.Nat.Basic\n\n'
    contract = prefix + 'theorem toy : True\n'
    fixtures = [
        ('valid', prefix + 'theorem toy : True := True.intro\n', 0),
        ('changed-statement', prefix + 'theorem toy : False → False := fun h => h\n', 1),
    ]
    return contract, fixtures, encoded


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--adapter', required=True, type=Path)
    parser.add_argument('--directory', required=True, type=Path)
    parser.add_argument('--node', required=True)
    parser.add_argument('--mathlib-fixture', action='store_true',
                        help='Exercise pinned package sources and compiled mathlib imports')
    parser.add_argument('--dependency-manifest', type=Path,
                        help='Trusted operator-pinned manifest; required with --mathlib-fixture')
    args = parser.parse_args()
    try:
        contract, fixtures, manifest_bytes = fixture_inputs(args.mathlib_fixture, args.dependency_manifest)
    except ValueError as error:
        parser.error(str(error))
    root = args.directory.resolve()
    root.mkdir(mode=0o700, exist_ok=False)
    jobs = root / 'jobs'
    jobs.mkdir(mode=0o700)
    for name, source, expected in fixtures:
        project = root / 'projects' / name
        project.mkdir(parents=True)
        git(project, 'init', '-q')
        (project / 'Frozen.lean').write_text(contract)
        (project / 'Submission.lean').write_text(contract.rstrip() + ' := by sorry\n')
        (project / 'lake-manifest.json').write_bytes(manifest_bytes)
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
        if expected != 0 and "Challenge and solution theorem statement do not match: 'toy'" not in (
                root / f'{name}.log').read_text():
            raise RuntimeError('changed-statement: missing actual comparator statement-mismatch evidence')
        print(json.dumps(dict(stage='roundtrip-passed', fixture=name, request_id=request_id,
                              returncode=result.returncode, service_id=operation['service_id'], task_id=operation['task_id'])), flush=True)


if __name__ == '__main__':
    main()
