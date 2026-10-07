#!/usr/bin/env python3
"""Blue/green issue-poller launch, retaining live legacy jobs and verifier receipts.

Operator-only: use an immutable workflow archive and an explicitly scoped legacy
fleet/catalog. Initially enable only the named canary project. This does NOT
release a legacy claim, interrupt workers, or claim mathematical acceptance.
"""
import argparse
import json
import os
from pathlib import Path
import secrets
import subprocess
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from _recursive_lean.parallel import PROTOCOL
from _recursive_lean.store import atomic_text


def command(*args, **kw):
    return subprocess.run(list(map(str, args)), check=True, capture_output=True, text=True, **kw).stdout.strip()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for flag in ('private', 'runtime', 'container-runtime'):
        parser.add_argument('--' + flag, required=True, type=Path)
    for flag in ('legacy-service', 'service', 'unit', 'canary-project', 'bind', 'python', 'gh', 'verifier'):
        parser.add_argument('--' + flag, required=True)
    parser.add_argument('--port', type=int, default=8848)
    args = parser.parse_args()
    os.umask(0o077)
    root, flow = args.private.resolve(strict=True), args.runtime.resolve(strict=True)
    if root.stat().st_mode & 0o077:
        raise RuntimeError('operator directory must be private')
    if not (flow / 'scripts/swarm-bootstrap.py').is_file():
        raise RuntimeError('immutable runtime archive missing')
    catalog_path = root / 'parallel-catalog.json'
    token_path = root / 'parallel-broker.token'
    if catalog_path.exists() or token_path.exists():
        raise RuntimeError('parallel deployment already prepared; reconcile it rather than recreate')
    legacy = json.loads((root / 'catalog.json').read_text())
    if args.canary_project not in {p['id'] for p in legacy['projects']}:
        raise RuntimeError('canary outside authorized projects')
    spec = json.loads(command('sudo', '-n', 'docker', 'service', 'inspect', args.legacy_service))[0]['Spec']
    container = spec['TaskTemplate']['ContainerSpec']
    with token_path.open('x') as handle:
        handle.write(secrets.token_hex(32) + '\n')
    catalog = json.loads(json.dumps(legacy))
    catalog['broker_protocol'] = PROTOCOL
    for project in catalog['projects']:
        project['enabled'] = project['id'] == args.canary_project
        project['issue_runtime_protocol'] = PROTOCOL
        project['command'] = ['python3', str(args.container_runtime / 'scripts/swarm-run-issue.py')]
    with catalog_path.open('x') as handle:
        json.dump(catalog, handle, indent=2)
    # Stop new legacy intake for this project, not its live proof/checker process.
    backup = root / 'catalog-before-parallel.json'
    with backup.open('x') as handle:
        json.dump(legacy, handle, indent=2)
    for project in legacy['projects']:
        if project['id'] == args.canary_project:
            project.update(enabled=False, disabled_reason='draining legacy owner for per-issue runtime')
    atomic_text(root / 'catalog.json', json.dumps(legacy, indent=2) + '\n')
    unit = [
        'systemd-run', '--user', '--collect', '--unit=' + args.unit, '--working-directory=' + str(flow),
        '--setenv=PYTHONPATH=' + os.environ.get('PYTHONPATH', ''),
    ]
    for key in ('FERMAT_VERIFIER_REFERENCE_CACHE', 'FERMAT_VERIFIER_REFERENCE_DIGEST'):
        if os.environ.get(key):
            unit.append('--setenv=' + key + '=' + os.environ[key])
    unit += [args.python, '-m', '_recursive_lean.swarm_broker', '--catalog', str(catalog_path),
        '--database', str(root / 'claims.sqlite'), '--token-file', str(token_path),
        '--snapshot', str(root / 'parallel-snapshot.json'), '--certificate', str(root / 'broker.crt'),
        '--key', str(root / 'broker.key'), '--bind', args.bind, '--port', str(args.port),
        '--gh', args.gh, '--verifier', args.verifier, '--preserve-existing-verifications']
    command(*unit)
    secret = args.service + '-broker-token'
    command('sudo', '-n', 'docker', 'secret', 'create', secret, token_path)
    create = ['sudo', '-n', 'docker', 'service', 'create', '--detach', '--no-resolve-image',
              '--name', args.service, '--mode', 'global', '--user', container.get('User', '0:0')]
    for key, value in spec.get('Labels', {}).items():
        create += ['--label', f'{key}={value}']
    for constraint in spec['TaskTemplate'].get('Placement', {}).get('Constraints', []):
        create += ['--constraint', constraint]
    for env in container.get('Env', []):
        if not env.startswith('HUMANIZE_SWARM_ENDPOINT='):
            create += ['--env', env]
    create += ['--env', f'HUMANIZE_SWARM_ENDPOINT=https://{args.bind}:{args.port}']
    for mount in container.get('Mounts', []):
        if mount['Type'] == 'bind':
            if mount['Target'] == '/swarm-worker.py':
                continue
            value = f"type=bind,source={mount['Source']},destination={mount['Target']}"
            if mount.get('ReadOnly'):
                value += ',readonly'
        elif mount['Type'] == 'tmpfs':
            value = f"type=tmpfs,destination={mount['Target']},tmpfs-mode={mount.get('TmpfsOptions', {}).get('Mode', 0o1777):o}"
        else:
            raise RuntimeError('unsupported legacy mount type')
        create += ['--mount', value]
    # Preserve frozen comparator_command; route that transport in NEW containers
    # only. Old workers continue executing their original immutable client.
    create += ['--mount', f'type=bind,source={flow}/scripts/swarm-compare.py,destination=/runtime/flows/math-lean-flow/scripts/swarm-compare.py,readonly']
    for ref in container.get('Secrets', []):
        file = ref['File']
        source = secret if file['Name'] == 'broker_token' else ref['SecretName']
        create += ['--secret', f"source={source},target={file['Name']},uid={file['UID']},gid={file['GID']},mode={file['Mode']:o}"]
    for ref in container.get('Configs', []):
        file = ref['File']
        create += ['--config', f"source={ref['ConfigName']},target={file['Name']},uid={file['UID']},gid={file['GID']},mode={file['Mode']:o}"]
    for network in spec['TaskTemplate'].get('Networks', []):
        create += ['--network', network['Target']]
    limits = spec['TaskTemplate'].get('Resources', {}).get('Limits', {})
    if limits.get('NanoCPUs'):
        create += ['--limit-cpu', str(limits['NanoCPUs'] / 1e9)]
    if limits.get('MemoryBytes'):
        create += ['--limit-memory', str(limits['MemoryBytes'])]
    create += [container['Image'], 'python3', str(args.container_runtime / 'scripts/swarm-bootstrap.py')]
    service_id = command(*create)
    receipt = dict(service=args.service, service_id=service_id, unit=args.unit,
                   runtime=str(flow), protocol=PROTOCOL, canary_project=args.canary_project,
                   state='pollers-launched; legacy ownership retained until terminal')
    atomic_text(root / 'parallel-deployment.json', json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(receipt), flush=True)


if __name__ == '__main__':
    main()
