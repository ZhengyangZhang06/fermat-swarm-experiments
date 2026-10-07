#!/usr/bin/env python3
"""Blue/green issue-poller launch, retaining live legacy jobs and verifier receipts.

Operator-only: use an immutable workflow archive and an explicitly scoped source
fleet/catalog. Default mode starts a canary; additive mode leaves source intake and
all running proof/checker jobs untouched. This does NOT release a claim, interrupt
workers, or claim mathematical acceptance.
"""
import argparse
import json
import os
from pathlib import Path
import secrets
import re
import sqlite3
import subprocess
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from _recursive_lean.parallel import PROTOCOL
from _recursive_lean.store import atomic_text


def command(*args, **kw):
    return subprocess.run(list(map(str, args)), check=True, capture_output=True, text=True, **kw).stdout.strip()


COMPARATOR_TARGET = '/runtime/flows/math-lean-flow/scripts/swarm-compare.py'


def mount_arguments(container, flow):
    """Replace only the comparator transport in new containers, never duplicate it."""
    mounts = []
    for mount in container.get('Mounts', []):
        if mount['Target'] in ('/swarm-worker.py', COMPARATOR_TARGET):
            continue
        if mount['Type'] == 'bind':
            value = f"type=bind,source={mount['Source']},destination={mount['Target']}"
            if mount.get('ReadOnly'):
                value += ',readonly'
        elif mount['Type'] == 'tmpfs':
            value = f"type=tmpfs,destination={mount['Target']},tmpfs-mode={mount.get('TmpfsOptions', {}).get('Mode', 0o1777):o}"
        else:
            raise RuntimeError('unsupported source mount type')
        mounts += ['--mount', value]
    mounts += ['--mount', f'type=bind,source={flow}/scripts/swarm-compare.py,destination={COMPARATOR_TARGET},readonly']
    return mounts


def retry_publication_failures(catalog, database, issues):
    """Clear only explicitly requested, terminal, publication-failed issue grants.

    This edits the NEW in-memory catalogue, never the source or claim ledger.
    Mathematical failures, uncertain/live owners and pending checkers remain blocked.
    """
    evidence = []
    with sqlite3.connect(f'file:{database}?mode=ro', uri=True) as db:
        db.row_factory = sqlite3.Row
        for issue in sorted(set(issues)):
            project = next((p for p in catalog['projects'] if issue in p.get('quarantined_issues', [])), None)
            if project is None:
                raise RuntimeError(f'issue {issue} is not quarantined in source catalogue')
            rows = db.execute('SELECT attempt,state,job,receipt,project FROM claims '
                'WHERE repository=? AND issue=? ORDER BY rowid DESC',
                (catalog['repository'].casefold(), issue)).fetchall()
            if not rows or any(row['state'] == 'owned' for row in rows):
                raise RuntimeError(f'issue {issue} lacks exclusive terminal claim evidence')
            claim = rows[0]
            receipt = json.loads(claim['receipt'])
            if (claim['state'] != 'released' or claim['project'] != project['id']
                    or receipt.get('state') != 'terminal' or type(receipt.get('returncode')) is not int):
                raise RuntimeError(f'issue {issue} has no terminal released receipt')
            pending = db.execute("SELECT count(*) FROM verifications v JOIN claims c ON c.attempt=v.attempt "
                "WHERE c.repository=? AND c.issue=? AND v.state!='finished'",
                (catalog['repository'].casefold(), issue)).fetchone()[0]
            if pending:
                raise RuntimeError(f'issue {issue} still has nonterminal verification')
            job = json.loads(claim['job'])
            log = Path(job['log_directory']) / (claim['attempt'] + '.log')
            # Restrict evidence to the final traceback, not a model-quoted earlier error.
            text = log.read_text(errors='replace')
            traceback = text.rsplit('Traceback (most recent call last):', 1)
            if len(traceback) != 2 or not re.search(
                    r'^_recursive_lean\.github\.PublicationError: GitHub (?:PATCH|POST|PUT|GET|DELETE) '
                    r'[^\n]+ failed; check gh authentication/repository access, then resume$',
                    traceback[-1], flags=re.MULTILINE):
                raise RuntimeError(f'issue {issue} did not end with a GitHub publication failure')
            project['quarantined_issues'] = [one for one in project['quarantined_issues'] if one != issue]
            evidence.append(dict(issue=issue, attempt=claim['attempt'], log=str(log),
                                 reason='terminal GitHub publication failure; retry exact saved checkpoint'))
    return evidence


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for flag in ('private', 'runtime', 'container-runtime'):
        parser.add_argument('--' + flag, required=True, type=Path)
    for flag in ('legacy-service', 'service', 'unit', 'bind', 'python', 'gh', 'verifier'):
        parser.add_argument('--' + flag, required=True)
    parser.add_argument('--canary-project')
    parser.add_argument('--source-catalog', default='catalog.json')
    parser.add_argument('--deployment-prefix', default='parallel')
    parser.add_argument('--additive', action='store_true', help='Leave existing fleet/catalogue unchanged')
    parser.add_argument('--verifier-paused', action='store_true', help='Keep pending-check guard, but queue all new checks')
    parser.add_argument('--retry-publication-issue', action='append', type=int, default=[])
    parser.add_argument('--port', type=int, default=8848)
    args = parser.parse_args()
    os.umask(0o077)
    root, flow = args.private.resolve(strict=True), args.runtime.resolve(strict=True)
    if root.stat().st_mode & 0o077:
        raise RuntimeError('operator directory must be private')
    if not (flow / 'scripts/swarm-bootstrap.py').is_file():
        raise RuntimeError('immutable runtime archive missing')
    if not re.fullmatch('[a-z][a-z0-9-]{0,39}', args.deployment_prefix):
        raise RuntimeError('invalid deployment prefix')
    if Path(args.source_catalog).name != args.source_catalog:
        raise RuntimeError('source catalogue must be a private-directory filename')
    if args.additive == bool(args.canary_project):
        raise RuntimeError('choose either additive mode or one canary project')
    if args.retry_publication_issue and not args.additive:
        raise RuntimeError('publication retries require an additive deployment')
    prefix = args.deployment_prefix
    catalog_path = root / f'{prefix}-catalog.json'
    token_path = root / f'{prefix}-broker.token'
    if catalog_path.exists() or token_path.exists():
        raise RuntimeError('parallel deployment already prepared; reconcile it rather than recreate')
    legacy = json.loads((root / args.source_catalog).read_text())
    if args.canary_project and args.canary_project not in {p['id'] for p in legacy['projects']}:
        raise RuntimeError('canary outside authorized projects')
    spec = json.loads(command('sudo', '-n', 'docker', 'service', 'inspect', args.legacy_service))[0]['Spec']
    container = spec['TaskTemplate']['ContainerSpec']
    catalog = json.loads(json.dumps(legacy))
    catalog['broker_protocol'] = PROTOCOL
    if args.verifier_paused:
        catalog['verifier_ready'] = False
    for project in catalog['projects']:
        if not args.additive:
            project['enabled'] = project['id'] == args.canary_project
        project['issue_runtime_protocol'] = PROTOCOL
        project['command'] = ['python3', str(args.container_runtime / 'scripts/swarm-run-issue.py')]
    retry_evidence = retry_publication_failures(catalog, root / 'claims.sqlite', args.retry_publication_issue)
    # Validate all mount forms before making any deployment changes.
    mounts = mount_arguments(container, flow)
    with token_path.open('x') as handle:
        handle.write(secrets.token_hex(32) + '\n')
    with catalog_path.open('x') as handle:
        json.dump(catalog, handle, indent=2)
    # Stop new legacy intake for this project, not its live proof/checker process.
    backup = root / f'catalog-before-{prefix}.json'
    with backup.open('x') as handle:
        json.dump(legacy, handle, indent=2)
    if not args.additive:
        for project in legacy['projects']:
            if project['id'] == args.canary_project:
                project.update(enabled=False, disabled_reason='draining legacy owner for per-issue runtime')
        atomic_text(root / args.source_catalog, json.dumps(legacy, indent=2) + '\n')
    unit = [
        'systemd-run', '--user', '--collect', '--unit=' + args.unit, '--working-directory=' + str(flow),
        '--setenv=PYTHONPATH=' + os.environ.get('PYTHONPATH', ''),
    ]
    for key in ('FERMAT_VERIFIER_REFERENCE_CACHE', 'FERMAT_VERIFIER_REFERENCE_DIGEST'):
        if os.environ.get(key):
            unit.append('--setenv=' + key + '=' + os.environ[key])
    unit += [args.python, '-m', '_recursive_lean.swarm_broker', '--catalog', str(catalog_path),
        '--database', str(root / 'claims.sqlite'), '--token-file', str(token_path),
        '--snapshot', str(root / f'{prefix}-snapshot.json'), '--certificate', str(root / 'broker.crt'),
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
    # Preserve frozen comparator_command; route that transport in NEW containers
    # only. Old workers continue executing their original immutable client.
    create += mounts
    for ref in container.get('Secrets', []):
        file = ref['File']
        source = secret if file['Name'] == 'broker_token' else ref['SecretName']
        create += ['--secret', f"source={source},target={file['Name']},uid={file['UID']},gid={file['GID']},mode=0{file['Mode']:o}"]
    for ref in container.get('Configs', []):
        file = ref['File']
        create += ['--config', f"source={ref['ConfigName']},target={file['Name']},uid={file['UID']},gid={file['GID']},mode=0{file['Mode']:o}"]
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
                   additive=args.additive, source_service=args.legacy_service,
                   source_catalog=args.source_catalog, verifier_ready=catalog.get('verifier_ready', False),
                   publication_retries=retry_evidence, endpoint=f'https://{args.bind}:{args.port}',
                   state='pollers-launched; legacy ownership retained until terminal')
    atomic_text(root / f'{prefix}-deployment.json', json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(receipt), flush=True)


if __name__ == '__main__':
    main()
