#!/usr/bin/env python3
"""Bounded operator-only post-seed diagnostics; dry-run unless --apply is given.

This never seeds/overwrites a volume, modifies proof claims or restarts a task.
Only exact terminal diagnostic success may open the node's production readiness
gate. A private controller manifest pins every seed service, original cache/archive
digest, diagnostic template and trusted code.
"""
import argparse
import copy
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import secrets
import sqlite3
import subprocess
import sys
import time

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from _recursive_lean.remote_dispatch_slot import private_directory, read_record
from _recursive_lean.swarm_verification import terminal_result


def digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def docker(*args):
    return subprocess.check_output(['sudo', '-n', 'docker', *args], text=True, timeout=45)


def inspect(kind, identity):
    args = (kind, 'inspect', identity) if kind in ('service', 'node') else ('inspect', identity)
    values = json.loads(docker(*args))
    if len(values) != 1:
        raise ValueError('ambiguous Docker identity')
    return values[0]


def canonical_task_tmpfs(task):
    """Normalize only Docker's omitted /tmp tmpfs mode, never explicit changes.

    Docker defaults a tmpfs mount to 01777 but may omit Mode from inspection.
    Keep raw service specifications for evidence hashing and readiness binding.
    """
    result = copy.deepcopy(task)
    for mount in result.get('ContainerSpec', {}).get('Mounts', []):
        if mount.get('Type') == 'tmpfs' and mount.get('Target') == '/tmp':
            mount.setdefault('TmpfsOptions', {}).setdefault('Mode', 0o1777)
    return result


def equivalent_service_spec(actual, expected):
    actual, expected = copy.deepcopy(actual), copy.deepcopy(expected)
    actual['TaskTemplate'] = canonical_task_tmpfs(actual['TaskTemplate'])
    expected['TaskTemplate'] = canonical_task_tmpfs(expected['TaskTemplate'])
    return actual == expected


def exact_task(service, node_id):
    ids = docker('service', 'ps', '--no-trunc', '--format', '{{.ID}}', service['ID']).split()
    if len(ids) != 1:
        raise ValueError('service does not have exactly one retained task')
    task = inspect('task', ids[0])
    if task.get('ID') != ids[0] or task['ServiceID'] != service['ID'] or task.get('NodeID') != node_id:
        raise ValueError('task service or physical node identity changed')
    actual = canonical_task_tmpfs(task.get('Spec', {}))
    actual.setdefault('Runtime', 'container')  # Swarm omits the default on task records.
    actual.get('ContainerSpec', {}).setdefault('StopGracePeriod', 10000000000)
    expected = canonical_task_tmpfs(service['Spec']['TaskTemplate'])
    expected.get('ContainerSpec', {}).setdefault('StopGracePeriod', 10000000000)
    if actual != expected:
        raise ValueError('task specification differs from pinned service')
    return task


def terminal_success(task):
    return terminal_result(task, task['ServiceID'], task_id=task['ID']) == 0


def json_receipts(task_id):
    receipts = []
    for line in docker('service', 'logs', '--raw', task_id).splitlines():
        if line == 'PRIVATE_FILE_AND_SOCKETS_DENIED':
            receipts.append({'stage': 'isolation-denied'})
            continue
        try:
            value = json.loads(line)
        except ValueError:
            continue
        if isinstance(value, dict):
            receipts.append(value)
    return receipts


def diagnostic_passed(config, receipts):
    def one(stage, fields):
        found = [r for r in receipts if r.get('stage') == stage]
        return len(found) == 1 and all(found[0].get(key) == value for key, value in fields.items())
    checker_hashes = [value for key, value in config['code_sha256'].items()
                      if Path(key).name == 'verify-frozen-node.py']
    return len(checker_hashes) == 1 and all([
        one('readonly-reference-inventory-passed', dict(uid=1000, reference_cache_digest=config['reference_digest'])),
        one('diagnostic-start', dict(uid=1000, verifier_sha256=checker_hashes[0])),
        one('isolation-denied', {}),
        one('diagnostic-passed', dict(comparator_cases=10, production_acceptance_enabled=False)),
        one('cache-selftest-passed', dict(reference_cache_digest=config['reference_digest'],
            post_test_inventory_verified=True, production_enabled=False)),
    ])


def verify_seed(config, node):
    service = inspect('service', node['seed_service_id'])
    if (service['ID'] != node['seed_service_id'] or service['Spec']['Name'] != node['seed_service']
            or digest(service['Spec']) != node['seed_spec_sha256']):
        raise ValueError('seed service specification changed')
    mounts = {m['Target']: m for m in service['Spec']['TaskTemplate']['ContainerSpec']['Mounts']}
    if (mounts.get('/reference', {}).get('Source') != config['volume'] or
            mounts['/reference'].get('Type') != 'volume' or
            service['Spec']['TaskTemplate']['RestartPolicy']['Condition'] != 'none'):
        raise ValueError('seed service volume or restart identity differs')
    task = exact_task(service, node['node_id'])
    if not terminal_success(task):
        return None
    matches = [r for r in json_receipts(task['ID']) if r.get('status') == 'seeded']
    if len(matches) != 1:
        raise ValueError('missing or ambiguous full-inventory seed receipt')
    receipt = matches[0]
    expected = dict(status='seeded', archive_sha256=config['archive_sha256'],
        reference_cache_digest=config['reference_digest'], inventory_entries=config['inventory_entries'],
        inventory_verified=True, root='/reference', owner=1000, mode='0700')
    if receipt != expected:
        raise ValueError('seed receipt differs from pinned archive/full inventory')
    return dict(service_id=service['ID'], task_id=task['ID'], receipt=receipt)


def diagnostic_spec(template, node):
    spec = copy.deepcopy(template)
    spec['Name'] = node['diagnostic_service']
    spec['TaskTemplate']['Placement']['Constraints'] = ['node.id==' + node['node_id']]
    return spec


def create_command(spec):
    """Clone only the reviewed unprivileged, credential-free diagnostic shape."""
    task, container = spec['TaskTemplate'], spec['TaskTemplate']['ContainerSpec']
    if (container['User'] != '1000:1000' or container.get('ReadOnly') is not True
            or container.get('CapabilityDrop') != ['ALL'] or container.get('CapabilityAdd')
            or container.get('Secrets') or container.get('Configs')
            or task['RestartPolicy']['Condition'] != 'none' or task.get('Networks')
            or spec['Mode'] != {'Replicated': {'Replicas': 1}}
            or not re.search(r'@sha256:[a-f0-9]{64}$', container['Image'])
            or container['Args'] != ['python3', '/canary/cache-selftest.py']):
        raise ValueError('diagnostic template is not the reviewed restricted shape')
    limits = task['Resources']['Limits']
    if limits != dict(NanoCPUs=2000000000, MemoryBytes=12884901888, Pids=256):
        raise ValueError('unexpected diagnostic resource limits')
    command = ['service', 'create', '--quiet', '--detach', '--no-resolve-image', '--name', spec['Name'],
        '--replicas', '1', '--restart-condition', 'none', '--user', '1000:1000', '--read-only',
        '--cap-drop', 'ALL', '--limit-cpu', '2', '--limit-memory', '12G', '--limit-pids', '256']
    for key, value in spec.get('Labels', {}).items():
        command += ['--label', key + '=' + value]
    for constraint in task['Placement']['Constraints']:
        command += ['--constraint', constraint]
    for value in container.get('Env', []):
        command += ['--env', value]
    for mount in container['Mounts']:
        if mount['Type'] == 'tmpfs' and mount['Target'] == '/tmp':
            if mount['TmpfsOptions'].get('Mode', 0o1777) != 0o1777:
                raise ValueError('diagnostic tmpfs mode differs from reviewed 01777')
            text = ('type=tmpfs,destination=/tmp,tmpfs-mode=1777,tmpfs-size=' +
                    str(mount['TmpfsOptions']['SizeBytes']))
        elif mount['Type'] in ('bind', 'volume') and mount.get('ReadOnly') is True:
            if any(',' in mount[key] for key in ('Source', 'Target')):
                raise ValueError('invalid mount coordinate')
            text = f"type={mount['Type']},source={mount['Source']},destination={mount['Target']},readonly"
            if mount['Type'] == 'volume':
                if mount.get('VolumeOptions') != {'NoCopy': True}:
                    raise ValueError('reference volume must not copy image contents')
                text += ',volume-nocopy'
        else:
            raise ValueError('diagnostic mount is not readonly reference/code or private tmpfs')
        if mount.get('Source') == '/var/run/docker.sock':
            raise ValueError('diagnostic cannot receive Docker credentials')
        command += ['--mount', text]
    return [*command, container['Image'], *container['Args']]


def write_record(path, value):
    temporary = path.with_suffix('.tmp')
    fd = os.open(temporary, os.O_CREAT | os.O_TRUNC | os.O_WRONLY | os.O_NOFOLLOW, 0o600)
    with os.fdopen(fd, 'w') as stream:
        json.dump(value, stream, sort_keys=True)
        stream.flush()
        os.fsync(stream.fileno())
    temporary.replace(path)
    fd = os.open(path.parent, os.O_RDONLY | os.O_DIRECTORY)
    try:
        os.fsync(fd)
    finally:
        os.close(fd)


def check_configuration(config):
    template = inspect('service', config['template_service_id'])
    if template['ID'] != config['template_service_id'] or digest(template['Spec']) != config['template_spec_sha256']:
        raise ValueError('diagnostic template changed')
    container = template['Spec']['TaskTemplate']['ContainerSpec']
    if sorted(container.get('Env', [])) != sorted([
            'FERMAT_VERIFIER_REFERENCE_CACHE=/reference',
            'FERMAT_VERIFIER_REFERENCE_DIGEST=' + config['reference_digest']]):
        raise ValueError('diagnostic environment differs from trusted cache')
    mounts = {mount['Target']: mount for mount in container['Mounts']}
    if (len(mounts) != len(container['Mounts']) or set(mounts) != {
            '/tmp', '/reference', '/canary', '/verifier', config['tools_directory']}
            or mounts['/reference']['Source'] != config['volume']
            or mounts[config['tools_directory']]['Source'] != config['tools_directory']):
        raise ValueError('diagnostic mount targets differ from reviewed template')
    required_code = {str(Path(mounts['/canary']['Source']) / 'cache-selftest.py'),
        *(str(Path(mounts['/verifier']['Source']) / name) for name in
          ('verify-frozen-node.py', 'swarm-verifier-selftest.py', 'seed-verifier-reference.py'))}
    if not required_code.issubset(config['code_sha256']):
        raise ValueError('diagnostic manifest must pin wrapper, checker, fixtures and seeder')
    for name, expected in config['code_sha256'].items():
        path = Path(name)
        if not path.is_absolute() or path.resolve() != path or hashlib.sha256(path.read_bytes()).hexdigest() != expected:
            raise ValueError('trusted diagnostic code changed')
    nodes, services = set(), set()
    for node in config['nodes']:
        if (node['node'] in nodes or node['diagnostic_service'] in services or
                not re.fullmatch(r'hoa(?:[0-9]|[1-9][0-9]|1[01][0-9]|12[0-7])', node['node']) or
                not re.fullmatch(r'[a-z0-9]{25}', node['node_id']) or
                not re.fullmatch(r'[A-Za-z0-9][A-Za-z0-9_.-]{0,127}', node['diagnostic_service'])):
            raise ValueError('duplicate or unauthorized diagnostic node')
        nodes.add(node['node'])
        services.add(node['diagnostic_service'])
        create_command(diagnostic_spec(template['Spec'], node))
    return template['Spec']


def run(config, directory, *, apply=False, ledger=None, max_active=3, readiness_directory=None):
    if type(max_active) is not int or not 1 <= max_active <= 128:
        raise ValueError('invalid diagnostic concurrency bound')
    template = check_configuration(config)
    config_digest, reports, active = digest(config), [], 0
    # Existing uncertain/submitted tasks occupy slots until exactly reconciled.
    records = {}
    for node in config['nodes']:
        path = directory / (node['node'] + '.json')
        if path.exists():
            record = read_record(path)
            if record['config_sha256'] != config_digest:
                raise ValueError('diagnostic manifest changed during retained operation')
            records[node['node']] = record
            active += record['state'] not in ('passed', 'failed', 'waiting-capacity')
    def process_node(node):
        nonlocal active
        record = records.get(node['node'])
        readiness = readiness_directory / (node['node'] + '.json') if readiness_directory else None
        if apply and readiness and not readiness.exists():
            write_record(readiness, dict(verifier_ready=False))
        if record and (record['state'] == 'failed' or record['state'] == 'passed' and
                (readiness is None or readiness.exists() and read_record(readiness) == record.get('readiness'))):
            reports.append(dict(node=node['node'], state=record['state']))
            return
        observed = inspect('node', node['node_id'])
        if (observed['ID'] != node['node_id'] or observed['Description']['Hostname'] != node['node']
                or observed['Status']['State'] != 'ready' or observed['Spec']['Availability'] != 'active'
                or observed['Spec'].get('Labels', {}).get(config['authorization_label']) != 'true'):
            raise ValueError('diagnostic node is not authorized ready active')
        seed = verify_seed(config, node)
        if seed is None:
            reports.append(dict(node=node['node'], state='seed-not-successfully-terminal'))
            return
        if record and record['seed'] != seed:
            raise ValueError('retained seed task or full-inventory receipt changed')
        spec = diagnostic_spec(template, node)
        existing = docker('service', 'ls', '--filter', 'name=' + spec['Name'], '--format', '{{.Name}}').split()
        present = spec['Name'] in existing
        if record and record['state'] in ('submitting', 'passed') and present:
            was_active = record['state'] == 'submitting'
            service = inspect('service', record.get('service_id') or spec['Name'])
            if not equivalent_service_spec(service['Spec'], spec) or record.get('service_id', service['ID']) != service['ID']:
                raise ValueError('diagnostic service differs from retained specification')
            task = exact_task(service, node['node_id'])
            if record.get('task_id') and task['ID'] != record['task_id']:
                raise ValueError('diagnostic task identity changed')
            record.update(service_id=service['ID'], task_id=task['ID'])
            terminal = terminal_result(task, service['ID'], task_id=task['ID'])
            if terminal is not None:
                passed = terminal_success(task) and diagnostic_passed(config, json_receipts(task['ID']))
                record['state'] = 'passed' if passed else 'failed'
                if apply:
                    if readiness:
                        record['readiness'] = dict(verifier_ready=passed, node=node['node'], node_id=node['node_id'],
                            config_sha256=config_digest, reference_digest=config['reference_digest'],
                            reference_volume=config['volume'],
                            verifier_sha256=next(value for key,value in config['code_sha256'].items()
                                if Path(key).name == 'verify-frozen-node.py'),
                            diagnostic_spec_sha256=digest(service['Spec']),
                            diagnostic_service_id=service['ID'], diagnostic_task_id=task['ID'])
                        write_record(readiness, record['readiness'])
                    ledger.release_node(node=node['node'], reservation_id=record['reservation_id'], owner=record['owner'])
                active -= int(was_active)
            if apply:
                write_record(directory / (node['node'] + '.json'), record)
            reports.append(dict(node=node['node'], state=record['state']))
            return
        if present or record and record['state'] in ('submitting', 'passed'):
            raise ValueError('untracked or missing submitted diagnostic requires reconciliation')
        if active >= max_active:
            reports.append(dict(node=node['node'], state='waiting-diagnostic-slot'))
            return
        if not apply:
            reports.append(dict(node=node['node'], state='ready-for-reservation'))
            return
        record = record or dict(config_sha256=config_digest, state='waiting-capacity', seed=seed,
            reservation_id=secrets.token_hex(16), owner='cache-diagnostic-' + secrets.token_hex(16))
        path = directory / (node['node'] + '.json')
        write_record(path, record)
        if not ledger.reserve_node(node=node['node'], reservation_id=record['reservation_id'],
                                   owner=record['owner'], purpose='cache-diagnostic'):
            reports.append(dict(node=node['node'], state='waiting-capacity'))
            return
        record['state'] = 'submitting'
        write_record(path, record)  # Durable before create; ambiguous create never retries.
        active += 1
        docker(*create_command(spec))
        reports.append(dict(node=node['node'], state='submitted'))
    for node in config['nodes']:
        try:
            process_node(node)
        except (OSError, ValueError, KeyError, RuntimeError, subprocess.SubprocessError) as error:
            # Preserve every reservation/intent. An observation failure on one
            # node must not prevent independent nodes using other bounded slots.
            reports.append(dict(node=node['node'], state='needs-reconciliation', error=type(error).__name__))
    return reports


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--config', type=Path, required=True)
    parser.add_argument('--state-directory', type=Path, required=True)
    parser.add_argument('--database', type=Path)
    parser.add_argument('--max-active', type=int, default=3)
    parser.add_argument('--readiness-directory', type=Path)
    parser.add_argument('--watch', action='store_true', help='Poll every 30 seconds without restarting retained tasks')
    parser.add_argument('--apply', action='store_true')
    args = parser.parse_args()
    config = read_record(args.config)
    directory = private_directory(args.state_directory)
    readiness_directory = private_directory(args.readiness_directory) if args.readiness_directory else None
    fd = os.open(directory / 'launcher.lock', os.O_CREAT | os.O_RDWR | os.O_NOFOLLOW, 0o600)
    with os.fdopen(fd, 'w') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        ledger = None
        if args.apply:
            if args.database is None:
                parser.error('--apply requires the authoritative --database')
            with sqlite3.connect(args.database.absolute().as_uri() + '?mode=ro', uri=True) as db:
                db.execute('SELECT reservation_id FROM node_reservations LIMIT 1')
            from _recursive_lean.distributed_claims import ClaimLedger
            ledger = ClaimLedger(args.database)
        while True:
            print(json.dumps(run(config, directory, apply=args.apply, ledger=ledger,
                max_active=args.max_active, readiness_directory=readiness_directory)), flush=True)
            if not args.watch:
                break
            time.sleep(30)


if __name__ == '__main__':
    main()
