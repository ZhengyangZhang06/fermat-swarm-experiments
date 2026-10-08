#!/usr/bin/env python3
"""Controller-only adapter: freeze a registered request, run it on one Swarm node.

Use an immutable deployment of this script and its sibling verifier scripts.
Exit 75 means remote identity/liveness needs reconciliation, not a failed proof.
Never mount credentials, the broker database, or Docker sockets in the job.
"""
from __future__ import annotations

import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from _recursive_lean.swarm_verification import bind_service, terminal_result, verify_result_evidence


IMAGE = 'python:3.12-bookworm@sha256:5560e9ab8709f459489e5b8aa696eda8a07ef821e14bb122be62d91234bfa98b'
BASE = Path('/mnt/data/zhengyang-workspace/fermat-example')
DOCKER = ['sudo', '-n', 'docker']


def docker(*args, timeout=30):
    return subprocess.run([*DOCKER, *map(str, args)], check=True, capture_output=True,
                          text=True, timeout=timeout).stdout


def inspect(kind, identity):
    values = json.loads(docker(kind, 'inspect', identity) if kind in {'service', 'node'} else docker('inspect', identity))
    if len(values) != 1:
        raise RuntimeError('ambiguous Docker identity')
    return values[0]


def record(path, value):
    temporary = path.with_suffix('.tmp')
    with temporary.open('w') as handle:
        json.dump(value, handle, sort_keys=True, indent=2)
        handle.flush()
        os.fsync(handle.fileno())
    temporary.replace(path)
    fd = os.open(path.parent, os.O_RDONLY | os.O_DIRECTORY)
    try:
        os.fsync(fd)
    finally:
        os.close(fd)


def reference_volume_settings(environment):
    """Cache coordinates come only from controller configuration, never a job.

    The controller's private cache prepares the packet; a separately operator-
    seeded node-local named volume must contain that exact same inventory. The
    receiver runs the unchanged checker's full inventory gates before and after
    compilation, so volume existence or an operator seed receipt is not a pass.
    """
    root = environment.get('FERMAT_VERIFIER_REFERENCE_CACHE', '')
    digest = environment.get('FERMAT_VERIFIER_REFERENCE_DIGEST', '')
    volume = environment.get('FERMAT_SWARM_VERIFIER_REFERENCE_VOLUME', '')
    if not (root or digest or volume):
        return None, None
    if not (root and digest and volume):
        raise RuntimeError('remote cached verification requires controller cache, digest and seeded volume')
    if not Path(root).is_absolute() or not re.fullmatch(r'[a-f0-9]{64}', digest):
        raise ValueError('invalid controller reference cache binding')
    if not re.fullmatch(r'[A-Za-z0-9][A-Za-z0-9_.-]{0,127}', volume):
        raise ValueError('invalid operator reference volume name')
    return volume, digest


def registered_node(record, name):
    """Bind the requested hostname to the actual authorized active Docker node."""
    identity = record.get('ID', '')
    if (not re.fullmatch(r'[a-z0-9]{25}', identity)
            or record.get('Description', {}).get('Hostname') != name
            or record.get('Status', {}).get('State') != 'ready'
            or record.get('Spec', {}).get('Availability') != 'active'
            or record.get('Spec', {}).get('Labels', {}).get('fermat-swarm-20261007') != 'true'):
        raise RuntimeError('verifier node identity is not an authorized ready active node')
    return identity


def bound_task(task, expected_node_id):
    if not task.get('NodeID') and task.get('Status', {}).get('State') in {'new', 'allocated', 'pending'}:
        return  # Scheduler has not assigned a node yet; this is not terminal evidence.
    if task.get('NodeID') != expected_node_id:
        raise RuntimeError('verification task moved from its registered node/cache identity')


def create_command(name, node, request_id, packet_digest, root, packet_root, *,
                   reference_volume=None, reference_digest=None):
    if bool(reference_volume) != bool(reference_digest):
        raise ValueError('remote reference volume and digest must be configured together')
    if reference_volume and (not re.fullmatch(r'[A-Za-z0-9][A-Za-z0-9_.-]{0,127}', reference_volume)
                             or not re.fullmatch(r'[a-f0-9]{64}', reference_digest)):
        raise ValueError('invalid remote reference volume binding')
    command = ['service', 'create', '--detach', '--no-resolve-image', '--name', name,
               '--label', 'experiment=fermat-swarm-20261007',
               '--label', f'fermat.request={request_id}', '--label', f'fermat.packet={packet_digest}',
               '--constraint', f'node.hostname=={node}', '--replicas', '1',
               '--restart-condition', 'none', '--user', '1000:1000', '--cap-drop', 'ALL',
               '--read-only', '--limit-cpu', '2', '--limit-memory', '12G' if reference_volume else '6G', '--limit-pids', '256',
               '--mount', 'type=tmpfs,destination=/tmp,tmpfs-size=536870912,tmpfs-mode=1777']
    mounts = [(root / 'code', '/verifier', True), (packet_root, '/input', True),
              (root / 'output', '/output', False)]
    trusted_paths = [BASE / '.humanize/verifier']
    if reference_volume:
        command.extend(['--mount', f'type=volume,source={reference_volume},destination=/reference,readonly,volume-nocopy',
                        '--env', 'FERMAT_VERIFIER_REFERENCE_CACHE=/reference',
                        '--env', f'FERMAT_VERIFIER_REFERENCE_DIGEST={reference_digest}'])
    else:
        trusted_paths.extend([BASE / '.humanize/toolchains/lean-4.33.1-linux', BASE / '.lake/packages'])
    for path in trusted_paths:
        mounts.append((path, str(path), True))
    for source, target, readonly in mounts:
        if any(character in str(source) + str(target) for character in (',', '\n', '\r')):
            raise ValueError('invalid verification mount path')
        command.extend(['--mount', f'type=bind,source={source},destination={target}' + (',readonly' if readonly else '')])
    command.extend([IMAGE, 'python3', '/verifier/swarm-verifier-packet.py',
                    '--packet', '/input', '--digest', packet_digest, '--output', '/output/result'])
    return command


def execute():
    os.umask(0o077)
    request_id = os.environ['FERMAT_VERIFICATION_REQUEST_ID']
    node = os.environ['FERMAT_SWARM_VERIFIER_NODE']
    if not re.fullmatch(r'[a-f0-9]{32}', request_id) or not re.fullmatch(r'hoa(?:[0-9]|[1-9][0-9]|1[01][0-9]|12[0-7])', node):
        raise ValueError('invalid registered request or verifier node')
    reference_volume, reference_digest = reference_volume_settings(os.environ)
    node_id = registered_node(inspect('node', node), node)
    if os.environ.get('FERMAT_SWARM_VERIFIER_EXPECTED_NODE_ID', node_id) != node_id:
        raise RuntimeError('remote verifier node differs from durable dispatcher/readiness identity')
    shared = Path(os.environ['FERMAT_SWARM_VERIFIER_DIRECTORY']).resolve(strict=True)
    project = Path(os.environ['FERMAT_VERIFIER_PROJECT']).resolve()
    if shared.is_relative_to(project.parent) or shared.stat().st_mode & 0o077:
        raise RuntimeError('verification directory must be private and outside worker projects')
    root = shared / request_id
    # A leftover directory is ambiguous. Only operator reconciliation may
    # authorize recovery; a timestamp or missing local PID is insufficient.
    root.mkdir(mode=0o700, exist_ok=False)
    receipt_path = root / 'operation.json'
    receipt = dict(request_id=request_id, node=node, node_id=node_id, state='preparing',
                   reference_volume=reference_volume, reference_cache_digest=reference_digest)
    record(receipt_path, receipt)
    (root / 'code').mkdir()
    (root / 'output').mkdir()
    for name in ('verify-frozen-node.py', 'swarm-verifier-selftest.py', 'swarm-verifier-packet.py'):
        shutil.copyfile(Path(__file__).with_name(name), root / 'code' / name)
    hashes = {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in (root / 'code').iterdir()}
    os.environ['FERMAT_VERIFIER_OUTPUT'] = str(root / 'prepared')
    spec = importlib.util.spec_from_file_location('immutable_checker', root / 'code/verify-frozen-node.py')
    verifier = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(verifier)
    try:
        packet_root, packet_digest = verifier.prepare_verification()
    except Exception:
        receipt.update(state='preparation-failed')
        record(receipt_path, receipt)
        raise  # No remote job was created; this is an ordinary verification failure.
    packet = verifier.validate_prepared(packet_root, packet_digest)
    name = f'fermat-verify-{request_id}'
    receipt.update(state='prepared', packet=str(packet_root), packet_digest=packet_digest,
                   code_sha256=hashes, service_name=name, candidate_commit=packet['evidence']['candidate_commit'])
    record(receipt_path, receipt)
    # Persist intent BEFORE the external create. An interrupted or failed
    # create is never blindly repeated under a second name.
    receipt.update(state='submitting')
    record(receipt_path, receipt)
    try:
        service_id = docker(*create_command(name, node, request_id, packet_digest, root, packet_root,
                                           reference_volume=reference_volume,
                                           reference_digest=reference_digest)).strip()
        if not re.fullmatch(r'[a-z0-9]{25}', service_id):
            raise RuntimeError('Docker did not return one service identity')
        receipt.update(service_id=service_id, state='submitted')
        record(receipt_path, receipt)
        service = inspect('service', service_id)
        service_digest = bind_service(service, request_id, packet_digest, service_id=service_id)
        receipt.update(service_spec_sha256=service_digest)
        record(receipt_path, receipt)
        task_id = None
        while True:
            try:
                service = inspect('service', service_id)
                bind_service(service, request_id, packet_digest, service_id=service_id, spec_digest=service_digest)
                tasks = docker('service', 'ps', '--no-trunc', '--format', '{{.ID}}', service_id).splitlines()
                if not tasks:
                    time.sleep(10)
                    continue
                if len(tasks) != 1:
                    raise RuntimeError('verification service has multiple task identities; reconcile it')
                if task_id is None:
                    task_id = tasks[0]
                    receipt.update(task_id=task_id, state='running')
                    record(receipt_path, receipt)
                if tasks != [task_id]:
                    raise RuntimeError('verification task was replaced')
                task = inspect('task', task_id)
                bound_task(task, node_id)
                code = terminal_result(task, service_id, task_id=task_id)
                if code is not None:
                    break
                print(f'Swarm verification {request_id}: {task["Status"]["State"]} on {node}', flush=True)
            except (subprocess.TimeoutExpired, subprocess.CalledProcessError):
                # An observation failure is not proof that the job stopped.
                print(f'Swarm verification {request_id}: observation retry, retaining task identity', flush=True)
            time.sleep(10)
        receipt.update(state='terminal', returncode=code, task_status=task['Status'])
        record(receipt_path, receipt)
        try:
            logs = subprocess.run([*DOCKER, 'service', 'logs', '--raw', service_id],
                                  check=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                  text=True, timeout=30)
            print(logs.stdout, end='', flush=True)
        except (subprocess.TimeoutExpired, subprocess.CalledProcessError):
            print('Remote log retrieval failed; terminal state and private evidence retained.', flush=True)
        if code != 0:
            return 1
        # Check the exact private inputs, code copies and final evidence again
        # on the controller; stdout and container exit alone are never enough.
        verifier.validate_prepared(packet_root, packet_digest)
        if any(hashlib.sha256((root / 'code' / filename).read_bytes()).hexdigest() != value
               for filename, value in hashes.items()):
            raise RuntimeError('remote verifier code changed during execution')
        evidence = json.loads((root / 'output/result/evidence.json').read_text())
        verify_result_evidence(evidence, packet['evidence'])
        receipt.update(state='verified')
        record(receipt_path, receipt)
        print(f'Verification evidence: {root / "output/result"}', flush=True)
        return 0
    except Exception as error:
        receipt.update(state='uncertain', error=f'{type(error).__name__}: {error}')
        record(receipt_path, receipt)
        print(f'Remote verification requires operator reconciliation: {receipt_path}', flush=True)
        return 75


if __name__ == '__main__':
    try:
        code = execute()
    except FileExistsError:
        print('Existing verification directory requires reconciliation; not creating another job.', flush=True)
        code = 75
    raise SystemExit(code)
