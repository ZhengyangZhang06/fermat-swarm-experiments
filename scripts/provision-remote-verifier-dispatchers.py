#!/usr/bin/env python3
"""Plan/install guarded remote verifier user units for an explicit operator fleet.

Default is read-only planning. --apply creates missing files exclusively; only
--start-new starts units created by this invocation. Existing units are never
replaced, restarted or started, including after an uncertain earlier launch.
"""
import argparse
import json
import os
from pathlib import Path
import re
import shlex
import subprocess
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from _recursive_lean.remote_dispatch_slot import private_directory, read_record


FIELDS = {'database', 'workflow_root', 'python', 'readiness_directory', 'packet_directory',
          'reference_cache', 'reference_digest', 'reference_volume', 'nodes', 'unit_prefix'}


def safe_path(value, *, directory=False):
    if not isinstance(value, str) or not re.fullmatch(r'/[A-Za-z0-9_./:@+\-]+', value):
        raise ValueError('operator paths must be absolute plain systemd-safe paths')
    path = Path(value)
    if '..' in path.parts or any(parent.is_symlink() for parent in (path, *path.parents)):
        raise ValueError('operator paths must not traverse symlinks or parent segments')
    if directory:
        private_directory(path)
    return path


def validate_config(config):
    if set(config) - FIELDS or FIELDS - {'unit_prefix'} - set(config):
        raise ValueError('missing or unknown operator configuration field')
    nodes = config['nodes']
    if (not isinstance(nodes, list) or not nodes or len(set(nodes)) != len(nodes)
            or any(not isinstance(n, str) or not re.fullmatch(
                r'hoa(?:[0-9]|[1-9][0-9]|1[01][0-9]|12[0-7])', n) for n in nodes)):
        raise ValueError('nodes must be an explicit unique authorized hostname list')
    prefix = config.get('unit_prefix', 'fermat-guarded-verifier')
    if not isinstance(prefix, str) or not re.fullmatch(r'[A-Za-z0-9][A-Za-z0-9-]{0,95}', prefix):
        raise ValueError('invalid systemd unit prefix')
    if not re.fullmatch(r'[a-f0-9]{64}', config['reference_digest']):
        raise ValueError('invalid operator cache digest')
    if not re.fullmatch(r'[A-Za-z0-9][A-Za-z0-9_.-]{0,127}', config['reference_volume']):
        raise ValueError('invalid reference volume')
    for field in ('database', 'workflow_root', 'python', 'readiness_directory',
                  'packet_directory', 'reference_cache'):
        safe_path(config[field], directory=field in {'readiness_directory', 'packet_directory', 'reference_cache'})
    if not Path(config['database']).is_file() or not Path(config['python']).is_file():
        raise ValueError('registered ledger and interpreter must already exist')
    for name in ('swarm-dispatch-verification.py', 'swarm-verify-frozen-node.py'):
        if not safe_path(str(Path(config['workflow_root']) / 'scripts' / name)).is_file():
            raise ValueError('immutable guarded workflow scripts must already exist')
    return dict(config, unit_prefix=prefix)


def unit_text(config, node):
    root = Path(config['workflow_root'])
    packet = Path(config['packet_directory']) / node
    readiness = Path(config['readiness_directory']) / f'{node}.json'
    command = [config['python'], str(root / 'scripts/swarm-dispatch-verification.py'),
               '--database', config['database'], '--catalog', str(readiness),
               '--program', str(root / 'scripts/swarm-verify-frozen-node.py'),
               '--remote-node', node, '--remote-directory', str(packet), '--require-bound-readiness']
    environments = dict(FERMAT_VERIFIER_REFERENCE_CACHE=config['reference_cache'],
                        FERMAT_VERIFIER_REFERENCE_DIGEST=config['reference_digest'],
                        FERMAT_SWARM_VERIFIER_REFERENCE_VOLUME=config['reference_volume'])
    return ('[Unit]\nDescription=Guarded remote theorem verifier on ' + node + '\n\n'
            '[Service]\nType=simple\nUMask=0077\nRestart=no\nKillMode=process\n'
            'SendSIGKILL=no\nTimeoutStopSec=infinity\n'
            + ''.join(f'Environment="{key}={value}"\n' for key, value in environments.items())
            + 'ExecStart=' + ' '.join(command) + '\n')


def systemctl(*arguments):
    return subprocess.run(['systemctl', '--user', *arguments], check=True,
                          capture_output=True, text=True, timeout=30).stdout


def unit_state(name):
    result = systemctl('show', name, '--property=LoadState,ActiveState,FragmentPath,DropInPaths,ExecStart,Environment,EnvironmentFiles,Type,Restart,KillMode,UMask,SendSIGKILL,TimeoutStopUSec')
    return dict(line.split('=', 1) for line in result.splitlines() if '=' in line)


def verify_loaded_spec(state, content):
    if state.get('LoadState') != 'loaded':
        return
    values = [line.split('=', 1) for line in content.splitlines() if '=' in line]
    fields = dict(values)
    command = re.fullmatch(r'\{ path=[^;]+; argv\[\]=(.*?) ; ignore_errors=no ; .*\}', state.get('ExecStart', ''))
    if command is None or command[1] != fields['ExecStart']:
        raise RuntimeError('loaded dispatcher command differs from immutable unit specification')
    expected_environment = [value.strip('"') for key, value in values if key == 'Environment']
    if sorted(shlex.split(state.get('Environment', ''))) != sorted(expected_environment) or state.get('EnvironmentFiles'):
        raise RuntimeError('loaded dispatcher environment differs from operator configuration')
    for field in ('Type', 'Restart', 'KillMode', 'UMask', 'SendSIGKILL'):
        if state.get(field) != fields[field]:
            raise RuntimeError('loaded dispatcher process policy differs: ' + field)
    if state.get('TimeoutStopUSec') != 'infinity':
        raise RuntimeError('loaded dispatcher stop policy differs')


def exclusive_write(path, data):
    fd = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW, 0o600)
    with os.fdopen(fd, 'w') as handle:
        handle.write(data)
        handle.flush()
        os.fsync(handle.fileno())
    fd = os.open(path.parent, os.O_RDONLY | os.O_DIRECTORY)
    try:
        os.fsync(fd)
    finally:
        os.close(fd)


def provision(config, unit_directory, *, apply=False, start_new=False):
    config = validate_config(config)
    unit_directory = private_directory(unit_directory)
    if start_new and not apply:
        raise ValueError('--start-new requires --apply')
    plans = []
    # Validate the entire requested batch before creating files or starting units.
    for node in config['nodes']:
        name = f"{config['unit_prefix']}-{node}.service"
        path = unit_directory / name
        content = unit_text(config, node)
        state = unit_state(name)
        if state.get('DropInPaths'):
            raise RuntimeError(f'{name}: drop-ins require operator reconciliation')
        present = path.exists() or path.is_symlink()
        if present:
            if path.is_symlink() or not path.is_file() or path.read_text() != content:
                raise RuntimeError(f'{name}: existing unit specification differs; not replacing')
            if state.get('LoadState') not in {'loaded', 'not-found'}:
                raise RuntimeError(f'{name}: ambiguous existing unit state')
            if state.get('FragmentPath') not in {'', str(path)}:
                raise RuntimeError(f'{name}: loaded from a different unit file')
            verify_loaded_spec(state, content)
        elif state.get('LoadState') != 'not-found' or state.get('ActiveState') != 'inactive':
            raise RuntimeError(f'{name}: existing runtime unit requires reconciliation')
        packet = Path(config['packet_directory']) / node
        if packet.exists() or packet.is_symlink():
            private_directory(packet)
        gate = Path(config['readiness_directory']) / f'{node}.json'
        gate_present = gate.exists() or gate.is_symlink()
        if gate_present:
            value = read_record(gate)
            if type(value.get('verifier_ready')) is not bool or value.get('node', node) != node:
                raise RuntimeError(f'{node}: invalid existing readiness gate')
        plans.append(dict(node=node, name=name, path=path, content=content, present=present,
                          gate=gate, gate_present=gate_present, packet=packet,
                          active_state=state.get('ActiveState', 'unknown')))
    created = []
    if apply:
        for plan in plans:
            plan['packet'].mkdir(mode=0o700, exist_ok=True)
            private_directory(plan['packet'])
            if not plan['gate_present']:
                # A concurrent diagnostic writer wins; never reset a ready gate.
                try:
                    exclusive_write(plan['gate'], json.dumps(dict(verifier_ready=False,
                                    node=plan['node']), sort_keys=True) + '\n')
                except FileExistsError:
                    value = read_record(plan['gate'])
                    if type(value.get('verifier_ready')) is not bool or value.get('node', plan['node']) != plan['node']:
                        raise RuntimeError('concurrent readiness gate is invalid')
            if not plan['present']:
                exclusive_write(plan['path'], plan['content'])
                created.append(plan)
        if created:
            systemctl('daemon-reload')
        if start_new:
            for plan in created:
                # Files are durable launch intents. An uncertain start is never
                # retried on a later invocation, which sees an existing unit.
                try:
                    state = unit_state(plan['name'])
                    if (state.get('LoadState') != 'loaded' or state.get('ActiveState') != 'inactive'
                            or state.get('FragmentPath') != str(plan['path']) or state.get('DropInPaths')):
                        raise RuntimeError(f"{plan['name']}: runtime changed before initial start")
                    verify_loaded_spec(state, plan['content'])
                    systemctl('start', plan['name'])
                except (OSError, RuntimeError, subprocess.SubprocessError) as error:
                    # Preserve this unit's uncertain launch intent, without
                    # stranding independent units in the same initial batch.
                    plan['start_error'] = type(error).__name__
    return [dict(node=p['node'], unit=p['name'], existing=p['present'],
                 previous_state=p['active_state'], action=('needs-reconciliation' if p.get('start_error') else
                     'unchanged' if p['present'] else
                     'started-new' if apply and start_new else 'installed-new' if apply else 'planned-new'))
            for p in plans]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--config', required=True, type=Path)
    parser.add_argument('--unit-directory', required=True, type=Path)
    parser.add_argument('--apply', action='store_true')
    parser.add_argument('--start-new', action='store_true')
    args = parser.parse_args()
    os.umask(0o077)
    result = provision(read_record(args.config), args.unit_directory,
                       apply=args.apply, start_new=args.start_new)
    print(json.dumps(result, sort_keys=True, indent=2))


if __name__ == '__main__':
    main()
