#!/usr/bin/env python3
"""Release one legacy grant only after exact Swarm-task and verifier termination.

No proof is accepted. Retain the interrupted RLCR receipt as immutable history,
mark adoption consumed, and let the next owner rerun all ordinary proof gates.
"""
import argparse
import json
from pathlib import Path
import re
import sqlite3
import ssl
import subprocess
import sys
from urllib.request import Request, urlopen
from urllib.parse import urlsplit

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from _recursive_lean.store import atomic_text


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--private', required=True, type=Path)
    p.add_argument('--attempt', required=True)
    p.add_argument('--task', required=True)
    p.add_argument('--receipt', type=Path)
    p.add_argument('--endpoint', required=True)
    args = p.parse_args()
    endpoint = urlsplit(args.endpoint)
    if (endpoint.scheme != 'https' or not endpoint.hostname or endpoint.username
            or endpoint.password or endpoint.path not in ('', '/') or endpoint.query or endpoint.fragment):
        raise RuntimeError('expected a credential-free HTTPS broker origin')
    root = args.private.resolve(strict=True)
    db = sqlite3.connect(f'file:{root / "claims.sqlite"}?mode=ro', uri=True)
    db.row_factory = sqlite3.Row
    held = db.execute('SELECT * FROM claims WHERE attempt=?', (args.attempt,)).fetchone()
    if not held or held['state'] != 'owned' or held['scope'] != 'project':
        raise RuntimeError('expected a live legacy project grant')
    owner_node, owner_task, boot = held['owner'].split('/')
    if owner_task != args.task:
        raise RuntimeError('task differs from the owned grant')
    task = json.loads(subprocess.check_output(['sudo', '-n', 'docker', 'inspect', '--type', 'task', args.task]))[0]
    status = task['Status']
    container = status.get('ContainerStatus', {})
    if (status['State'] not in {'complete', 'failed', 'shutdown'}
            or type(container.get('ExitCode')) is not int or container.get('PID', 0) != 0):
        raise RuntimeError('exact owned container is not confirmed terminal')
    if db.execute("SELECT 1 FROM verifications WHERE attempt=? AND state!='finished' LIMIT 1", (args.attempt,)).fetchone():
        raise RuntimeError('owned verification is not terminal')
    registration = json.loads(held['job'])['verification']
    project = Path(registration['project']).resolve()
    live_receipts = [f for f in (project / '.humanize/github-theorem-prover/runs').glob('*/nodes/*/rlcr-process.json')
                     if not json.loads(f.read_text()).get('consumed')]
    receipt = args.receipt.resolve(strict=True) if args.receipt else None
    if receipt is None and live_receipts:
        raise RuntimeError('unconsumed RLCR receipt requires explicit reconciliation')
    if receipt and (not receipt.is_relative_to(project / '.humanize/github-theorem-prover/runs')
                    or receipt.name != 'rlcr-process.json'
                    or any(f.resolve() != receipt for f in live_receipts)):
        raise RuntimeError('RLCR receipt outside owned project or another unconsumed receipt exists')
    record = json.loads(receipt.read_text()) if receipt else {}
    execution_host = record.get('execution_host', '')
    if receipt and (not isinstance(execution_host, str)
                    or not re.fullmatch('[a-f0-9]{12,64}', execution_host)
                    or not container['ContainerID'].startswith(execution_host)):
        raise RuntimeError('RLCR host differs from the terminal container')
    if receipt:
        backup = receipt.with_name(f'rlcr-process-before-cutover-{args.attempt}.json')
        if not backup.exists():
            with backup.open('x') as output:
                json.dump(record, output, indent=2)
    record.update(consumed=True, operator_terminal={
        'task': args.task, 'container': container['ContainerID'], 'state': status['State'],
        'container_exitcode': container['ExitCode'], 'observed_at': status['Timestamp'],
        'proof_outcome': 'unknown; no acceptance; preserve edits and rerun all gates',
    })
    if receipt:
        atomic_text(receipt, json.dumps(record, indent=2) + '\n')
    atomic_text(root / f'cutover-{args.attempt}.json', json.dumps(record['operator_terminal'], indent=2) + '\n')
    token = (root / 'broker.token').read_text().strip()
    context = ssl.create_default_context(cafile=str(root / 'broker.crt'))
    body = dict(node=owner_node, task=owner_task, boot=boot, attempt=args.attempt, claim_token=held['token'])
    def request(path, fields):
        req = Request(args.endpoint.rstrip('/') + path, data=json.dumps({**body, **fields}).encode(),
                      headers={'Authorization': 'Bearer ' + token, 'Content-Type': 'application/json'})
        with urlopen(req, context=context, timeout=90) as response:
            return json.load(response)
    request('/observe', {'receipt': {**record['operator_terminal'], 'state': 'terminal',
                                  'node': owner_node, 'boot': boot}})
    request('/release', {'outcome': 'stopped', 'processes_remaining': 0, 'returncode': container['ExitCode']})
    print(json.dumps({'attempt': args.attempt, 'task': args.task, 'released': True, 'proof_accepted': False}))


if __name__ == '__main__':
    main()
