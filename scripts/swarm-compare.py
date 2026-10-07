#!/usr/bin/env python3
"""Request the controller's real verifier for this exact committed candidate."""
import json
import os
from pathlib import Path
import ssl
import subprocess
import time
import uuid
from urllib.request import Request, urlopen
from urllib.error import HTTPError

revision = subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip()
if subprocess.check_output(['git', 'status', '--porcelain', '--untracked-files=no'], text=True).strip():
    raise SystemExit('Commit the candidate before verification')
body = {
    'node': os.environ['SWARM_NODE'], 'task': os.environ['SWARM_TASK'],
    'boot': os.environ['HUMANIZE_SWARM_BOOT'], 'attempt': os.environ['HUMANIZE_SWARM_ATTEMPT'],
    'claim_token': os.environ['HUMANIZE_SWARM_CLAIM_TOKEN'],
    'request_id': uuid.uuid4().hex, 'revision': revision, 'candidate': str(Path.cwd()),
    'run_directory': os.environ['HUMANIZE_RUN_DIR'], 'node_id': os.environ['HUMANIZE_NODE_ID'],
}
token = Path('/run/secrets/broker_token').read_text().strip()
context = ssl.create_default_context(cafile='/broker.crt')
endpoint = os.environ.get('HUMANIZE_SWARM_ENDPOINT', 'https://10.44.0.210:8847').rstrip('/')
if not endpoint.startswith('https://'):
    raise SystemExit('TLS verification broker URL required')
while True:
    request = Request(endpoint + '/verify', data=json.dumps(body).encode(),
                      headers={'Authorization': 'Bearer ' + token, 'Content-Type': 'application/json'})
    try:
        with urlopen(request, context=context, timeout=90) as response:
            result = json.load(response)
    except HTTPError as error:
        if error.code in {400, 401, 403, 409}:
            raise SystemExit(f'Verification request rejected: HTTP {error.code}')
        time.sleep(10)
        continue
    except OSError:
        time.sleep(10)
        continue
    if result['request_id'] != body['request_id'] or result['revision'] != revision:
        raise SystemExit('Verification response identity mismatch')
    if result['state'] == 'finished':
        if subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip() != revision:
            raise SystemExit('Candidate advanced during verification; rerun it')
        print(result['output'], end='')
        raise SystemExit(result['returncode'])
    if result['state'] == 'uncertain':
        raise SystemExit('Verification process needs operator reconciliation; not restarting it')
    print(f"Controller verification {body['request_id']}: {result['state']}", flush=True)
    time.sleep(10)
