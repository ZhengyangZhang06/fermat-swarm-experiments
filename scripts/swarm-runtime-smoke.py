#!/usr/bin/env python3
"""One real, no-tools model turn using only the user-authorized local credentials."""
import json
import os
from pathlib import Path
import shutil
import subprocess
import tomllib
from urllib.parse import urlsplit

home = Path('/home/ubuntu/.codex')
home.mkdir(parents=True, exist_ok=True)
for source, target in (('/run/secrets/codex_auth', 'auth.json'),
                       ('/run/secrets/codex_config', 'config.toml')):
    shutil.copyfile(source, home / target)
    (home / target).chmod(0o600)
config = tomllib.loads((home / 'config.toml').read_text())
provider = config.get('model_provider', '')
url = config.get('model_providers', {}).get(provider, {}).get('base_url', '')
host = (urlsplit(url).hostname or '').casefold()
if host == 'rust.cat' or host.endswith('.rust.cat'):
    raise SystemExit('Forbidden provider configuration')
environment = {**os.environ, 'CODEX_HOME': str(home), 'HUMANIZE_HOME': '/tmp/humanize-smoke',
               'PATH': '/runtime/bin:' + os.environ['PATH']}
humanize = Path(environment['HUMANIZE_HOME'])
humanize.mkdir(exist_ok=True)
(humanize / 'flowverses').symlink_to('/runtime/flowverses')
version = subprocess.check_output(['/runtime/bin/codex', '--version'], text=True).strip()
print(json.dumps({'codex': version, 'model': config['model'], 'stage': 'runtime-loaded'}), flush=True)
check = subprocess.run(['python3', '-c',
    'from hmz.flows import configures; c=configures("official/humanize1:rlcr"); '
    'assert c is not None and "skip_code_review" in c.model_fields; print("RLCR_CONFIG_READY")'],
    env=environment, capture_output=True, text=True)
if check.returncode:
    print(json.dumps({'stage': 'humanize-import', 'ok': False, 'returncode': check.returncode}), flush=True)
    raise SystemExit(1)
print(json.dumps({'stage': 'humanize-import', 'ok': True}), flush=True)
result_path = Path('/tmp/codex-smoke-result.txt')
result = subprocess.run([
    '/runtime/bin/codex', 'exec', '--skip-git-repo-check', '--sandbox', 'read-only',
    '-m', config['model'], '-c', 'web_search="disabled"',
    '--output-last-message', str(result_path),
    'This is a worker-runtime authentication smoke test, not a math problem. '
    'Do not use tools, browse, search, or read or edit any files. '
    'Reply with exactly FERMAT_SWARM_READY.',
], cwd='/tmp', env=environment, capture_output=True, text=True, timeout=300)
answer = result_path.read_text().strip() if result_path.exists() else ''
ok = result.returncode == 0 and answer == 'FERMAT_SWARM_READY'
print(json.dumps({'stage': 'authenticated-model-turn', 'ok': ok,
                  'returncode': result.returncode, 'answer_matches': answer == 'FERMAT_SWARM_READY'}), flush=True)
raise SystemExit(0 if ok else 1)
