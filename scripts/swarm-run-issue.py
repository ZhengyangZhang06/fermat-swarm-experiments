#!/usr/bin/env python3
"""Run one self-selected theorem step while the node daemon holds its claim."""
import json
import os
from pathlib import Path
import subprocess
import sys
import tomllib
from urllib.parse import urlsplit


def main():
    for key in ('HUMANIZE_SWARM_ATTEMPT', 'HUMANIZE_SWARM_CLAIM_TOKEN', 'HUMANIZE_SWARM_BOOT'):
        if not os.environ.get(key):
            raise RuntimeError('A broker-owned issue claim is required')
    # This directory is populated from the explicitly authorized local-home
    # credentials through Docker secrets. No provider fallback is permitted.
    auth_home = Path('/home/ubuntu/.codex')
    if not (auth_home / 'auth.json').is_file():
        raise RuntimeError('Authorized Codex authentication is unavailable')
    model_config = tomllib.loads((auth_home / 'config.toml').read_text())
    provider = model_config.get('model_providers', {}).get(model_config.get('model_provider'), {})
    host = (urlsplit(provider.get('base_url', '')).hostname or '').casefold()
    if host == 'rust.cat' or host.endswith('.rust.cat'):
        raise RuntimeError('Forbidden provider configuration')
    project = Path.cwd()
    config = json.loads((project / 'swarm-project.json').read_text())
    access = subprocess.run(['git', 'ls-remote', '--heads', 'origin', config['github_base_branch']],
                            capture_output=True, text=True, timeout=60)
    if access.returncode:
        # Git remotes have already been restricted to token-free GitHub URLs.
        # Keep the actual SSH failure visible instead of repeatedly starting HMZ.
        print(access.stderr, file=sys.stderr, flush=True)
        raise RuntimeError('Worker cannot read the registered GitHub branch')
    config.update(github_poll_once=True, github_issue_workers=1,
                  github_selected_issue=int(os.environ['HUMANIZE_SELECTED_ISSUE']))
    destination = project / '.humanize/swarm-configs' / (os.environ['HUMANIZE_SWARM_ATTEMPT'] + '.json')
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text(json.dumps(config, ensure_ascii=False, indent=2) + '\n')
    agent = ('cli=codex,permission=auto,web_search=off,model=' + model_config['model']
             + ',effort=' + model_config.get('model_reasoning_effort', 'high'))
    command = [sys.executable, '-m', 'hmz', 'exec', '-f',
               '/runtime/flows/math-lean-flow:github-theorem-prover', '-c', str(destination),
               '-a', agent, '-a', agent, (project / 'PROBLEM.md').read_text().strip()]
    print(json.dumps({'stage': 'issue-runtime', 'issue': config['github_selected_issue'],
                      'project': config['problem_id'], 'web_search': 'off'}), flush=True)
    os.execvpe(command[0], command, os.environ)


if __name__ == '__main__':
    main()
