#!/usr/bin/env python3
"""Populate a container-local authorized home, then start its autonomous poller."""
import os
from pathlib import Path
import pwd
import shutil
import subprocess
import sys
import tempfile
import tomllib
import uuid
from urllib.parse import urlsplit


def main():
    os.umask(0o077)
    if os.geteuid() == 0:
        try:
            account = pwd.getpwuid(1000)
        except KeyError:
            subprocess.run(['/usr/sbin/useradd', '--uid', '1000', '--user-group', '--home-dir', '/home/ubuntu',
                            '--no-create-home', 'ubuntu'], check=True)
            account = pwd.getpwuid(1000)
        if account.pw_dir != '/home/ubuntu':
            raise RuntimeError('Unexpected container worker account')
    home = Path('/home/ubuntu')
    codex = home / '.codex'
    ssh = home / '.ssh'
    humanize = home / '.humanize'
    for directory in (codex, ssh, humanize):
        directory.mkdir(parents=True, exist_ok=True)
        if os.geteuid() == 0:
            os.chown(directory, 1000, 1000)
    for source, target in (('codex_auth', codex / 'auth.json'), ('codex_config', codex / 'config.toml'),
                           ('github_ssh', ssh / 'id_ed25519'), ('github_hosts', ssh / 'known_hosts')):
        shutil.copyfile('/run/secrets/' + source, target)
        target.chmod(0o600)
        if os.geteuid() == 0:
            os.chown(target, 1000, 1000)
    config = tomllib.loads((codex / 'config.toml').read_text())
    provider = config.get('model_providers', {}).get(config.get('model_provider'), {})
    host = (urlsplit(provider.get('base_url', '')).hostname or '').casefold()
    if host == 'rust.cat' or host.endswith('.rust.cat'):
        raise RuntimeError('Forbidden provider configuration')
    flowverses = humanize / 'flowverses'
    if not flowverses.exists():
        flowverses.symlink_to('/runtime/flowverses')
    os.environ.update(CODEX_HOME=str(codex), HUMANIZE_HOME=str(humanize),
        GH_TOKEN=Path('/run/secrets/github_token').read_text().strip(),
        GIT_SSH_COMMAND='ssh -F /dev/null -o BatchMode=yes -o IdentitiesOnly=yes -o StrictHostKeyChecking=yes '
                        '-o UserKnownHostsFile=/home/ubuntu/.ssh/known_hosts -i /home/ubuntu/.ssh/id_ed25519',
        GIT_AUTHOR_NAME='Fermat Experiment', GIT_AUTHOR_EMAIL='fermat-experiment@example.invalid',
        GIT_COMMITTER_NAME='Fermat Experiment', GIT_COMMITTER_EMAIL='fermat-experiment@example.invalid')
    if os.geteuid() == 0:
        os.setgroups([])
        os.setgid(1000)
        os.setuid(1000)
    if '--check' in sys.argv:
        subprocess.run(['git', 'ls-remote', '--heads', 'git@github.com:ZhengyangZhang06/fermat-swarm-experiments.git',
                        'experiments/fermat-p04'], check=True, timeout=60)
        print('Worker uid, SSH transport and authorized home check passed', flush=True)
        return
    if '--tool-check' in sys.argv:
        # The random challenge is never included in the prompt: a matching
        # answer requires a successful tool read, not just model authentication.
        with tempfile.TemporaryDirectory(prefix='swarm-tool-check-') as temporary:
            root = Path(temporary)
            challenge = uuid.uuid4().hex
            (root / 'challenge.txt').write_text(challenge)
            result_path = root / 'answer.txt'
            result = subprocess.run(['/runtime/bin/codex', 'exec', '--skip-git-repo-check',
                '--dangerously-bypass-approvals-and-sandbox', '-m', config['model'],
                '-c', 'web_search="disabled"', '--output-last-message', str(result_path),
                'Runtime tool test only. Use the shell tool to read challenge.txt in the current '
                'directory, then reply with exactly its contents. Do not read any other file, '
                'access credentials, use network/search, or change files.'], cwd=root,
                capture_output=True, text=True, timeout=300)
            answer = result_path.read_text().strip() if result_path.exists() else ''
            if result.returncode or answer != challenge:
                raise RuntimeError('Worker real tool-execution smoke test failed')
        print('Authenticated model and real local tool-execution check passed', flush=True)
        return
    os.execv(sys.executable, [sys.executable, '/runtime/flows/math-lean-flow/scripts/swarm-worker.py',
        '--endpoint', 'https://10.44.0.210:8847', '--certificate', '/broker.crt',
        '--token-file', '/run/secrets/broker_token'])


if __name__ == '__main__':
    main()
