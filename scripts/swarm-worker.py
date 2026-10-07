#!/usr/bin/env python3
"""One autonomous pull worker per Swarm node; no parent job notifications.

TLS authenticates the broker. A scoped Docker secret authenticates this worker.
An uncertain claim or process never triggers timeout-based reassignment.
"""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import random
import signal
import ssl
import subprocess
import threading
import time
import uuid
from urllib.request import Request, urlopen


class Worker:
    def __init__(self, endpoint, certificate, token_file, node, task, interval=15):
        if not endpoint.startswith('https://'):
            raise ValueError('TLS broker URL required')
        self.endpoint = endpoint.rstrip('/')
        self.context = ssl.create_default_context(cafile=str(certificate))
        self.token = token_file.read_text().strip()
        self.identity = {'node': node, 'task': task, 'boot': uuid.uuid4().hex}
        self.interval, self.polls = interval, 0
        self.stop = threading.Event()
        self.phase, self.issue = 'starting', None
        self.held = None
        self.lock = threading.Lock()

    def request(self, path, body=None):
        data = json.dumps(body).encode() if body is not None else None
        request = Request(self.endpoint + path, data=data, headers={
            'Authorization': 'Bearer ' + self.token, 'Content-Type': 'application/json',
        })
        with urlopen(request, context=self.context, timeout=90) as response:
            return json.load(response)

    def retry(self, path, body):
        # Retain the SAME attempt after a lost response. Never request a new job
        # while ownership is uncertain, even if the broker is temporarily down.
        previous_phase = self.phase
        while True:
            try:
                result = self.request(path, body)
                self.phase = previous_phase
                return result
            except Exception as exc:
                print(f'broker response uncertain: {type(exc).__name__}; retaining identity', flush=True)
                self.phase = 'uncertain'
                time.sleep(5)

    def heartbeat(self):
        while not self.stop.is_set():
            try:
                self.request('/heartbeat', {**self.identity, 'phase': self.phase,
                             'issue': self.issue, 'polls': self.polls})
            except Exception as exc:
                print(f'heartbeat unavailable: {type(exc).__name__}', flush=True)
            self.stop.wait(15)

    @staticmethod
    def remaining_processes():
        # The container is dedicated to this worker. Refuse to release if an
        # escaped RLCR/Codex child still exists, including reparented descendants.
        remaining = []
        for entry in Path('/proc').iterdir():
            if not entry.name.isdigit() or int(entry.name) in {os.getpid(), 1}:
                continue
            try:
                state = (entry / 'stat').read_text().rsplit(')', 1)[1].split()[0]
                if state not in {'Z', 'X'}:
                    remaining.append(int(entry.name))
            except (OSError, IndexError):
                continue
        return remaining

    def execute(self, response):
        claim, job = response['claim'], response['job']
        self.phase, self.issue = 'working', claim['issue']
        owned = {**self.identity, 'attempt': claim['attempt'], 'claim_token': claim['token']}
        env = os.environ.copy()
        env.update(job['environment'])
        env.update(HUMANIZE_SELECTED_ISSUE=str(claim['issue']),
                   HUMANIZE_SWARM_OWNER=claim['owner'], HUMANIZE_SWARM_ATTEMPT=claim['attempt'],
                   HUMANIZE_SWARM_BOOT=self.identity['boot'], HUMANIZE_SWARM_CLAIM_TOKEN=claim['token'])
        directory = Path(job['log_directory'])
        directory.mkdir(parents=True, exist_ok=True)
        log = directory / f"{claim['attempt']}.log"
        self.retry('/observe', {**owned, 'receipt': {'state': 'spawn-intent', **self.identity}})
        try:
            with log.open('ab', buffering=0) as output:
                process = subprocess.Popen(job['command'], cwd=job['cwd'], env=env,
                                           stdout=output, stderr=subprocess.STDOUT, start_new_session=True)
                self.retry('/observe', {**owned, 'receipt': {
                    'state': 'running', **self.identity, 'pid': process.pid,
                    'log': str(log), 'started_at': time.time(),
                }})
                print(f"claimed issue #{claim['issue']} on {self.identity['node']}; proof process started", flush=True)
                while process.poll() is None:
                    # On shutdown leave ownership reserved. Swarm terminates the
                    # container's complete process tree; an operator reconciles it.
                    if self.stop.wait(1):
                        os.killpg(process.pid, signal.SIGTERM)
                        return
                code = process.returncode
        except OSError:
            # Even a spawn failure is conservatively reserved for reconciliation.
            self.phase = 'uncertain'
            raise
        remaining = self.remaining_processes()
        if remaining:
            self.phase = 'uncertain'
            self.retry('/observe', {**owned, 'receipt': {
                'state': 'descendants-remain', **self.identity, 'remaining': remaining, 'returncode': code,
            }})
            raise RuntimeError('refusing to release a claim with live descendants')
        self.retry('/observe', {**owned, 'receipt': {
            'state': 'terminal', **self.identity, 'returncode': code, 'ended_at': time.time(),
        }})
        self.retry('/release', {**owned, 'processes_remaining': 0, 'returncode': code,
                               'outcome': 'yielded' if code == 0 else 'stopped'})
        self.held = None
        self.phase, self.issue = 'idle', None

    def run(self):
        threading.Thread(target=self.heartbeat, daemon=True).start()
        while not self.stop.is_set():
            try:
                self.phase = 'polling'
                available = self.request('/issues')['issues']
                self.polls += 1
                random.shuffle(available)
                for selected in available:
                    if self.stop.is_set():
                        break
                    request = {**self.identity, 'project': selected['project'],
                               'issue': selected['issue'], 'attempt': uuid.uuid4().hex}
                    response = self.retry('/claim', request)
                    if response.get('claim'):
                        self.held = response['claim']
                        self.execute(response)
                        break
                self.phase = 'idle'
            except Exception as exc:
                print(f'poll/resolve failure: {type(exc).__name__}', flush=True)
                if self.held or self.phase == 'uncertain':
                    self.phase = 'uncertain'
                    # Do not obtain another claim until an operator reconciles this
                    # process. Heartbeats continue so this is visibly not healthy idle.
                    self.stop.wait()
                    return
                self.phase = 'error'
            self.stop.wait(self.interval * random.uniform(.8, 1.2))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--endpoint', required=True)
    parser.add_argument('--certificate', required=True, type=Path)
    parser.add_argument('--token-file', required=True, type=Path)
    parser.add_argument('--node', default=os.environ.get('SWARM_NODE', ''))
    parser.add_argument('--task', default=os.environ.get('SWARM_TASK', ''))
    args = parser.parse_args()
    os.umask(0o077)
    worker = Worker(args.endpoint, args.certificate, args.token_file, args.node, args.task)
    signal.signal(signal.SIGTERM, lambda *_: worker.stop.set())
    signal.signal(signal.SIGINT, lambda *_: worker.stop.set())
    worker.run()


if __name__ == '__main__':
    main()
