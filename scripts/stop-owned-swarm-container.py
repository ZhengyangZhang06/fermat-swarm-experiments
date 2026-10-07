#!/usr/bin/env python3
"""Operator-only graceful stop of one exactly identified legacy resolver.

Run only on the task's node. This never releases its claim or changes proof
acceptance. The operator must separately reconcile all verifier descendants.
"""
import argparse
import http.client
import json
import re
import socket


class DockerConnection(http.client.HTTPConnection):
    def connect(self):
        self.sock = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
        self.sock.settimeout(self.timeout)
        self.sock.connect('/var/run/docker.sock')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--container', required=True)
    parser.add_argument('--task', required=True)
    parser.add_argument('--service', required=True)
    args = parser.parse_args()
    if not re.fullmatch('[a-f0-9]{64}', args.container) or not re.fullmatch('[a-z0-9]{25}', args.task):
        raise RuntimeError('invalid exact container/task identity')
    conn = DockerConnection('localhost', timeout=60)
    conn.request('GET', f'/containers/{args.container}/json')
    response = conn.getresponse()
    if response.status != 200:
        raise RuntimeError('target container not present')
    record = json.loads(response.read())
    labels = record['Config']['Labels']
    if (record['Id'] != args.container or labels.get('com.docker.swarm.task.id') != args.task
            or labels.get('com.docker.swarm.service.name') != args.service):
        raise RuntimeError('target differs from the authorized task')
    if record['State']['Running']:
        conn.request('POST', f'/containers/{args.container}/stop?t=30')
        response = conn.getresponse()
        response.read()
        if response.status not in (204, 304):
            raise RuntimeError('graceful container stop failed')
    print(json.dumps({'task': args.task, 'container': args.container, 'stop_requested': True,
                      'claim_released': False}), flush=True)


if __name__ == '__main__':
    main()
