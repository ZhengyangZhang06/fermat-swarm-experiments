#!/usr/bin/env python3
"""Operator-only two-node filesystem lock smoke test; never touches proof state."""
import argparse
import fcntl
import json
import os
from pathlib import Path
import socket
import time


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--directory', type=Path, required=True)
    parser.add_argument('--mode', choices=('hold', 'probe'), required=True)
    args = parser.parse_args()
    root = args.directory.resolve(strict=True)
    lock_path = root / 'cross-node.lock'
    if args.mode == 'hold':
        with lock_path.open('a+') as lock:
            fcntl.flock(lock, fcntl.LOCK_EX)
            (root / 'holder.json').write_text(json.dumps({'host': socket.gethostname(), 'pid': os.getpid(),
                'inode': lock_path.stat().st_ino, 'state': 'holding'}))
            deadline = time.monotonic() + 180
            while not (root / 'probe.json').exists() and time.monotonic() < deadline:
                time.sleep(0.5)
            if not (root / 'probe.json').exists():
                raise RuntimeError('probe did not arrive within smoke-test bound')
    else:
        deadline = time.monotonic() + 60
        while not (root / 'holder.json').exists() and time.monotonic() < deadline:
            time.sleep(0.5)
        holder = json.loads((root / 'holder.json').read_text())
        with lock_path.open('a+') as lock:
            blocked = False
            try:
                fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
            except BlockingIOError:
                blocked = True
            result = {'host': socket.gethostname(), 'holder_host': holder['host'],
                      'blocked': blocked, 'same_inode': lock_path.stat().st_ino == holder['inode']}
            (root / 'probe.json').write_text(json.dumps(result))
            if not blocked or not result['same_inode'] or result['host'] == result['holder_host']:
                raise RuntimeError('cross-node lock exclusion failed')
    print(json.dumps({'mode': args.mode, 'passed': True}), flush=True)


if __name__ == '__main__':
    main()
