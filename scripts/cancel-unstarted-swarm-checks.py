#!/usr/bin/env python3
"""Cancel queued (never spawned) checks after their exact owner task terminates.

The cancellation is failure, not proof evidence. Running/uncertain checks are
never changed here and continue to prevent claim release.
"""
import argparse
import json
from pathlib import Path
import sqlite3
import subprocess


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--database', required=True, type=Path)
    p.add_argument('--attempt', required=True)
    args = p.parse_args()
    db = sqlite3.connect(args.database, timeout=60)
    db.row_factory = sqlite3.Row
    with db:
        db.execute('BEGIN IMMEDIATE')
        claim = db.execute('SELECT * FROM claims WHERE attempt=?', (args.attempt,)).fetchone()
        if not claim or claim['scope'] != 'project' or claim['state'] != 'owned':
            raise RuntimeError('expected an owned legacy claim')
        task_id = claim['owner'].split('/')[1]
        task = json.loads(subprocess.check_output(['sudo', '-n', 'docker', 'inspect', '--type', 'task', task_id]))[0]
        status = task['Status']
        container = status.get('ContainerStatus', {})
        if (status['State'] not in {'complete', 'failed', 'shutdown'}
                or type(container.get('ExitCode')) is not int or container.get('PID', 0) != 0):
            raise RuntimeError('exact owner task is not terminal')
        checks = db.execute("SELECT * FROM verifications WHERE attempt=? AND state='queued'", (args.attempt,)).fetchall()
        for check in checks:
            if check['pid'] is not None or check['start_ticks'] is not None:
                raise RuntimeError('queued check unexpectedly has a process identity')
            log = Path(check['log']).resolve()
            if not log.is_relative_to(args.database.resolve().parent / 'verification'):
                raise RuntimeError('check log outside private verification directory')
            with log.open('a') as out:
                out.write('\nOPERATOR CANCELLED BEFORE SPAWN: exact owner task terminal; parallel cutover; no proof accepted.\n')
            db.execute("UPDATE verifications SET state='finished',returncode=125 WHERE id=? AND state='queued'", (check['id'],))
            print(json.dumps({'request': check['id'], 'cancelled_before_spawn': True, 'proof_accepted': False}))


if __name__ == '__main__':
    main()
