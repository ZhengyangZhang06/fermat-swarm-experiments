"""Read-only, allowlisted verification observations, separate from proof acceptance.

Run on the ledger's controller: PIDs are controller-local dispatcher/checker
handles. A live remote adapter is a running verification *job*, not evidence that
a remote Lean compiler is currently busy. No claim or verification is modified.
"""
import json
from contextlib import closing
from pathlib import Path
import re
import sqlite3
import time


def process_matches(pid, start_ticks):
    """Missing, inaccessible, zombie and reused process handles are not live evidence."""
    try:
        if type(pid) is not int or pid <= 0 or not str(start_ticks).isdigit():
            return False
        stat = Path(f'/proc/{pid}/stat').read_text().rsplit(')', 1)[1].split()
        return stat[0] not in ('Z', 'X') and stat[19] == str(start_ticks)
    except (OSError, IndexError):
        return False


def observe_verifications(database, repository, *, stamp=None, process_check=process_matches):
    """Read one SQL snapshot; never publish paths, request bodies, logs or credentials.

    Unfinished checks of released claims count in aggregate but cannot attach to
    a newer owner. Multiple requests/revisions remain counts, never 'latest wins'.
    Missing/corrupt evidence means unavailable, not an empty queue.
    """
    stamp = time.time() if stamp is None else stamp
    result = dict(available=False, observed_at=stamp, counts=None, nodes=[])
    counts = dict(queued=0, running=0, starting=0, needs_reconciliation=0,
                  finished=0, unowned_pending=0)
    grouped = {}
    try:
        uri = Path(database).absolute().as_uri() + '?mode=ro'
        with closing(sqlite3.connect(uri, uri=True, timeout=2)) as db:
            db.row_factory = sqlite3.Row
            db.execute('PRAGMA query_only=ON')
            rows = db.execute('''SELECT v.state, v.pid, v.start_ticks, v.request,
                c.attempt, c.project, c.repository, c.issue, c.state AS claim_state
                FROM verifications v JOIN claims c ON c.attempt=v.attempt
                WHERE c.repository=? COLLATE NOCASE''', (repository,)).fetchall()
        for row in rows:
            state = row['state']
            activity = ('running' if process_check(row['pid'], row['start_ticks']) else
                        'needs_reconciliation') if state == 'running' else {
                'queued': 'queued', 'spawning': 'starting', 'finished': 'finished',
                'uncertain': 'needs_reconciliation',
            }.get(state, 'needs_reconciliation')
            counts[activity] += 1
            if row['claim_state'] != 'owned':
                counts['unowned_pending'] += activity != 'finished'
                continue
            request = json.loads(row['request'])
            node_id, revision = request['node_id'], request['revision']
            if (not isinstance(node_id, str) or not re.fullmatch(r'[A-Za-z0-9_.-]+', node_id)
                    or not isinstance(revision, str) or not re.fullmatch(r'[a-f0-9]{40}', revision)
                    or type(row['issue']) is not int or row['issue'] < 1):
                raise ValueError('invalid verification identity')
            key = (row['project'], row['issue'], node_id)
            group = grouped.setdefault(key, dict(counts=dict(queued=0, running=0, starting=0,
                needs_reconciliation=0, finished=0), attempts=set(), revisions=set()))
            group['counts'][activity] += 1
            group['attempts'].add(row['attempt'])
            if activity != 'finished':
                group['revisions'].add(revision)
        nodes = []
        for (project, issue, node_id), group in grouped.items():
            nodes.append(dict(project=project, issue=issue, node_id=node_id,
                counts=group['counts'], ambiguous_ownership=len(group['attempts']) > 1,
                pending_revisions=len(group['revisions'])))
        result.update(available=True, counts=counts, nodes=nodes)
    except (OSError, sqlite3.Error, ValueError, KeyError, TypeError):
        pass
    return result


def attach_verification_activity(proofs, observation, repository, *, stamp=None, freshness=180):
    """Keep saved proof stage and worker activity intact; add bounded observation only."""
    stamp = time.time() if stamp is None else stamp
    observed_at = observation.get('observed_at')
    fresh = (isinstance(observed_at, (int, float)) and
             0 <= stamp - observed_at <= freshness)
    available = observation.get('available') is True and fresh
    groups = {(n['project'], n['issue'], n['node_id']): n
              for n in observation.get('nodes', [])} if available else {}
    for problem in proofs:
        for node in problem['nodes']:
            node['saved_status'] = node.get('status', 'unknown')
            url = node.get('issue_url', '')
            match = re.fullmatch(r'https://github\.com/' + re.escape(repository) +
                                 r'/issues/([1-9][0-9]*)', url, flags=re.IGNORECASE)
            group = groups.get((problem['id'], int(match[1]), node.get('local_id'))) if match else None
            counts = dict(group['counts']) if group else None
            state = 'unavailable' if not available else 'no-active-check'
            if group:
                if group['ambiguous_ownership'] or counts['needs_reconciliation']:
                    state = 'needs-reconciliation'
                elif counts['running']:
                    state = 'verification-running'
                elif counts['starting']:
                    state = 'starting'
                elif counts['queued']:
                    state = 'waiting-verification'
            node['verification_activity'] = dict(state=state, counts=counts,
                pending_revisions=group['pending_revisions'] if group else 0,
                observed_at=observed_at)
