import json
import os
from pathlib import Path
import sqlite3
import tempfile
import unittest
from unittest.mock import patch

from _recursive_lean.verification_status import (
    observe_verifications, attach_verification_activity, process_matches,
)


class VerificationStatusTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.database = Path(self.temp.name) / 'claims.sqlite'
        with sqlite3.connect(self.database) as db:
            db.execute('CREATE TABLE claims (attempt TEXT,project TEXT,repository TEXT,issue INTEGER,state TEXT)')
            db.execute('CREATE TABLE verifications (attempt TEXT,state TEXT,pid INTEGER,start_ticks TEXT,request TEXT)')
            db.execute("INSERT INTO claims VALUES ('a','p1','o/r',7,'owned')")
        self.node = dict(local_id='child', status='comparing', issue_url='https://github.com/o/r/issues/7',
                         observed_running=True, lean_verified=False, integrated=False)
        self.proofs = [dict(id='p1', nodes=[self.node])]

    def add(self, state, *, attempt='a', node='child', revision='a'*40, pid=123, ticks='456'):
        request = dict(node_id=node, revision=revision, candidate='/secret/path', token='secret-canary')
        with sqlite3.connect(self.database) as db:
            db.execute('INSERT INTO verifications VALUES (?,?,?,?,?)',
                       (attempt, state, pid, ticks, json.dumps(request)))

    def observe(self, live=True):
        return observe_verifications(self.database, 'o/r', stamp=100,
                                     process_check=lambda pid, ticks: live and (pid, ticks) == (123, '456'))

    def attach(self, observation=None, stamp=100):
        observation = observation or self.observe()
        attach_verification_activity(self.proofs, observation, 'o/r', stamp=stamp)
        return self.node['verification_activity']

    def test_queue_is_not_execution_and_saved_stage_remains(self):
        self.add('queued')
        self.assertEqual(self.attach()['state'], 'waiting-verification')
        self.assertEqual(self.node['saved_status'], 'comparing')
        self.assertTrue(self.node['observed_running'])
        self.assertFalse(self.node['lean_verified'])

    def test_live_job_needs_exact_pid_and_start_identity(self):
        self.add('running')
        self.assertEqual(self.attach()['state'], 'verification-running')
        self.assertEqual(self.attach(self.observe(live=False))['state'], 'needs-reconciliation')
        self.assertEqual(self.observe(live=False)['counts']['running'], 0)

    def test_starting_uncertain_finished_do_not_imply_running_or_acceptance(self):
        for state, expected in [('spawning', 'starting'), ('uncertain', 'needs-reconciliation'),
                                ('finished', 'no-active-check')]:
            with self.subTest(state=state):
                with sqlite3.connect(self.database) as db:
                    db.execute('DELETE FROM verifications')
                self.add(state)
                self.assertEqual(self.attach()['state'], expected)
                self.assertFalse(self.node['integrated'])
                self.assertFalse(self.node['lean_verified'])

    def test_multiple_candidates_and_finished_history_are_not_latest_wins(self):
        self.add('running')
        self.add('queued', revision='b'*40)
        self.add('finished', revision='c'*40)
        activity = self.attach()
        self.assertEqual(activity['state'], 'verification-running')
        self.assertEqual(activity['pending_revisions'], 2)
        self.assertEqual(activity['counts']['queued'], 1)
        self.add('uncertain', revision='d'*40)
        self.assertEqual(self.attach()['state'], 'needs-reconciliation')

    def test_old_claim_does_not_attach_to_new_owner(self):
        self.add('running')
        with sqlite3.connect(self.database) as db:
            db.execute("UPDATE claims SET state='released'")
            db.execute("INSERT INTO claims VALUES ('b','p1','o/r',7,'owned')")
        self.add('queued', attempt='b')
        observation = self.observe()
        self.assertEqual(observation['counts']['unowned_pending'], 1)
        self.assertEqual(self.attach(observation)['state'], 'waiting-verification')

    def test_conflicting_owned_attempts_require_reconciliation(self):
        self.add('queued')
        with sqlite3.connect(self.database) as db:
            db.execute("INSERT INTO claims VALUES ('b','p1','o/r',7,'owned')")
        self.add('running', attempt='b')
        self.assertEqual(self.attach()['state'], 'needs-reconciliation')

    def test_repository_project_issue_and_node_all_must_match(self):
        self.add('running')
        for field, value in [('local_id', 'other'), ('issue_url', 'https://github.com/x/y/issues/7'),
                             ('issue_url', 'https://github.com/o/r/issues/8')]:
            old = self.node[field]
            self.node[field] = value
            self.assertEqual(self.attach()['state'], 'no-active-check')
            self.node[field] = old
        self.proofs[0]['id'] = 'p2'
        self.assertEqual(self.attach()['state'], 'no-active-check')
        self.assertEqual(observe_verifications(self.database, 'other/repo')['counts']['running'], 0)

    def test_github_repository_identity_is_case_insensitive(self):
        self.add('queued')
        observation = observe_verifications(self.database, 'O/R', stamp=100)
        self.assertEqual(observation['counts']['queued'], 1)
        attach_verification_activity(self.proofs, observation, 'O/R', stamp=100)
        self.assertEqual(self.node['verification_activity']['state'], 'waiting-verification')

    def test_missing_corrupt_stale_and_future_observations_are_unknown(self):
        missing = self.database.with_name('missing')
        self.assertFalse(observe_verifications(missing, 'o/r')['available'])
        self.assertFalse(missing.exists())
        missing.write_text('not sqlite')
        self.assertFalse(observe_verifications(missing, 'o/r')['available'])
        self.add('running')
        for stamp in (99, 281):
            self.assertEqual(self.attach(stamp=stamp)['state'], 'unavailable')
        self.assertEqual(self.attach(dict(available=False, observed_at=100))['state'], 'unavailable')

    def test_observer_is_readonly_and_allowlisted(self):
        self.add('queued')
        before = self.database.read_bytes()
        observation = self.observe()
        self.attach(observation)
        self.assertEqual(before, self.database.read_bytes())
        for secret in ('secret-canary', '/secret/path', 'candidate', 'start_ticks', '"pid"'):
            self.assertNotIn(secret, json.dumps([observation, self.proofs]))

    def test_corrupt_request_fails_closed_without_publishing_partial_counts(self):
        self.add('queued')
        with sqlite3.connect(self.database) as db:
            db.execute("UPDATE verifications SET request='broken'")
        observation = self.observe()
        self.assertFalse(observation['available'])
        self.assertIsNone(observation['counts'])

    def test_process_matches_reused_zombie_missing_handles(self):
        current = Path(f'/proc/{os.getpid()}/stat').read_text().rsplit(')', 1)[1].split()
        self.assertTrue(process_matches(os.getpid(), current[19]))
        self.assertFalse(process_matches(os.getpid(), '0'))
        self.assertFalse(process_matches(None, None))
        with patch('pathlib.Path.read_text', side_effect=PermissionError):
            self.assertFalse(process_matches(123, '456'))
        with patch('pathlib.Path.read_text', return_value='123 (a tricky) name) Z ' + '0 '*18 + '456'):
            self.assertFalse(process_matches(123, '456'))


if __name__ == '__main__':
    unittest.main()
