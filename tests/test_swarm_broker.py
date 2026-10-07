from concurrent.futures import ThreadPoolExecutor
import json
from pathlib import Path
import tempfile
import threading
import unittest
from unittest.mock import Mock
from http.server import ThreadingHTTPServer
from urllib.request import Request, urlopen
from urllib.error import HTTPError

from _recursive_lean.distributed_claims import ClaimLedger, OwnershipError
from _recursive_lean.swarm_broker import Broker, handler
from _recursive_lean.parallel import PROTOCOL


class BrokerTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.catalog = self.root / 'catalog.json'
        self.config = {'repository': 'owner/repo', 'projects': [{
            'id': 'p01', 'root_issue': 1, 'enabled': True,
            'command': ['/trusted/runner'], 'cwd': '/trusted/project',
            'environment': {}, 'log_directory': '/private/logs',
        }]}
        self.save()
        self.broker = Broker(self.catalog, ClaimLedger(self.root / 'claims.sqlite'),
                             'test-only-token-' * 4, self.root / 'snapshot.json', 'gh')
        self.broker.github = Mock(side_effect=lambda repository, resource:
                                  [{'number': 1, 'title': 'Root', 'state': 'open'}]
                                  if resource.startswith('issues?') else {'state': 'open'})
        self.body = {'node': 'hoa0', 'task': 'task000000', 'boot': 'boot000000',
                     'project': 'p01', 'issue': 1, 'attempt': 'attempt0000'}

    def save(self):
        self.catalog.write_text(json.dumps(self.config))

    def test_github_reads_coalesced_but_worker_choices_not_assigned(self):
        self.assertEqual(self.broker.issues()['issues'][0]['issue'], 1)
        self.broker.issues()
        self.broker.github.assert_called_once()
        self.assertEqual(self.broker.ledger.active(), [])

    def test_disabled_projects_cannot_be_claimed(self):
        self.config['projects'][0]['enabled'] = False
        self.save()
        self.assertEqual(self.broker.issues()['issues'], [])
        self.assertIsNone(self.broker.claim(self.body)['claim'])

    def parallel_project(self):
        self.config['projects'][0].update(issue_runtime_protocol=PROTOCOL, issue_numbers=[1, 2])
        self.save()
        self.broker.github = Mock(side_effect=lambda repository, resource:
            [{'number': i, 'title': f'Leaf {i}', 'state': 'open'} for i in (1, 2)]
            if resource.startswith('issues?') else {'state': 'open'})

    def test_parallel_siblings_remain_available_and_claimable(self):
        self.parallel_project()
        first = self.broker.claim(self.body)
        self.assertEqual(first['claim']['scope'], 'issue')
        self.assertEqual(first['job']['environment']['HUMANIZE_SWARM_PROTOCOL'], PROTOCOL)
        self.assertEqual([j['issue'] for j in self.broker.issues()['issues']], [2])
        second = self.broker.claim({**self.body, 'node': 'hoa1', 'issue': 2, 'attempt': 'second'})
        self.assertIsNotNone(second['claim'])
        self.assertEqual(len(self.broker.ledger.active()), 2)

    def test_live_legacy_owner_excludes_new_parallel_grants(self):
        first = self.broker.claim(self.body)
        self.parallel_project()
        self.assertEqual(self.broker.issues()['issues'], [])
        self.assertIsNone(self.broker.claim({**self.body, 'node': 'hoa1', 'issue': 2, 'attempt': 'second'})['claim'])
        self.assertEqual(self.broker.claim(self.body), first)

    def test_new_broker_cannot_recover_or_release_legacy_grant(self):
        first = self.broker.claim(self.body)
        self.config['broker_protocol'] = PROTOCOL
        self.save()
        with self.assertRaises(OwnershipError):
            self.broker.claim(self.body)
        with self.assertRaises(OwnershipError):
            self.broker.release({**self.body, 'claim_token': first['claim']['token'],
                'outcome': 'stopped', 'processes_remaining': 0, 'returncode': 0})

    def test_parallel_failed_issue_is_quarantined_without_stopping_sibling(self):
        self.parallel_project()
        first = self.broker.claim(self.body)
        self.broker.release({**self.body, 'claim_token': first['claim']['token'],
            'outcome': 'stopped', 'processes_remaining': 0, 'returncode': 1})
        project = json.loads(self.catalog.read_text())['projects'][0]
        self.assertTrue(project['enabled'])
        self.assertEqual(project['quarantined_issues'], [1])
        self.assertEqual([j['issue'] for j in self.broker.issues()['issues']], [2])
        self.assertIsNone(self.broker.claim({**self.body, 'attempt': 'retry'})['claim'])

    def test_proved_open_issue_remains_available_for_publication_only_recovery(self):
        self.parallel_project()
        project = self.config['projects'][0]
        project['verification'] = {'project': str(self.root / 'project')}
        artifacts = self.root / 'project/.humanize/github-theorem-prover'
        run = artifacts / 'runs/one'
        run.mkdir(parents=True)
        (artifacts / 'LATEST').write_text('.humanize/github-theorem-prover/runs/one')
        for pr_state in ('', 'open', 'merged'):
            (run / 'dag.json').write_text(json.dumps({'nodes': [dict(id='root', children=[],
                status='proved', github_pr_state=pr_state,
                github_issue_url='https://github.com/owner/repo/issues/1')]}))
            self.assertEqual(self.broker.project_issues(project, 'owner/repo'), [1])

    def test_128_remote_identities_get_only_one_grant(self):
        def request(i):
            return self.broker.claim({**self.body, 'node': f'hoa{i}', 'attempt': f'attempt{i}'})
        with ThreadPoolExecutor(max_workers=128) as pool:
            results = list(pool.map(request, range(128)))
        self.assertEqual(sum(bool(r['claim']) for r in results), 1)
        self.assertEqual(self.broker.issues()['issues'], [])

    def test_uncertain_response_recovers_original_job_after_catalogue_changes(self):
        first = self.broker.claim(self.body)
        self.config['projects'][0].update(enabled=False, command=['/different/runner'])
        self.save()
        second = self.broker.claim(self.body)
        self.assertEqual(first, second)
        self.assertEqual(second['job']['command'], ['/trusted/runner'])

    def test_wrong_identity_cannot_retrieve_existing_grant(self):
        self.broker.claim(self.body)
        with self.assertRaises(OwnershipError):
            self.broker.claim({**self.body, 'node': 'hoa1'})
        with self.assertRaises(OwnershipError):
            self.broker.claim({**self.body, 'issue': 2})

    def test_release_requires_explicit_terminal_process_evidence(self):
        result = self.broker.claim(self.body)
        body = {**self.body, 'claim_token': result['claim']['token'], 'outcome': 'yielded'}
        with self.assertRaises(OwnershipError):
            self.broker.release(body)
        with self.assertRaises(OwnershipError):
            self.broker.release({**body, 'processes_remaining': 1, 'returncode': 0})
        self.broker.release({**body, 'processes_remaining': 0, 'returncode': 0})
        self.assertEqual(self.broker.ledger.active(), [])
        self.assertIsNone(self.broker.claim(self.body)['claim'])

    def test_snapshot_has_no_claim_bearer_token(self):
        result = self.broker.claim(self.body)
        self.broker.heartbeat({**self.body, 'phase': 'working', 'polls': 1})
        snapshot = (self.root / 'snapshot.json').read_text()
        self.assertNotIn(result['claim']['token'], snapshot)
        self.assertNotIn(self.broker.token, snapshot)

    def test_pending_verification_prevents_release(self):
        result = self.broker.claim(self.body)
        self.broker.verifier = Mock()
        self.broker.verifier.pending.return_value = True
        with self.assertRaises(OwnershipError):
            self.broker.release({**self.body, 'claim_token': result['claim']['token'],
                                'outcome': 'yielded', 'processes_remaining': 0, 'returncode': 0})
        self.assertEqual(len(self.broker.ledger.active()), 1)

    def test_new_child_issues_discovered_without_parent_notifications(self):
        project = self.config['projects'][0]
        project['verification'] = {'project': str(self.root / 'project')}
        artifacts = self.root / 'project/.humanize/github-theorem-prover'
        run = artifacts / 'runs/one'
        run.mkdir(parents=True)
        (artifacts / 'LATEST').write_text('.humanize/github-theorem-prover/runs/one')
        nodes = [dict(id='root', children=['child'], status='waiting-children', github_issue_url='https://github.com/owner/repo/issues/1'),
                 dict(id='child', status='queued', workspace_handoff_commit='abc', workspace_bundle_path='bundle',
                      parent_handoff='handoff', github_issue_url='https://github.com/owner/repo/issues/2'),
                 dict(id='obsolete', status='queued', github_issue_url='https://github.com/owner/repo/issues/3')]
        (run / 'dag.json').write_text(json.dumps({'nodes': nodes}))
        self.assertEqual(self.broker.project_issues(project, 'owner/repo'), [2])
        nodes[1]['status'] = 'proved'
        (run / 'dag.json').write_text(json.dumps({'nodes': nodes}))
        self.assertEqual(self.broker.project_issues(project, 'owner/repo'), [1])

    def test_dag_pointer_cannot_escape_project(self):
        project = self.config['projects'][0]
        project['verification'] = {'project': str(self.root / 'project')}
        artifacts = self.root / 'project/.humanize/github-theorem-prover'
        artifacts.mkdir(parents=True)
        (artifacts / 'LATEST').write_text('/tmp/foreign-run')
        with self.assertRaises(ValueError):
            self.broker.project_issues(project, 'owner/repo')

    def test_out_of_scope_node_rejected(self):
        for node in ('hoa128', 'manager', 'hoa-1', 'hoa00'):
            with self.assertRaises(ValueError):
                self.broker.claim({**self.body, 'node': node})

    def test_nonzero_runner_exit_disables_project_until_operator_review(self):
        result = self.broker.claim(self.body)
        self.broker.release({**self.body, 'claim_token': result['claim']['token'],
                             'outcome': 'stopped', 'processes_remaining': 0, 'returncode': 1})
        self.assertFalse(json.loads(self.catalog.read_text())['projects'][0]['enabled'])
        self.assertEqual(self.broker.ledger.active(), [])

    def test_http_authentication_and_health(self):
        # Transport-independent handler test; production CLI requires TLS.
        server = ThreadingHTTPServer(('127.0.0.1', 0), handler(self.broker))
        thread = threading.Thread(target=server.serve_forever, daemon=True)
        thread.start()
        self.addCleanup(server.server_close)
        self.addCleanup(server.shutdown)
        url = f'http://127.0.0.1:{server.server_port}/health'
        with self.assertRaises(HTTPError) as failure:
            urlopen(url)
        self.assertEqual(failure.exception.code, 401)
        request = Request(url, headers={'Authorization': 'Bearer ' + self.broker.token})
        with urlopen(request) as response:
            self.assertTrue(json.load(response)['ok'])


if __name__ == '__main__':
    unittest.main()
