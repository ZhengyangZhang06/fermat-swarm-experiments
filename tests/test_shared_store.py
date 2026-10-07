"""Real-process stale-writer regressions; no model or GitHub calls."""
import json
from concurrent.futures import ThreadPoolExecutor
import multiprocessing
from pathlib import Path
import tempfile
import unittest

from _recursive_lean.models import ProvedTheorem
from _recursive_lean.shared_dag import ACCEPTANCE_FIELDS, StateConflict, validate_nodes
from _recursive_lean.shared_lock import SharedLock
from _recursive_lean.store import Store


def writer(root, node, barrier):
    root = Path(root)
    store = Store(root / 'run', root / 'wiki', 'test', shared=True)
    barrier.wait(timeout=15)
    store.update(node, 'planning', f'worker {node}')


class SharedStoreTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)

    def store(self):
        return Store(self.root / 'run', self.root / 'wiki', 'test', shared=True)

    def seed(self):
        a = self.store()
        a.ensure('root', parent=None, depth=0, title='root', statement='root')
        for key in ('a', 'b'):
            a.ensure(key, parent='root', depth=1, title=key, statement=key,
                     lean_name='Submission.' + key)
        return a

    def test_stale_workers_preserve_independent_node_updates_and_aliases(self):
        a = self.seed()
        b = self.store()
        alias = b.nodes['a']
        a.update('a', 'planning', 'first')
        b.update('b', 'natural-proof', 'second')
        a.refresh()
        self.assertIs(b.nodes['a'], alias)
        self.assertEqual(alias.message, 'first')
        self.assertEqual(a.nodes['b'].message, 'second')

    def test_processes_start_from_same_snapshot(self):
        self.seed()
        ctx = multiprocessing.get_context('spawn')
        barrier = ctx.Barrier(2)
        jobs = [ctx.Process(target=writer, args=(str(self.root), key, barrier))
                for key in ('a', 'b')]
        try:
            for job in jobs:
                job.start()
            for job in jobs:
                job.join(20)
                self.assertEqual(job.exitcode, 0)
        finally:
            for job in jobs:
                if job.is_alive():
                    job.terminate()
                    job.join()
        held = self.store()
        self.assertEqual([held.nodes[k].message for k in ('a', 'b')], ['worker a', 'worker b'])

    def test_conflicting_direct_writes_do_not_overwrite_disk(self):
        a = self.seed()
        b = self.store()
        a.nodes['a'].candidate_commit = 'aaa'
        b.nodes['a'].candidate_commit = 'bbb'
        a.render()
        saved = (a.root / 'dag.json').read_bytes()
        with self.assertRaises(StateConflict):
            b.render()
        self.assertEqual((a.root / 'dag.json').read_bytes(), saved)

    def test_corruption_and_disappearing_state_fail_closed(self):
        a = self.seed()
        path = a.root / 'dag.json'
        path.write_text('{corrupted')
        with self.assertRaises(StateConflict):
            a.render()
        with self.assertRaises(StateConflict):
            self.store()
        self.assertEqual(path.read_text(), '{corrupted')
        path.unlink()
        with self.assertRaises(StateConflict):
            a.render()

    def test_stale_update_cannot_regress_checkpoint(self):
        a = self.seed()
        b = self.store()
        a.update('a', 'proved', 'verified', candidate_commit='accepted')
        b.update('a', 'planning', 'stale retry')
        self.assertEqual(b.nodes['a'].status, 'proved')
        b.nodes['a'].candidate_commit = 'replacement'
        with self.assertRaises(StateConflict):
            b.render()

    def test_local_acceptance_cannot_acquire_remote_contract_change(self):
        a = self.seed()
        b = self.store()
        a.nodes['a'].status = 'proved'
        a.nodes['a'].candidate_commit = 'accepted-old-contract'
        b.nodes['a'].statement = 'new unverified statement'
        b.render()
        with self.assertRaises(StateConflict):
            a.render()
        self.assertEqual(self.store().nodes['a'].status, 'queued')

    def test_acceptance_bundle_cannot_be_replaced_by_stale_writer(self):
        for field in ACCEPTANCE_FIELDS:
            if field in {'id', 'parent', 'depth'}:
                continue
            with self.subTest(field=field):
                a = self.store()
                if 'root' not in a.nodes:
                    a = self.seed()
                    a.update('a', 'proved', candidate_commit='accepted')
                b = self.store()
                old = getattr(b.nodes['a'], field)
                setattr(b.nodes['a'], field, ['unreviewed'] if isinstance(old, list) else 'unreviewed')
                with self.assertRaises((StateConflict, ValueError)):
                    b.render()

    def test_verified_integration_and_remote_publication_can_advance(self):
        a = self.seed()
        a.update('a', 'integrating', candidate_commit='checked', theorems=['Submission.a'])
        b = self.store()
        a.update('a', 'proved', integrated_commit='combined-checked')
        b.nodes['a'].github_pr_url = 'https://github.com/example/proofs/pull/7'
        b.nodes['a'].github_pr_commit = 'published-checked'
        b.nodes['a'].github_pr_state = 'open'
        b.render()
        a.refresh()
        self.assertEqual(a.nodes['a'].status, 'proved')
        self.assertEqual(a.nodes['a'].candidate_commit, 'checked')
        self.assertEqual(a.nodes['a'].integrated_commit, 'combined-checked')
        self.assertEqual(a.nodes['a'].github_pr_state, 'open')
        a.nodes['a'].github_pr_state = 'merged'
        a.nodes['a'].github_merge_commit = 'verified-remote-tree'
        a.nodes['a'].github_issue_state = 'closed'
        a.render()
        b.refresh()
        self.assertEqual(b.nodes['a'].github_pr_state, 'merged')
        self.assertEqual(b.nodes['a'].github_issue_state, 'closed')

    def test_invalid_metadata_and_duplicate_identities_fail_at_load(self):
        a = self.seed()
        path = a.root / 'dag.json'
        payload = json.loads(path.read_text())
        for change in ({'required_references': 42}, {'task': None}, {'nodes': None},
                       {'nodes': payload['nodes'] + [payload['nodes'][0]]}):
            path.write_text(json.dumps(dict(payload, **change)))
            with self.assertRaises(StateConflict):
                self.store()
        payload['nodes'][1]['depends_on'] = ['root']
        path.write_text(json.dumps(payload))
        with self.assertRaises(StateConflict):
            self.store()

    def test_concurrent_wiki_publications_retain_every_link(self):
        self.seed()
        def publish(i):
            s = self.store()
            theorem = ProvedTheorem(name=f'Submission.lemma{i}', statement='True',
                                    lean_file='Submission.lean', natural_summary='A checked proof.')
            return s.publish(s.nodes['a'], theorem, plan='plan', natural='proof', comparator_log='passed')
        with ThreadPoolExecutor(max_workers=16) as pool:
            pages = list(pool.map(publish, range(32)))
        index = (self.root / 'wiki' / 'README.md').read_text()
        for page in pages:
            self.assertIn(page.name, index)

    def test_sibling_appends_preserve_both(self):
        a = self.seed()
        b = self.store()
        a.ensure('c', parent='root', depth=1, title='c', statement='c')
        b.ensure('d', parent='root', depth=1, title='d', statement='d')
        self.assertEqual(set(self.store().nodes['root'].children), {'a', 'b', 'c', 'd'})

    def test_duplicate_declarations_cycles_and_missing_dependencies_rejected(self):
        a = self.seed()
        a.nodes['b'].lean_name = a.nodes['a'].lean_name
        with self.assertRaises(StateConflict):
            a.render()
        a = self.store()
        a.nodes['a'].depends_on = ['b']
        a.nodes['b'].depends_on = ['a']
        with self.assertRaises(StateConflict):
            a.render()
        a = self.store()
        a.nodes['a'].depends_on = ['missing']
        with self.assertRaises(StateConflict):
            validate_nodes({k: n.model_dump(mode='json') for k, n in a.nodes.items()}, complete=True)

    def test_metadata_preserved_across_writers(self):
        a = self.seed()
        b = self.store()
        a.reference_manifest = 'pinned'
        a.render()
        b.update('b', 'planning')
        self.assertEqual(self.store().reference_manifest, 'pinned')

    def test_two_instances_reenter_same_lock_and_keep_inode(self):
        path = self.root / 'lock'
        with SharedLock(path):
            inode = path.stat().st_ino
            with SharedLock(path):
                self.assertEqual(path.stat().st_ino, inode)
        self.assertEqual(path.stat().st_ino, inode)


if __name__ == '__main__':
    unittest.main()
