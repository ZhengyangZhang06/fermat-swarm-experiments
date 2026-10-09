"""Browser regressions for minute-boundary and failed live-status fetches.

Run with a Python environment containing Playwright and installed Chromium.
All requests are intercepted; tests make no network requests.
"""
import json
from datetime import datetime, timezone
from pathlib import Path
import unittest

from playwright.sync_api import sync_playwright


ROOT = Path(__file__).resolve().parents[1]


class StatusBrowserTests(unittest.TestCase):
    def setUp(self):
        self.playwright = sync_playwright().start()
        self.addCleanup(self.playwright.stop)
        self.browser = self.playwright.chromium.launch(headless=True)
        self.addCleanup(self.browser.close)
        self.page = self.browser.new_page(viewport={"width": 390, "height": 844})
        self.page.add_init_script("window.setInterval = (fn,ms) => {window.testRefresh = fn; window.testRefreshInterval = ms; return 1}")
        self.mode = "previous-minute"
        self.requests = []
        self.errors = []
        self.verification = None
        self.held_routes = []
        self.addCleanup(self.finish_held_routes)
        self.problems = [dict(id="fermat-p01", nodes=[
            dict(id="fermat-p01/root", problem="fermat-p01", local_id="root",
                 title="Theorem", requires=[], status="decomposing", prose_status="reviewed",
                 observed_running=True, worker_node="hoa3")])]
        self.page.on("pageerror", lambda error: self.errors.append(str(error)))
        self.page.route("**/*", self.route)

    def finish_held_routes(self):
        for route in self.held_routes:
            try:
                route.abort()
            except Exception:
                pass  # Aborted requests may already have left the browser.

    def route(self, route):
        url = route.request.url
        self.requests.append(url)
        if url.endswith("/index.html"):
            return route.fulfill(content_type="text/html", body=(ROOT / "site/index.html").read_text())
        if url.endswith("/campaign.json"):
            return route.fulfill(content_type="application/json", body=(ROOT / "campaign.json").read_text())
        if "api.github.com" in url:
            return route.fulfill(status=403, content_type="application/json",
                                 body='{"message":"API rate limit exceeded"}')
        minute = int(datetime.now(timezone.utc).timestamp() // 60)
        pointer = '/status-live/status.json?' in url
        if self.mode == 'hung' or (self.mode == 'slow-peer' and f'/ticks/{minute}/' in url):
            self.held_routes.append(route)
            return
        if (self.mode not in ('offline', 'pointer') and f"/ticks/{minute-1}/" in url) or (pointer and self.mode in ('pointer', 'stale-pointer')):
            observed = datetime.fromtimestamp((minute-1)*60, timezone.utc)
            snapshot = dict(observed_at=observed.isoformat(), message="Live proof work",
                            readiness_passed=128, running_resolvers=128,
                            verified_integrated_roots=0, problems=self.problems)
            if self.verification is not None:
                snapshot['verification_activity'] = self.verification
            if self.mode == "older" or (self.mode == 'stale-pointer' and pointer):
                snapshot.update(observed_at="2026-01-01T00:00:00Z", running_resolvers=0, problems=[])
            return route.fulfill(content_type="application/json", body=json.dumps(snapshot))
        return route.fulfill(status=404, body="unavailable")

    def test_previous_minute_is_used_and_failures_preserve_progress(self):
        self.page.goto("https://status.test/index.html")
        self.page.wait_for_function("document.querySelector('#resolvers').textContent === '128'")
        self.assertIn("decomposing", self.page.locator("#graph-fermat-p01 .problem-dag").text_content())
        self.assertIn("worker hoa3", self.page.locator("#graph-fermat-p01 .problem-dag").text_content())
        self.mode = "older"
        self.page.evaluate("window.testRefresh()")
        self.assertEqual(self.page.locator("#resolvers").inner_text(), "128")
        self.assertIn("decomposing", self.page.locator("#graph-fermat-p01 .problem-dag").text_content())
        self.mode = "offline"
        self.page.evaluate("window.testRefresh()")
        self.assertIn("refresh incomplete", self.page.locator("#notice").inner_text())
        self.assertIn("decomposing", self.page.locator("#graph-fermat-p01 .problem-dag").text_content())
        self.assertNotIn("https://status.test/status.json", self.requests)
        self.assertFalse(self.page.evaluate("document.documentElement.scrollWidth > innerWidth"))
        self.assertEqual(self.errors, [])

    def test_first_load_failure_does_not_invent_queued_jobs(self):
        self.mode = "offline"
        self.page.goto("https://status.test/index.html")
        self.page.wait_for_function("document.querySelector('#notice').textContent.includes('refresh incomplete')")
        self.page.set_viewport_size({"width": 420, "height": 844})
        self.assertEqual(self.page.locator(".problem-dag a").count(), 0)
        self.assertEqual(self.page.locator("#resolvers").inner_text(), "—")
        self.assertEqual(self.errors, [])

    def test_api_forbidden_does_not_break_dashboard_or_ledger(self):
        root = self.problems[0]['nodes'][0]
        root.update(issue_state='open', pr_state='open')
        self.page.goto('https://status.test/index.html')
        self.page.wait_for_function("document.querySelectorAll('#problems .problem').length === 10")
        self.page.evaluate('window.testRefresh()')
        self.assertEqual(self.page.locator('#notice').inner_text(), 'Live proof work')
        self.assertIn('Published issue state: open', self.page.locator('#problems .state').first.get_attribute('title'))
        root.update(issue_state='closed', pr_state='merged')
        self.page.evaluate('window.testRefresh()')
        self.assertIn('Published issue state: closed; PR merged',
                      self.page.locator('#problems .state').first.get_attribute('title'))
        self.assertEqual(self.page.locator('#verified').inner_text(), '0')
        self.assertFalse(any('api.github.com' in url for url in self.requests))
        self.assertEqual(self.errors, [])

    def test_recent_snapshots_bypass_mutable_pointer_and_previous_cache_keys(self):
        self.open_graphs()
        self.page.evaluate('window.testRefresh()')
        self.assertEqual(self.page.evaluate('window.testRefreshInterval'), 30000)
        previous = [u for u in self.requests if '/status-live/' in u]
        self.assertTrue(previous)
        self.assertTrue(all('/ticks/' in u for u in previous))
        minute = int(datetime.now(timezone.utc).timestamp() // 60)
        self.assertTrue(all(f'/ticks/{minute+1}/' not in u for u in previous))
        self.problems[0]['nodes'][0]['status'] = 'lean-review'
        self.page.evaluate('window.testRefresh()')
        self.assertIn('Checking proof integrity', self.page.locator('#graph-fermat-p01').inner_text())
        current = [u for u in self.requests if '/status-live/' in u]
        self.assertEqual(len(current), len(previous) + 2)
        self.assertEqual(len(set(current)), len(current))
        self.assertTrue(all('?refresh=' in u for u in current))

    def test_slow_fallback_cannot_hold_back_a_fresh_observation(self):
        self.mode = 'slow-peer'
        self.page.goto('https://status.test/index.html', wait_until='domcontentloaded')
        self.page.wait_for_function("document.querySelector('#resolvers').textContent === '128'", timeout=3000)
        self.assertEqual(self.page.locator('#notice').inner_text(), 'Live proof work')
        self.assertTrue(self.held_routes)
        self.assertEqual(self.errors, [])

    def test_cached_stale_pointer_does_not_override_fresh_minute_snapshot(self):
        self.mode = 'stale-pointer'
        self.page.goto('https://status.test/index.html')
        self.page.wait_for_function("document.querySelector('#resolvers').textContent === '128'")
        self.assertNotIn('Activity observation stale', self.page.locator('#problem-graphs').inner_text())
        self.assertTrue(any('/ticks/' in u for u in self.requests))

    def test_timed_out_fetches_release_refresh_for_next_attempt(self):
        self.mode = 'hung'
        self.page.add_init_script("const timer=window.setTimeout;window.setTimeout=(fn,ms,...args)=>timer(fn,ms===10000?100:ms,...args)")
        self.page.goto('https://status.test/index.html', wait_until='domcontentloaded')
        self.page.wait_for_function("document.querySelector('#notice').textContent.includes('refresh incomplete')", timeout=3000)
        self.assertEqual(self.page.locator('#resolvers').inner_text(), '—')
        self.mode = 'pointer'
        self.page.evaluate('window.testRefresh()')
        self.assertEqual(self.page.locator('#resolvers').inner_text(), '128')
        self.assertEqual(self.page.locator('#notice').inner_text(), 'Live proof work')
        self.assertEqual(self.errors, [])

    def test_returning_to_tab_or_network_refreshes_immediately(self):
        self.mode = 'pointer'
        self.open_graphs()
        self.page.evaluate('window.testRefresh()')
        for index, event in enumerate(('focus', 'online', 'pageshow', 'visibilitychange')):
            status = 'lean-review' if index % 2 == 0 else 'rlcr-lean'
            expected = 'Checking proof integrity' if index % 2 == 0 else 'Writing Lean proof'
            self.problems[0]['nodes'][0]['status'] = status
            target = 'document' if event == 'visibilitychange' else 'window'
            self.page.evaluate(f"{target}.dispatchEvent(new Event('{event}'))")
            self.page.wait_for_function("expected => document.querySelector('#graph-fermat-p01').textContent.includes(expected)", arg=expected, timeout=3000)
            self.page.evaluate('window.testRefresh()')
        self.assertEqual(self.errors, [])

    def add_graphs(self):
        def node(problem, local, requires=()):
            return dict(id=f'{problem}/{local}', problem=problem, local_id=local,
                        title=f'{problem}.{local}_descriptive_theorem_name', requires=list(requires),
                        status='waiting-children' if requires else 'decomposing', prose_status='reviewed',
                        issue_url='https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/23',
                        observed_running=local=='child-a', worker_node='hoa6' if local=='child-a' else '')
        self.problems = [dict(id='fermat-p01', nodes=[
            node('fermat-p01', 'root', ['fermat-p01/child-a', 'fermat-p01/child-b']),
            node('fermat-p01', 'child-a'), node('fermat-p01', 'child-b')]),
            dict(id='fermat-p02', nodes=[node('fermat-p02', 'root', ['fermat-p02/child-c']),
                                      node('fermat-p02', 'child-c')])]

    def open_graphs(self):
        self.page.goto('https://status.test/index.html')
        self.page.wait_for_function("document.querySelectorAll('.problem-panel').length === 10")

    def test_each_problem_has_an_independent_graph_and_arrow_markers(self):
        self.add_graphs()
        self.open_graphs()
        self.assertEqual(self.page.locator('.problem-dag').count(), 10)
        self.assertEqual(self.page.locator('#problem-nav a').count(), 10)
        for problem, nodes, edges in [('fermat-p01', 3, 2), ('fermat-p02', 2, 1)]:
            graph = self.page.locator(f'#graph-{problem} .problem-dag')
            self.assertEqual(graph.locator('a').count(), nodes)
            self.assertEqual(graph.locator('.dependency-edge').count(), edges)
            ids = graph.locator('a').evaluate_all('(elements) => elements.map(el => el.dataset.nodeId)')
            self.assertTrue(all(value.startswith(problem + '/') for value in ids))
        self.assertTrue(self.page.evaluate("""[...document.querySelectorAll('.dependency-edge')].every(edge => {
          const id = edge.getAttribute('marker-end').slice(5, -1);
          return document.getElementById(id)?.ownerSVGElement === edge.ownerSVGElement;
        })"""))
        self.assertIn('Awaiting a live observation', self.page.locator('#graph-fermat-p03').inner_text())
        self.assertNotIn('queued', self.page.locator('#problem-graphs').inner_text())
        self.page.locator('#problem-nav a').nth(1).click()
        self.assertTrue(self.page.url.endswith('#graph-fermat-p02'))
        self.assertFalse(self.page.evaluate('document.documentElement.scrollWidth > innerWidth'))
        self.assertEqual(self.errors, [])

    def test_unpublished_child_has_explicit_pending_publication_label(self):
        self.add_graphs()
        child = self.problems[0]['nodes'][1]
        child.update(issue_url='', publication_pending=True, observed_running=False,
                     worker_node='', status='planning')
        self.open_graphs()
        node = self.page.locator('a[data-node-id="fermat-p01/child-a"]')
        self.assertIn('pending issue publication', node.text_content())
        self.assertNotIn('worker hoa6', node.text_content())
        self.assertEqual(self.errors, [])

    def test_dependency_wait_is_primary_and_saved_decomposing_does_not_imply_execution(self):
        self.add_graphs()
        first, second = self.problems[0]['nodes'][1:]
        first.update(issue_url='https://github.com/o/r/issues/140', status='integrating', accepted=False)
        second.update(issue_url='https://github.com/o/r/issues/141', requires=[first['id']],
                      waiting_on=[first['id']], activity_state='waiting-dependencies')
        self.open_graphs()
        node = self.page.locator('a[data-node-id="fermat-p01/child-b"]')
        self.assertEqual(node.locator('.node-activity').text_content(), 'Waiting on #140')
        self.assertEqual(node.locator('.node-saved').text_content(), 'Saved: decomposing')

        second.update(activity_state='executing', observed_running=True, worker_node='hoa54', waiting_on=[])
        self.page.evaluate('window.testRefresh()')
        self.assertEqual(node.locator('.node-activity').text_content(), 'Decomposing')
        self.assertIn('worker hoa54', node.text_content())
        self.mode='offline'
        self.page.evaluate('Date.now = () => ' + str(int((datetime.now(timezone.utc).timestamp()+181)*1000)))
        self.page.evaluate('window.testRefresh()')
        self.assertEqual(node.locator('.node-activity').text_content(), 'Activity observation stale')
        self.assertNotIn('worker hoa54', node.text_content())
        self.assertEqual(self.errors, [])

    def test_provisional_work_and_waiting_draft_are_distinguished(self):
        self.add_graphs()
        root = self.problems[0]['nodes'][0]
        root.update(status='speculative-lean', observed_running=True, worker_node='hoa2')
        self.open_graphs()
        self.assertIn('Writing provisional proof', self.page.locator('#graph-fermat-p01').text_content())
        root.update(status='speculative-ready', observed_running=False,
                    activity_state='waiting-dependencies', waiting_on=root['requires'])
        self.page.evaluate('window.testRefresh()')
        self.page.wait_for_function("document.querySelector('#graph-fermat-p01').textContent.includes('Draft ready; waiting on')")
        self.assertEqual(self.errors, [])

    def test_proved_active_job_shows_publication_then_merge_without_reproving(self):
        self.add_graphs()
        child = self.problems[0]['nodes'][1]
        child.update(status='proved', saved_status='proved', accepted=True,
                     lean_verified=True, integrated=False, observed_running=True,
                     worker_node='hoa93', activity_state='executing', pr_url='', pr_state='')
        self.open_graphs()
        node = self.page.locator('a[data-node-id="fermat-p01/child-a"]')
        self.assertEqual(node.locator('.node-activity').text_content(), 'Verified; publication pending')
        self.assertEqual(node.locator('.node-saved').text_content(), 'Saved: proved')
        self.assertIn('worker hoa93', node.text_content())
        self.assertNotIn('Worker active', node.text_content())
        child.update(pr_url='https://github.com/o/r/pull/632', pr_state='open')
        self.page.evaluate('window.testRefresh()')
        self.assertEqual(node.locator('.node-activity').text_content(), 'Verified; merge pending')
        child.update(pr_state='merged', merge_commit='a'*40, integrated=True)
        self.page.evaluate('window.testRefresh()')
        self.assertEqual(node.locator('.node-activity').text_content(), 'Verified and merged')
        self.assertIn('worker hoa93', node.text_content())  # Finishing a job is still observable.
        child.update(observed_running=False, worker_node='')
        self.page.evaluate('window.testRefresh()')
        self.assertEqual(node.locator('.node-activity').text_content(), 'Verified and merged')
        self.assertNotIn('worker hoa93', node.text_content())
        self.assertEqual(self.errors, [])

    def test_proved_without_worker_or_with_closed_pr_does_not_invent_completion(self):
        self.add_graphs()
        root = self.problems[0]['nodes'][0]
        root.update(status='proved', observed_running=False, integrated=False, pr_url='')
        self.open_graphs()
        node = self.page.locator('a[data-node-id="fermat-p01/root"]')
        self.assertEqual(node.locator('.node-activity').text_content(), 'Verified; publication pending')
        self.assertIn('Verified; publication pending', self.page.locator('#problems .state').first.inner_text())
        root.update(pr_url='https://github.com/o/r/pull/2', pr_state='closed')
        self.page.evaluate('window.testRefresh()')
        self.assertEqual(node.locator('.node-activity').text_content(), 'Verified; PR closed unmerged')
        self.assertNotIn('Verified and merged', node.text_content())
        self.mode = 'offline'
        self.page.evaluate('Date.now = () => ' + str(int((datetime.now(timezone.utc).timestamp()+181)*1000)))
        self.page.evaluate('window.testRefresh()')
        self.assertEqual(node.locator('.node-activity').text_content(), 'Activity observation stale')
        self.assertEqual(self.errors, [])

    def test_comparing_distinguishes_queued_running_and_unobserved_checks(self):
        self.add_graphs()
        observed = datetime.now(timezone.utc).timestamp()
        self.verification = dict(available=True, observed_at=observed,
            counts=dict(queued=2, running=1, starting=0, needs_reconciliation=0, unowned_pending=0))
        states = ['waiting-verification', 'verification-running', 'no-active-check']
        for node, state in zip(self.problems[0]['nodes'], states):
            node.update(status='comparing', saved_status='comparing',
                        verification_activity=dict(state=state, observed_at=observed))
        self.open_graphs()
        graph = self.page.locator('#graph-fermat-p01 .problem-dag')
        self.assertIn('waiting for verification', graph.text_content())
        self.assertIn('verification job running', graph.text_content())
        self.assertIn('no active check observed', graph.text_content())
        self.assertEqual(graph.text_content().count('Saved: comparing'), 3)
        self.assertIn('2 queued · 1 running', self.page.locator('#verification-summary').inner_text())
        self.assertIn('remote preparation', self.page.locator('#verification-summary').inner_text())
        self.assertEqual(self.errors, [])

    def test_stale_verification_labels_expire_even_after_refresh_failure(self):
        self.add_graphs()
        observed = datetime.now(timezone.utc).timestamp()
        self.verification = dict(available=True, observed_at=observed,
            counts=dict(queued=0, running=1, starting=0, needs_reconciliation=0, unowned_pending=0))
        self.problems[0]['nodes'][0].update(status='comparing',
            verification_activity=dict(state='verification-running', observed_at=observed))
        self.open_graphs()
        self.assertIn('verification job running', self.page.locator('#graph-fermat-p01 .problem-dag').text_content())
        self.mode = 'offline'
        self.page.evaluate('Date.now = () => ' + str(int((observed + 181) * 1000)))
        self.page.evaluate('window.testRefresh()')
        graph = self.page.locator('#graph-fermat-p01 .problem-dag')
        self.assertNotIn('verification job running', graph.text_content())
        self.assertIn('check activity unavailable', graph.text_content())
        self.assertIn('Saved: comparing', graph.text_content())
        self.assertIn('unavailable or stale', self.page.locator('#verification-summary').inner_text())
        self.assertEqual(self.errors, [])

    def test_wide_graph_scroll_is_local_and_survives_refresh_and_resize(self):
        self.add_graphs()
        self.open_graphs()
        scroll = self.page.locator('#graph-fermat-p01 .graph-scroll')
        self.assertTrue(scroll.evaluate('(el) => el.scrollWidth > el.clientWidth'))
        self.assertTrue(scroll.evaluate("""(el) => {
          const root=el.querySelector('a[data-node-id="fermat-p01/root"]').getBoundingClientRect();
          const viewport=el.getBoundingClientRect();
          return root.left >= viewport.left && root.right <= viewport.right;
        }"""))
        scroll.evaluate('(el) => el.scrollLeft = 110')
        self.page.evaluate('window.testRefresh()')
        self.assertEqual(scroll.evaluate('(el) => el.scrollLeft'), 110)
        self.page.set_viewport_size({'width': 1440, 'height': 1000})
        self.assertEqual(self.page.locator('.problem-dag').count(), 10)
        self.assertFalse(self.page.evaluate('document.documentElement.scrollWidth > innerWidth'))
        self.assertEqual(self.errors, [])

    def test_cycle_in_one_graph_does_not_hide_other_problems(self):
        self.add_graphs()
        self.problems[0]['nodes'][1]['requires'] = ['fermat-p01/root']
        self.open_graphs()
        self.assertIn('Cyclic theorem dependencies', self.page.locator('#graph-fermat-p01 .graph-message').inner_text())
        self.assertEqual(self.page.locator('#graph-fermat-p02 .problem-dag a').count(), 2)
        self.assertEqual(self.errors, [])

    def test_shared_prerequisite_is_explicitly_labeled_not_merged_into_global_graph(self):
        self.add_graphs()
        self.problems[0]['nodes'][0]['requires'].append('fermat-p02/child-c')
        self.open_graphs()
        shared = self.page.locator('#graph-fermat-p01 a[data-external="true"]')
        self.assertEqual(shared.count(), 1)
        self.assertIn('P02 · shared', shared.text_content())
        self.assertEqual(self.page.locator('#graph-fermat-p02 .problem-dag a').count(), 2)
        self.assertEqual(self.errors, [])


if __name__ == "__main__":
    unittest.main()
