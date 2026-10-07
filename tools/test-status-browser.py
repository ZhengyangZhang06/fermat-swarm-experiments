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
        self.page.add_init_script("window.setInterval = fn => {window.testRefresh = fn; return 1}")
        self.mode = "previous-minute"
        self.requests = []
        self.errors = []
        self.page.on("pageerror", lambda error: self.errors.append(str(error)))
        self.page.route("**/*", self.route)

    def route(self, route):
        url = route.request.url
        self.requests.append(url)
        if url.endswith("/index.html"):
            return route.fulfill(content_type="text/html", body=(ROOT / "site/index.html").read_text())
        if url.endswith("/campaign.json"):
            return route.fulfill(content_type="application/json", body=(ROOT / "campaign.json").read_text())
        if "api.github.com" in url:
            return route.fulfill(content_type="application/json", body="[]")
        minute = int(datetime.now(timezone.utc).timestamp() // 60)
        if self.mode != "offline" and f"/ticks/{minute-1}/" in url:
            observed = datetime.fromtimestamp((minute-1)*60, timezone.utc)
            snapshot = dict(observed_at=observed.isoformat(), message="Live proof work",
                            readiness_passed=128, running_resolvers=128,
                            verified_integrated_roots=0, problems=[dict(id="fermat-p01", nodes=[
                                dict(id="fermat-p01/root", problem="fermat-p01", local_id="root",
                                     title="Theorem", requires=[], status="decomposing", prose_status="reviewed")])])
            if self.mode == "older":
                snapshot.update(observed_at="2026-01-01T00:00:00Z", running_resolvers=0, problems=[])
            return route.fulfill(content_type="application/json", body=json.dumps(snapshot))
        return route.fulfill(status=404, body="unavailable")

    def test_previous_minute_is_used_and_failures_preserve_progress(self):
        self.page.goto("https://status.test/index.html")
        self.page.wait_for_function("document.querySelector('#resolvers').textContent === '128'")
        self.assertIn("decomposing", self.page.locator("#dag").text_content())
        self.mode = "older"
        self.page.evaluate("window.testRefresh()")
        self.assertEqual(self.page.locator("#resolvers").inner_text(), "128")
        self.assertIn("decomposing", self.page.locator("#dag").text_content())
        self.mode = "offline"
        self.page.evaluate("window.testRefresh()")
        self.assertIn("refresh incomplete", self.page.locator("#notice").inner_text())
        self.assertIn("decomposing", self.page.locator("#dag").text_content())
        self.assertNotIn("https://status.test/status.json", self.requests)
        self.assertFalse(self.page.evaluate("document.documentElement.scrollWidth > innerWidth"))
        self.assertEqual(self.errors, [])

    def test_first_load_failure_does_not_invent_queued_jobs(self):
        self.mode = "offline"
        self.page.goto("https://status.test/index.html")
        self.page.wait_for_function("document.querySelector('#notice').textContent.includes('refresh incomplete')")
        self.page.set_viewport_size({"width": 420, "height": 844})
        self.assertEqual(self.page.locator("#dag a").count(), 0)
        self.assertEqual(self.page.locator("#resolvers").inner_text(), "—")
        self.assertEqual(self.errors, [])


if __name__ == "__main__":
    unittest.main()
