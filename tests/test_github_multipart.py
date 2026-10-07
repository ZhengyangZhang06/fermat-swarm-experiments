from __future__ import annotations

import hashlib
import tempfile
import unittest
from pathlib import Path

from _recursive_lean.github import GitHubClient, PublicationError


class ThreadGitHub(GitHubClient):
    def __init__(self, cwd):
        super().__init__("example/proofs", cwd, 30)
        self.issues = []
        self.comments = []
        self.writes = []
        self.lose = ""
        self.hide_comments = False

    def request(self, method, resource, payload=None, *, paginate=False):
        if method == "GET":
            if resource.startswith("issues?"):
                return [dict(one) for one in self.issues]
            if "/comments?" in resource:
                assert paginate
                return [] if self.hide_comments else [dict(one) for one in self.comments]
            if resource.startswith("issues/comments/"):
                return dict(next(one for one in self.comments if one["id"] == int(resource.split("/")[-1])))
            return dict(next(one for one in self.issues if one["number"] == int(resource.split("/")[-1])))
        self.writes.append((method, resource))
        assert len(payload.get("body", "").encode("utf-8")) <= 65536
        if method == "PATCH":
            record = self.issues[int(resource.split("/")[-1]) - 1]
            record.update(payload)
        elif resource.endswith("/comments"):
            number = int(resource.split("/")[1])
            record = {**payload, "id": len(self.comments) + 1}
            record["html_url"] = f"https://github.com/example/proofs/issues/{number}#issuecomment-{record['id']}"
            self.comments.append(record)
        else:
            record = {**payload, "number": len(self.issues) + 1, "state": "open"}
            record["html_url"] = f"https://github.com/example/proofs/issues/{record['number']}"
            self.issues.append(record)
        if self.lose == resource or self.lose == method:
            self.lose = ""
            raise PublicationError("accepted mutation; lost response")
        return dict(record)


class MultipartIssueTests(unittest.TestCase):
    marker = "<!-- stable theorem p09 -->"
    body = "## Exact Lean goal\n```lean\ntheorem sample : True := by sorry\n```\n\n" + ("∀ α, a proposed proof with a gap.\n\n" * 4000) + "\nTrailing spaces  \n"

    def api(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        return ThreadGitHub(Path(temporary.name))

    def publish(self, api, body=None):
        return api.issue(self.marker, "Theorem", self.body if body is None else body)

    def payload(self, comment):
        return comment["body"].split("<!-- theorem-record-payload-start -->\n", 1)[1].rsplit("\n<!-- theorem-record-payload-end -->", 1)[0]

    def test_exact_unicode_payload_and_idempotent_publication(self):
        api = self.api()
        issue = self.publish(api)
        self.assertEqual("".join(self.payload(c) for c in api.comments), self.body)
        self.assertIn(hashlib.sha256(self.body.encode()).hexdigest(), issue["body"])
        self.assertIn("does not assert that the theorem is proved", issue["body"])
        self.assertGreater(len(api.comments), 1)
        for c in api.comments:
            self.assertIn(c["html_url"], issue["body"])
        writes = len(api.writes)
        self.publish(api)
        self.assertEqual(len(api.writes), writes)

    def test_lost_issue_and_comment_creates_reconcile_after_restart(self):
        for resource in ("issues", "issues/1/comments", "PATCH"):
            with self.subTest(resource=resource):
                api = self.api()
                api.lose = resource
                with self.assertRaises(PublicationError):
                    self.publish(api)
                if resource != "PATCH":
                    self.assertIn("publication incomplete", api.issues[0]["body"])
                api._issue_urls.clear()
                api._comment_ids.clear()
                self.publish(api)
                self.assertEqual(len(api.issues), 1)
                self.assertEqual("".join(self.payload(c) for c in api.comments), self.body)

    def test_old_current_record_survives_interrupted_replacement(self):
        api = self.api()
        old = self.publish(api)
        old_count = len(api.comments)
        api.lose = "issues/1/comments"
        with self.assertRaises(PublicationError):
            self.publish(api, self.body + "New exact proof status: unreviewed.\n")
        self.assertEqual(api.issues[0]["body"], old["body"])
        new = self.publish(api, self.body + "New exact proof status: unreviewed.\n")
        for c in api.comments[:old_count]:
            self.assertNotIn(c["html_url"] + ")", new["body"])
            self.assertIn("historical or pending", c["body"])
        self.assertEqual("".join(self.payload(c) for c in api.comments[old_count:]), self.body + "New exact proof status: unreviewed.\n")

    def test_changed_or_duplicate_part_fails_closed(self):
        for duplicate in (False, True):
            with self.subTest(duplicate=duplicate):
                api = self.api()
                self.publish(api)
                if duplicate:
                    api.comments.append(dict(api.comments[0], id=99))
                else:
                    api.comments[0]["body"] += "altered"
                writes = len(api.writes)
                with self.assertRaises(PublicationError):
                    self.publish(api)
                self.assertEqual(len(api.writes), writes)

    def test_successful_comments_survive_stale_listing(self):
        api = self.api()
        self.publish(api)
        writes = len(api.writes)
        api.hide_comments = True
        self.publish(api)
        self.assertEqual(len(api.writes), writes)

    def test_small_replacement_does_not_retain_current_manifest(self):
        api = self.api()
        self.publish(api)
        comments = [dict(c) for c in api.comments]
        result = self.publish(api, "Exact smaller record.")
        self.assertEqual(result["body"], self.marker + "\n\nExact smaller record.")
        self.assertEqual(comments, api.comments)

    def test_wrong_known_url_and_tampered_issue_identity_fail_closed(self):
        api = self.api()
        issue = self.publish(api)
        for url in ("https://github.com/other/repo/issues/1",):
            with self.assertRaises(PublicationError):
                api.issue(self.marker, "Theorem", self.body, known_url=url)
        api.issues[0]["body"] = "<!-- different -->"
        with self.assertRaises(PublicationError):
            api.issue(self.marker, "Theorem", self.body, known_url=issue["html_url"])

    def test_lost_create_and_stale_listing_fail_closed_across_restart(self):
        api = self.api()
        api.lose = "issues/1/comments"
        with self.assertRaises(PublicationError):
            self.publish(api)
        restarted = ThreadGitHub(api.cwd)
        restarted.issues, restarted.comments = api.issues, api.comments
        restarted.hide_comments = True
        with self.assertRaisesRegex(PublicationError, "uncertain outcome"):
            self.publish(restarted)
        self.assertEqual(restarted.writes, [])
        self.assertEqual(len(restarted.comments), 1)
        restarted.hide_comments = False
        self.publish(restarted)
        self.assertEqual("".join(self.payload(c) for c in restarted.comments), self.body)

    def test_success_receipt_recovers_stale_comments_after_restart(self):
        api = self.api()
        self.publish(api)
        restarted = ThreadGitHub(api.cwd)
        restarted.issues, restarted.comments = api.issues, api.comments
        restarted.hide_comments = True
        self.publish(restarted)
        self.assertEqual(restarted.writes, [])

    def test_changed_create_response_cannot_select_current_record(self):
        for change in ("body", "id"):
            with self.subTest(change=change):
                api = self.api()
                original = api.request
                def altered(method, resource, payload=None, *, paginate=False):
                    result = original(method, resource, payload, paginate=paginate)
                    if method == "POST" and resource.endswith("/comments"):
                        result[change] = "truncated" if change == "body" else 999
                    return result
                api.request = altered
                with self.assertRaises(PublicationError):
                    self.publish(api)
                self.assertIn("publication incomplete", api.issues[0]["body"])


if __name__ == "__main__":
    unittest.main()
