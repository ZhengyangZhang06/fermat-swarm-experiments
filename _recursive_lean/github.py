"""Bounded GitHub publication through the user's authenticated GitHub CLI."""

from __future__ import annotations

import hashlib
import json
import re
import subprocess
from pathlib import Path
from typing import Any
from urllib.parse import urlsplit

from .store import atomic_text


class PublicationError(RuntimeError):
    """An infrastructure failure; it must not trigger another mathematical proof."""

    def __init__(self, message: str, *, status_code: int | None = None) -> None:
        super().__init__(message)
        self.status_code = status_code


def repository_from_url(url: str) -> str:
    """Accept credential-free GitHub HTTPS and Git SSH remote coordinates."""
    match = re.fullmatch(r"git@github\.com:([^\s]+)", url)
    if match:
        path = match.group(1)
    else:
        parsed = urlsplit(url)
        if (
            parsed.hostname != "github.com"
            or parsed.password
            or parsed.query
            or parsed.fragment
            or parsed.port
            or not (
                (parsed.scheme == "https" and parsed.username is None)
                or (parsed.scheme == "ssh" and parsed.username == "git")
            )
        ):
            raise PublicationError(
                "publication requires a credential-free github.com remote"
            )
        path = parsed.path.lstrip("/")
    path = path.removesuffix(".git")
    if not re.fullmatch(r"[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+", path):
        raise PublicationError("GitHub remote must identify one owner/repository")
    return path


class GitHubClient:
    """Find by durable marker before create, including after an uncertain response."""

    def __init__(self, repository: str, cwd: Path, timeout: float) -> None:
        if not re.fullmatch(r"[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+", repository):
            raise PublicationError("expected a GitHub owner/repository")
        self.repository = repository
        self.cwd = cwd
        self.timeout = timeout
        self._issue_urls: dict[str, str] = {}
        self._comment_ids: dict[str, int] = {}

    def request(
        self,
        method: str,
        resource: str,
        payload: dict[str, Any] | None = None,
        *,
        paginate: bool = False,
    ) -> Any:
        command = [
            "gh",
            "api",
            "--hostname",
            "github.com",
            "--method",
            method,
            f"repos/{self.repository}/{resource}".rstrip("/"),
        ]
        if paginate:
            command += ["--paginate", "--slurp"]
        if payload is not None:
            command += ["--input", "-"]
        try:
            result = subprocess.run(
                command,
                cwd=self.cwd,
                input=json.dumps(payload) if payload is not None else None,
                capture_output=True,
                text=True,
                timeout=self.timeout,
                check=False,
            )
        except (OSError, subprocess.TimeoutExpired) as error:
            raise PublicationError(
                "GitHub CLI unavailable or timed out; restore access and resume this run"
            ) from error
        if result.returncode:
            status = re.search(r"\(HTTP (\d{3})\)", result.stderr or "")
            # Do not echo transport output: it may contain credential-helper diagnostics.
            raise PublicationError(
                f"GitHub {method} {resource.split('?')[0]} failed; "
                "check gh authentication/repository access, then resume",
                status_code=int(status.group(1)) if status else None,
            )
        try:
            value = json.loads(result.stdout)
            return [item for page in value for item in page] if paginate else value
        except (ValueError, TypeError) as error:
            raise PublicationError(
                "GitHub returned an invalid JSON response"
            ) from error

    @staticmethod
    def _marked(items: list[dict[str, Any]], marker: str) -> dict[str, Any] | None:
        matches = [
            one for one in items if (one.get("body") or "").splitlines()[:1] == [marker]
        ]
        if len(matches) > 1:
            raise PublicationError(
                "multiple GitHub records have the same theorem identity"
            )
        return matches[0] if matches else None

    def issue(
        self, marker: str, title: str, body: str, *, known_url: str = ""
    ) -> dict[str, Any]:
        if len((marker + "\n\n" + body).encode("utf-8")) > 65536:
            return self._multipart_issue(
                marker, title, body, known_url=known_url
            )
        known_url = known_url or self._issue_urls.get(marker, "")
        if known_url:
            match = re.fullmatch(
                rf"https://github\.com/{re.escape(self.repository)}/issues/([1-9][0-9]*)",
                known_url,
            )
            if not match:
                raise PublicationError("known theorem issue belongs to a different repository")
            found = self.request("GET", f"issues/{match.group(1)}")
            if "pull_request" in found or (found.get("body") or "").splitlines()[:1] != [marker]:
                raise PublicationError("known theorem issue has a different identity")
        else:
            items = self.request("GET", "issues?state=all&per_page=100", paginate=True)
            found = self._marked(
                [one for one in items if "pull_request" not in one], marker
            )
        payload = {"title": title, "body": marker + "\n\n" + body}
        if found:
            if found["title"] == title and found.get("body") == payload["body"]:
                result = found
            else:
                result = self.request("PATCH", f"issues/{found['number']}", payload)
        else:
            # A failed/uncertain POST escapes. Resume reconciles before retrying.
            result = self.request("POST", "issues", payload)
        # List endpoints can lag a successful mutation. Never create again merely
        # because the next list omits an identity already returned by GitHub.
        self._issue_urls[marker] = result["html_url"]
        return result

    def _multipart_issue(
        self, marker: str, title: str, body: str, *, known_url: str
    ) -> dict[str, Any]:
        """Publish immutable parts, then atomically select the complete version.

        Publication remains under the runtime's existing publication lock. A
        failed create escapes: a retry lists every comment and reconciles its
        durable identity before creating anything. No mathematical payload is
        shortened or rewritten, and no partial version is advertised complete.
        """
        if len(marker.encode("utf-8")) > 1024 or "\n" in marker:
            raise PublicationError("theorem publication marker is not a bounded single line")
        encoded = body.encode("utf-8")
        digest = hashlib.sha256(encoded).hexdigest()
        identity = hashlib.sha256(marker.encode("utf-8")).hexdigest()
        parts = []
        offset = 0
        while offset < len(encoded):
            end = min(offset + 60000, len(encoded))
            # Never split a Unicode code point; prefer a nearby paragraph/line
            # boundary without stripping any whitespace from the exact record.
            while end < len(encoded) and encoded[end] & 0xC0 == 0x80:
                end -= 1
            newline = encoded.rfind(b"\n", offset + (end - offset) // 2, end)
            if end < len(encoded) and newline >= 0:
                end = newline + 1
            parts.append(encoded[offset:end].decode("utf-8"))
            offset = end

        def manifest(urls: list[str]) -> str:
            return (
                "## Complete theorem record\n\n"
                "The exact Lean problem, natural-language proof, dependencies and "
                "proof status are preserved in the ordered continuation comments "
                "below. This publication status does not assert that the theorem "
                "is proved. Concatenate the text between the payload delimiters "
                "in part order to recover the original record exactly.\n\n"
                f"Current record SHA-256: `{digest}`\n\n"
                f"Record size: {len(encoded)} UTF-8 bytes; {len(parts)} parts.\n\n"
                + "\n".join(f"- [Part {i} of {len(parts)}]({url})" for i, url in enumerate(urls, 1))
                + "\n\nOnly these linked parts with the current digest constitute "
                "the current record. All other continuation comments are historical "
                "or incomplete publication attempts.\n"
            )

        # Fail before writing anything if even the index cannot fit. Use a
        # conservative URL bound, not guessed/truncated mathematical content.
        if len((marker + "\n\n" + manifest(["x" * 256] * len(parts))).encode("utf-8")) > 65536:
            raise PublicationError("complete theorem continuation index exceeds GitHub's body limit")
        known_url = known_url or self._issue_urls.get(marker, "")
        if known_url:
            match = re.fullmatch(
                rf"https://github\.com/{re.escape(self.repository)}/issues/([1-9][0-9]*)",
                known_url,
            )
            if not match:
                raise PublicationError("known theorem issue belongs to a different repository")
            found = self.request("GET", f"issues/{match.group(1)}")
            if "pull_request" in found or (found.get("body") or "").splitlines()[:1] != [marker]:
                raise PublicationError("known theorem issue has a different identity")
        else:
            found = self._marked(
                [one for one in self.request("GET", "issues?state=all&per_page=100", paginate=True)
                 if "pull_request" not in one], marker
            )
        if not found:
            found = self.request("POST", "issues", {
                "title": title,
                "body": marker + "\n\n## Theorem record publication incomplete\n\n"
                "The complete record is being published in continuation comments. "
                "No complete current record is selected yet; this is not proof acceptance.\n",
            })
        if (
            type(found.get("number")) is not int or found["number"] <= 0
            or found.get("html_url") != f"https://github.com/{self.repository}/issues/{found.get('number')}"
        ):
            raise PublicationError("theorem continuation issue has inconsistent coordinates")
        self._issue_urls[marker] = found["html_url"]
        comments = self.request("GET", f"issues/{found['number']}/comments?per_page=100", paginate=True)
        urls = []
        for index, part in enumerate(parts, 1):
            part_marker = f"<!-- theorem-record:{identity}:sha256:{digest}:part:{index} -->"
            content = (
                part_marker + f"\n\n## Theorem record continuation {index}/{len(parts)}\n\n"
                f"Record SHA-256: `{digest}`. This is a historical or pending part "
                "unless the issue body's current-record index explicitly links it "
                "with this digest. Publication is not proof acceptance.\n\n"
                "<!-- theorem-record-payload-start -->\n" + part
                + "\n<!-- theorem-record-payload-end -->"
            )
            intent_key = hashlib.sha256((self.repository + "\n" + part_marker).encode()).hexdigest()
            intent_path = self.cwd / ".humanize" / "publication-intents" / (intent_key + ".json")
            intent_identity = {
                "repository": self.repository,
                "issue_number": found["number"],
                "marker": part_marker,
                "content_sha256": hashlib.sha256(content.encode()).hexdigest(),
            }
            try:
                intent = json.loads(intent_path.read_text())
            except FileNotFoundError:
                intent = None
            except (OSError, ValueError) as error:
                raise PublicationError("theorem continuation intent is unreadable; reconcile before publication") from error
            if intent is not None and (
                not isinstance(intent, dict)
                or any(intent.get(key) != value for key, value in intent_identity.items())
                or intent.get("state") not in {"pending", "created"}
                or (intent["state"] == "created" and (
                    type(intent.get("comment_id")) is not int or intent["comment_id"] <= 0
                ))
            ):
                raise PublicationError("theorem continuation intent has a different identity")
            comment = self._marked(comments, part_marker)
            if not comment and intent and intent["state"] == "created":
                comment = self.request("GET", f"issues/comments/{intent['comment_id']}")
            if not comment and part_marker in self._comment_ids:
                comment = self.request("GET", f"issues/comments/{self._comment_ids[part_marker]}")
            if not comment:
                if intent:
                    raise PublicationError(
                        "theorem continuation create has an uncertain outcome; "
                        "wait for its marker to reconcile before resuming (not creating a duplicate)"
                    )
                atomic_text(intent_path, json.dumps({**intent_identity, "state": "pending"}))
                comment = self.request("POST", f"issues/{found['number']}/comments", {"body": content})
            if comment.get("body") != content:
                raise PublicationError("immutable theorem continuation was changed; reconcile before publication")
            if (
                type(comment.get("id")) is not int or comment["id"] <= 0
                or comment.get("html_url") != (
                    f"https://github.com/{self.repository}/issues/{found['number']}#issuecomment-{comment.get('id')}"
                )
            ):
                raise PublicationError("theorem continuation has a different issue identity")
            self._comment_ids[part_marker] = comment["id"]
            atomic_text(intent_path, json.dumps({**intent_identity, "state": "created", "comment_id": comment["id"]}))
            urls.append(comment["html_url"])
        # Existing complete records stay current until every replacement part
        # exists. If this PATCH has an uncertain result, the same manifest is
        # safely reconciled on resume; superseded parts remain auditable.
        return self.issue(marker, title, manifest(urls), known_url=found["html_url"])

    def find_pull_request(self, marker: str) -> dict[str, Any] | None:
        return self._marked(self.request("GET", "pulls?state=all&per_page=100", paginate=True), marker)

    def merge_verified(self, record: dict[str, Any], *, commit: str, base_commit: str) -> dict[str, Any]:
        """Normal GitHub merge with a head-SHA guard; never bypass protection."""
        current = self.request("GET", f"pulls/{record['number']}")
        if current["head"]["sha"] != commit or current["base"]["ref"] != record["base"]["ref"]:
            raise PublicationError("theorem PR changed after verification; refusing merge")
        if current.get("merged_at"):
            return current
        if current["state"] != "open" or current.get("draft") or current["base"]["sha"] != base_commit:
            raise PublicationError("theorem PR is draft, closed, or has an unverified base; refusing merge")
        result = self.request("PUT", f"pulls/{record['number']}/merge", {"sha": commit, "merge_method": "merge"})
        if not result.get("merged"):
            raise PublicationError("GitHub did not confirm the verified theorem merge")
        merged = self.request("GET", f"pulls/{record['number']}")
        if not merged.get("merged_at") or merged.get("merge_commit_sha") != result.get("sha"):
            raise PublicationError("theorem merge needs remote reconciliation")
        return merged

    def close_proved_issue(self, url: str, marker: str) -> dict[str, Any]:
        prefix = f"https://github.com/{self.repository}/issues/"
        if not url.startswith(prefix) or not url[len(prefix):].isdigit():
            raise PublicationError("invalid theorem issue identity")
        resource = f"issues/{url[len(prefix):]}"
        issue = self.request("GET", resource)
        if "pull_request" in issue or (issue.get("body") or "").splitlines()[:1] != [marker]:
            raise PublicationError("theorem issue identity changed; refusing closure")
        if issue.get("state") == "closed":
            return issue
        return self.request("PATCH", resource, {"state": "closed", "state_reason": "completed"})

    def pull_request(
        self,
        marker: str,
        title: str,
        body: str,
        *,
        head: str,
        base: str,
        commit: str,
    ) -> dict[str, Any]:
        items = self.request("GET", "pulls?state=all&per_page=100", paginate=True)
        found = self._marked(items, marker)
        payload = {"title": title, "body": marker + "\n\n" + body}
        if found:
            if (
                found["head"]["ref"] != head
                or found["base"]["ref"] != base
                or found["head"]["sha"] != commit
            ):
                raise PublicationError(
                    "existing theorem PR has different branch or commit coordinates"
                )
            if found["state"] != "open":
                if not found.get("merged_at"):
                    raise PublicationError(
                        "theorem PR was closed without merge; resolve it before resuming"
                    )
                # Generated descriptions may need a lifecycle-policy update after
                # explicit user authorization changes, without touching proof code.
                if found["title"] == title and found.get("body") == payload["body"]:
                    return found
                return self.request("PATCH", f"pulls/{found['number']}", payload)
            if found["title"] == title and found.get("body") == payload["body"]:
                return found
            return self.request("PATCH", f"pulls/{found['number']}", payload)
        return self.request("POST", "pulls", {**payload, "head": head, "base": base})
