"""Repair adopted root identities without changing live DAGs or proof acceptance.

Default is read-only. --apply promotes the original campaign issue and closes
duplicate publications as not planned, retaining their complete proof bodies.
"""
import argparse
import json
import re
import subprocess
from pathlib import Path


MARKER = re.compile(r"^<!-- math-lean-flow:[a-f0-9]{64} -->$", re.M)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("campaign", type=Path)
    parser.add_argument("--gh", default="gh")
    parser.add_argument("--apply", action="store_true")
    args = parser.parse_args()
    campaign = json.loads(args.campaign.read_text())
    repo = campaign["repository"]

    def api(method, resource, payload=None, paginate=False):
        cmd = [args.gh, "api", "--method", method, f"repos/{repo}/{resource}"]
        if payload is not None:
            cmd += ["--input", "-"]
        if paginate:
            cmd += ["--paginate", "--slurp"]
        result = subprocess.run(cmd, input=json.dumps(payload) if payload is not None else None,
                                check=True, capture_output=True, text=True, timeout=120)
        value = json.loads(result.stdout)
        return [item for page in value for item in page] if paginate else value

    all_issues = api("GET", "issues?state=all&per_page=100", paginate=True)
    plans = []
    aliases = {}
    for problem in campaign["problems"]:
        number = problem["issue_number"]
        original = api("GET", f"issues/{number}")
        body = original.get("body") or ""
        stable = f"<!-- theorem-id: {problem['id']}/root -->"
        contract = (args.campaign.parent / problem["contract"]).read_text().strip()
        # Legacy live publishers may already have replaced the campaign body
        # without retaining its stable marker. The manifest's exact issue number,
        # complete contract and explicit root/theorem identity still bind it.
        root_identity = stable in body or (
            "Node: `root`" in body and f"## Theorem `{problem['theorem']}`" in body
        )
        if not root_identity or contract not in body or original["state"] != "open" or "pull_request" in original:
            raise RuntimeError(f"Original issue #{number} does not match its open frozen contract")
        markers = set(MARKER.findall(body))
        if len(markers) != 1:
            raise RuntimeError(f"Original issue #{number} has ambiguous runtime identity")
        marker = markers.pop()
        duplicates = [i for i in all_issues if i["number"] != number and "pull_request" not in i
                      and (i.get("body") or "").splitlines()[:1] == [marker]]
        for duplicate in duplicates:
            if contract not in duplicate["body"] or "Node: `root`" not in duplicate["body"]:
                raise RuntimeError(f"Duplicate #{duplicate['number']} has a different contract")
            aliases[duplicate["html_url"]] = original["html_url"]
        plans.append((problem, original, marker, stable, duplicates))
        print(problem["id"], "canonical", number, "duplicates", [d["number"] for d in duplicates], flush=True)

    if not args.apply:
        return
    # Promote canonical identities before retiring aliases. Intermediate ambiguity
    # fails closed in old publishers, rather than authorizing another creation.
    for problem, original, marker, stable, duplicates in plans:
        current = api("GET", f"issues/{original['number']}")
        if current["body"] != original["body"]:
            raise RuntimeError("Root was concurrently updated; inspect and rerun reconciliation")
        selected = max(duplicates, key=lambda d: d["number"]) if duplicates else original
        body = MARKER.sub("", selected["body"]).strip()
        if stable not in body:
            body = stable + "\n\n" + body
        for alias, canonical in aliases.items():
            body = re.sub(re.escape(alias) + r"(?![0-9])", canonical, body)
        api("PATCH", f"issues/{original['number']}", {"body": marker + "\n\n" + body})
    for problem, original, marker, stable, duplicates in plans:
        for duplicate in duplicates:
            current = api("GET", f"issues/{duplicate['number']}")
            if current["body"] != duplicate["body"]:
                raise RuntimeError("Duplicate was concurrently updated; inspect and rerun")
            explanation = (f"Duplicate publication of {original['html_url']}. Closed as a duplicate, "
                           "NOT as a proved theorem. The original proof text is retained below. "
                           "Follow the canonical issue for current work and verification.\n\n")
            api("PATCH", f"issues/{duplicate['number']}", {
                "title": f"[Duplicate of #{original['number']}] {problem['theorem']}"[:240],
                "body": explanation + MARKER.sub("", current["body"]).strip(),
                "state": "closed", "state_reason": "not_planned",
            })
            print("Retired duplicate", duplicate["number"], "canonical", original["number"], flush=True)


if __name__ == "__main__":
    main()
