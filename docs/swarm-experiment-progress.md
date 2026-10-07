# Fermat Swarm campaign — implementation checkpoint

This document records observed state, not completion or proof acceptance.

## Scope

Finish all ten `Fermat/manifest.json` problems in
`humanfia/lean-test-problems` at
`d8c69c0aae9dadbb9d0b4817ffc99ea07c2f7e99`, using the new issue/PR workflow
under ZhengyangZhang06. The problem source pins
`anthropics/fermats-last-theorem` at
`6e837e75355538c7f80bab5b956861e86c4eacc2` and Lean 4.33.1.

The requested deployment is 128 autonomous issue resolvers, one on each
`hoa0`–`hoa127`, not 128 concurrent copies of every problem. Maintain per-theorem
and per-subtheorem issues, Lean contracts and prose, verified solution PRs,
authorized merge/closure, and a live website with a dependency DAG.

## Verified infrastructure

- All 128 target nodes are Ready/Active; three other management nodes are drained.
- `sudo -n docker` is available. The unprivileged Docker socket is inaccessible.
- Shared workspace storage is CephFS.
- Readiness service `fermat-cluster-preflight-20261007`, ID
  `sd9l2bqcj4ua5ga89wmzyofsn`, ran as a global-job with restart disabled.
- All 128 tasks completed successfully and returned 128 distinct node reports.
  Each reported all ten source contracts present and Lean 4.33.1 executable.
- Manifest SHA256:
  `49a5cc0ae31784c0c4a6809085814b59443ccb8919027532faed6ee2b6ee69af`.
- Probe mounts were read-only: its script, the benchmark directory, and the
  toolchain. No credentials or Docker socket were mounted. No model was started.
- The base `python:3.12-bookworm` image has Python and Git, but no Node/Codex.
  The host Codex is a standalone executable, so Node is not itself required.
- On 2026-10-07 the user confirmed use of `/home/ubuntu/.codex`; the prior
  missing `/home/zhengyang/.codex` path is no longer a blocker.

## Implementation direction (not deployed yet)

Retain the existing proof engine and gates. Add a one-issue invocation that yields
after resolving an eligible node or publishing its children. Long-lived node
workers independently poll the GitHub-backed issue list and request ownership.
They must not receive start notifications from parent proof workers.

Use one durable transactional ownership authority. Serialize per-problem runtime
mutations initially, so separate processes cannot overwrite the in-memory DAG
store or race integrations. Different problems remain concurrent. All 128
pollers may be running while at most ten problems are doing proof work at once;
idle polling is not model work and must be reported distinctly.

Never expire a claim solely on elapsed time. An uncertain owner stays reserved
until its actual Swarm task/process is reconciled. Receipt identities must include
the node/task identity, not bare PIDs, because PIDs overlap across machines.
Only the authoritative publisher may merge/close after the existing proof gates.

The current verifier requires a user systemd service plus Landlock. Do not bypass
these protections inside containers. Provide a controller-owned verification
service or equivalent tested isolation, then keep candidate verification requests
bound to immutable Git revisions and frozen contracts. A remote report of success
alone is not acceptance evidence.

## Remaining deliverables

- Durable distributed claims, one-issue runtime, restart reconciliation, tests.
- Worker runtime packaging, scoped authentication, and real model smoke test.
- Campaign repository/branches, all ten root contracts/issues and configs.
- Project-specific comparator adaptation and negative/combined-interface tests.
- 128 actual resolver services, with observed issue claims and proof processes.
- Live campaign/DAG website reporting queued, working, blocked, verified, merged.
- Ten verified root solutions and every introduced helper's issue/PR, followed by
  actual authorized integration and issue closure. No theorem is yet claimed proved.

## Follow-up checkpoint, 07:12 UTC

- Created `ZhengyangZhang06/fermat-swarm-experiments` and pushed frozen contract
  commit `cc45347`. All ten root issues (#1–#10) now exist. The idempotent publisher
  was rerun and reused those records, without creating duplicates.
- Added a durable SQLite claim ledger for a single authoritative broker, requiring
  broker-local storage (not CephFS). Eight tests pass, including 128 competing
  connections, restart/lost-response idempotency, project/issue/owner exclusivity,
  stale-token rejection, and no takeover based on elapsed time. This is a unit
  test of the claim component, not an end-to-end deployed broker.
- The campaign's setup dashboard source shows ten frozen root nodes and no invented
  dependency edges; GitHub issue states refresh independently of proof acceptance.
  Its observation explicitly reports zero running resolvers and zero verified roots.

## Follow-up checkpoint, 07:17 UTC

- Public dashboard is deployed at
  https://zhengyangzhang06.github.io/fermat-swarm-experiments/ . GitHub Pages build
  `dc9add28cbcacf4b37af657d1d008d23a1e7892b` is built; HTTP returns 200.
  Real Chromium inspection found ten SVG theorem links, no JavaScript errors,
  zero running resolvers displayed, explicit non-black fills, and no horizontal
  overflow at 390px. Screenshot: `/tmp/fermat-swarm-setup-mobile.png`.
- Campaign main: `4ff5278`; Pages: `dc9add2`. Root issues remain #1–#10.
- Added `github_poll_once`, `github_selected_issue`, `github_root_issue_number`.
  Single-step mode requires poll mode, one local worker, and the issue that the
  external worker itself selected. It does not spawn a local pool and waits for
  integrations before returning. Its caller MUST retain the broker's exclusive
  project claim for the complete invocation; no broker/client is deployed yet.
- The existing root issue is adopted only with its stable problem marker and
  exact contract. A closed issue, a PR, wrong marker or changed contract is rejected.
- RLCR receipts now record execution host; an unfinished receipt on another host
  fails closed before looking up its PID. Do not mistake cross-node PID collisions
  for the original process. Terminal cross-host receipts remain eligible for the
  normal fresh comparator/review gates.
- Existing-plus-claim suite: 148 tests passed, one optional browser test skipped.
  Four additional issue/adoption tests then passed (18 issue-worker tests total).
  The public browser check above was run separately and passed.

Next: implement the authenticated durable broker/client and immutable comparator
request service, package the standalone Codex runtime using Docker secrets, then
freeze ten executable projects and enable one real worker smoke test before the
128-node resolver service. Root issue numbers must be reused, not recreated.

## Follow-up checkpoint, 08:03 UTC

- The user reconfirmed **Use Ubuntu** after a fresh workspace instruction again
  named the absent zhengyang home. `/home/ubuntu/.codex` is authorized.
- The TLS broker is deployed with broker-local durable ownership. Global service
  `fermat-issue-resolvers-20261007` has 128 live node workers independently polling;
  no theorem job has been enabled, claimed, or proved yet. The earlier pilot is
  scaled to zero. No timestamp-based ownership transfer is implemented.
- The real model runtime smoke job completed with the configured gpt-6-astra
  and the authorized authentication. It used no tools/search and proved no theorem.
- The public site uses minute-addressed snapshots from `status-live`; its observer
  checks both current Swarm task IDs and fresh heartbeats. It still requires the
  full proof/DAG feed before any job is enabled.
- Added immutable remote verification requests, pending-verification release
  protection, and automatic discovery of published dependency-ready child issues.
  Seven verifier-service tests and thirteen broker tests pass. Full workflow suite
  also returned exit zero with one optional browser skip before the last two DAG tests.
- The real comparator self-test is still live (PID 2801298, exec session 14133).
  It has accepted the valid cases and rejected changed type, sorryAx and a new
  axiom so far. Do not equate that partial result with full verifier readiness.
- Baseline commit `647767b` stages the exact 98-module import closure, manifest and
  source hashes; all ten frozen Fermat contracts are unchanged. Its `lake build
  Fermat` remains live under `fermat-contract-build.service` (PID 2780465).
- Ten isolated projects are being prepared/pushed to `experiments/fermat-pNN` in
  the campaign repository. Their Submission.lean starts as the exact unsolved
  contract; main retains the benchmark originals. Each target branch receives
  that problem's verified root solution; the campaign index must link integration
  evidence. These branches are setup, not solutions or accepted proof PRs.

Next: finish the live build/self-test, stage the worker runtime and secrets, validate
the ten configs without model calls, update the live proof-aware status publisher,
then enable real proof jobs and observe actual ownership/model processes. All ten
root proofs and every newly introduced helper remain outstanding.
