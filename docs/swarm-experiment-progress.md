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

## Follow-up checkpoint, 08:20 UTC — real proof jobs launched

- All ten executable project branches `experiments/fermat-p01` through `p10` are
  pushed. Source registrations are in the broker-local catalogue. All ten configs
  passed Humanize schema validation; `hmz check` reports zero errors (seven config
  description warnings). The runtime is staged under `fermat-swarm-runtime/flows/`.
- The 128-worker service now has the full runtime, pinned toolchain/packages,
  shared project mounts, and scoped Docker secrets. Bootstrap creates a real
  container account, copies authorized credentials into a container-local Ubuntu
  home, then drops to uid/gid 1000 before polling. Never publish those secrets.
- Two pilot attempts failed safely before model work because SSH requires a passwd
  entry for uid1000. Both receipts were terminal/released and the project disabled.
  The corrected bootstrap passed a real remote Git transport check on hoa0.
- **All ten root issues are now claimed and working on distinct nodes**:
  p01 hoa82, p02 hoa32, p03 hoa97, p04 hoa35, p05 hoa108, p06 hoa49,
  p07 hoa91, p08 hoa24, p09 hoa71, p10 hoa52. Real model responses are present
  in every job's logs. p04 reached natural-proof drafting; the others are planning.
  There are no accepted natural proofs or verified theorem solutions yet.
- All 128 Swarm tasks are Running with current heartbeat observations. The other
  118 workers poll independently. **Do not roll/restart this service with active
  claims.** Non-expiring claims must be reconciled against actual task/process state.
- Comparator self-test session14133 finished exit0: all ten positive/negative
  cases passed, including combined retained child interfaces. No longer live.
  Baseline `fermat-contract-build.service` PID2780465 remains live and advancing.
  The private catalogue still has `verifier_ready:false` until remaining checks
  and baseline validation complete; proof drafting may proceed but cannot pass
  the formal acceptance gate while this flag is false.
- Broker PID2856288 now includes the immutable revision verifier. Verification
  snapshots/evidence are stored under its private /var/tmp directory, outside
  worker-writable shared projects. Worker worktrees remain on shared storage even
  for long child node names, so the host verifier and later pollers can access them.
- Main campaign commit3dc6f4b includes a proof-aware live observer and six passing
  feed tests. Pages commit65bcbab is built. The page shows the real dynamic DAG,
  distinct prose/Lean/merge states and counts; 08:18 feed reported128 pollers,
  ten active issue jobs and zero accepted proofs. Producer cadence60s, UI120s.
- Workflow deployed commit79d862d, branch `workflow/swarm-issue-resolvers` in the
  campaign repository. Subsequent controller checks must be tested/pushed without
  interrupting the ten live proof jobs. Original benchmark contracts remain intact.

Next: complete baseline/compiler and sandbox checks; enable real verification,
monitor drafts/reviews and issue decompositions, then verify/merge every resulting
helper and all ten root PRs. Do not confuse worker deployment with experiment
completion. The current scheduler remains one active issue per problem; independent
child parallelism within a problem would require isolating shared DAG/integration
state, not simply deleting the project lock.

## Follow-up checkpoint, 08:27 UTC — tools and verification ready

- A stronger runtime check exposed a missing companion binary: the model could
  answer, but `/runtime/bin/codex-code-mode-host` was absent, preventing filesystem
  tools. Workers correctly refused to invent reference evidence. Copied the exact
  authorized standalone0.159.0 companion atomically into the shared read-only
  runtime; no active worker or claim was restarted. SHA256:
  `160c7ea08738447582821fbb2611ee016d6dd628853401bbc441767cb4e95ef8`.
  Also staged the installed static `rg` binary for local searches.
- Bootstrap smoke job `i1dhkr3ax0awwd4c6kaqcudbq` on hoa0 completed exit0. It asks
  the configured model to read a random local file whose value is not in the
  prompt. The exact answer matched, proving actual tool execution, not merely
  authentication. p04 logs independently confirm restored file reads and research
  into restriction/transfer for the four Tate-cohomology degree cases.
- All ten jobs reached natural-proof drafting; none has a passing prose review
  yet. Earlier unreviewed drafts retain their reported missing-tool gaps.
- The additional sandbox canary test passed: code inside the verification sandbox
  cannot read a private file outside the allowlisted roots. All55 worktree tests
  pass, including long Swarm paths staying on shared storage.
- The controller catalogue now sets `verifier_ready:true`. The ten-case comparator
  self-test, seven remote-service tests and sandbox canary are complete. The
  background whole-project baseline build is still live; it is no longer a global
  hold on individual candidate checking because every real verification independently
  compiles its frozen challenge and candidate and runs all acceptance checks.
  This does not mark any theorem or baseline build successful.
- Actual Chromium mobile check of the public site:128 pollers,10 active jobs,
  zero reviewed/verified roots, ten DAG links, no JavaScript errors, no overflow.
  Screenshot `/tmp/fermat-swarm-live-mobile.png`. Browser environment:
  `/tmp/math-lean-flow-status-browser/bin/python` with
  `LD_LIBRARY_PATH=/tmp/proof-status-libs.cEVZPT/extracted/usr/lib/x86_64-linux-gnu`.

## Follow-up checkpoint, 08:52 UTC — reviews and dashboard regression

- All128 resolver tasks remain Running; all10 issue jobs remain active. Roots
  p01,p03,p04,p05,p07 have accepted prose and are decomposing. No child handoff,
  verified Lean solution or solution PR is yet recorded. Other roots are revising.
- A dashboard regression explained the user's apparent return to "queued": it
  fetched only current/next minute ticks, then fell back to the old bundled setup
  snapshot when publication crossed a minute boundary. Main92c1166 and
  Pages39a1e16 now try recent ticks plus the live pointer, preserve the newest
  displayed observation, and show fetch failure instead of inventing queued jobs.
  Two real-browser regression tests and six proof-feed tests pass. Both branches
  pushed; Pages39a1e16 was building at08:52 (verify before claiming deployed).
- Citation-validation defect: p02 auditv3 approved the mathematics, but all paths
  were project-relative; the validator treated them only as snapshot-relative and
  restarted prose revision. A local fix accepts either spelling only after strict
  realpath containment inside the correct frozen snapshot.23 local/preflight tests
  pass. This change is NOT committed/deployed yet; do not restart live workers.
- URGENT publication defect: adopted root markers were appended, but ordinary
  issue discovery matches only the first line. Publication created duplicate roots:
  p04 #11/#12; p07 #13/#14; p01 #15/#16; p03 #17/#18; p05 #19/#20.
  Original roots#1–#10 remain open. Both passes of `_sync_issues` created records,
  so also investigate list read-after-write visibility. No duplicates reconciled
  yet. Fix identity reuse with tests; preserve original root numbers and do not
  close anything as proved. Live DAGs currently point at the later duplicates.
  A safe repair must not overwrite active DAG files or interrupt healthy jobs.
- Baselinebuild PID2780465 remains live with eight Lean children. Some frozen
  inputs retain `attribute [-simp]` names from removed proof imports; p04 worker
  flagged this during decomposition. A read-only stdin probe of
  `import Mathlib; attribute [-simp] Representation.TateResCor.cosetDecomp_apply`
  is still live as exec session70821; collect its real result, not a guessed error.
  Do not silently alter frozen benchmark contracts or import their target proofs.
- Workflow33689db is confirmed pushed. Broker/status services remain healthy.

## Follow-up checkpoint, 08:59 UTC — canonical issue repair

- Pages39a1e16 is built. A real public-browser check observed128 pollers,10
  activejobs,5 reviewed root proofs, correct stages, and no JavaScript errors.
- Repaired original root issues#1–#10: runtime identity is now first-line, and
  the full reviewed argument from duplicate publications is retained on the
  original issue where available. Issues#11–#20 were closed **not planned** as
  duplicates, not as accepted proofs; each retains its complete original proof
  text and links the canonical issue. No live DAG file/process was modified.
  Old live publishers should rediscover original identities on their next sync.
- Publisher now updates known issue URLs directly, verifies their marker/repo,
  caches successful identities against lagging list endpoints, preserves the
  stable problem marker, and promotes legacy appended markers during adoption.
  Reference-path spelling fix is included. Full178-test suite passes with one
  optional browser skip; website browser tests were separately run and passed.
- Existing root author/reviewer logs now independently confirm actual compile
  failures from leftover `attribute [-simp]` references in benchmark scaffolds
  p01,p04,p05,p07. Workers retained frozen files and checked proposed child types
  against the exact imports instead; that does NOT pass the literal Submission
  import gate. This packaging defect must be resolved without changing theorem
  statements/assumptions or importing upstream target proofs. No normalization
  has been implemented/authorized as acceptance evidence yet.

## Follow-up checkpoint, 09:05 UTC — first autonomous child claimed

- Workflow2e30c71 pushed and staged by fast-forward in the shared runtime. Existing
  model/controller processes retain their imported code; new issue invocations use
  the fixed publisher/citation validator. No worker service restart performed.
- p04's original owner on hoa35 completed the root decomposition and released its
  claim. Issues#21 (Tate index annihilation) and#22 (prime-avoiding annihilators)
  were published with exact types and reviewed natural-language arguments.
  A different poller on **hoa43**, actual task `o5ckrgt1sathaf13z2pxgbz8b` verified
  Running, independently claimed#22. Its attempt is
  `89ca235862414f08a959e07f39579754`; the log contains a real author no-split proposal
  and an active independent reviewer. No parent notification/dispatch was used.
  Root4 is waiting-children; both dependency edges appear in the live feed.
- p08 also passed prose review and is decomposing. Other original jobs remain live.
  No formal acceptance or solution PR yet. Duplicate roots#11–#20 remain explicitly
  closed as not planned, never counted as proved.
- p02's old in-memory validator rejected another otherwise passing review because
  its citations were project-relative. A compatibility symlink was added only at
  the reference bundle root (not either Git snapshot): bundle/.humanize points to
  that project's .humanize. The old strict-realpath check now resolves20 cited
  paths into the correct frozen bundle. Both project/mathlib snapshot Git trees
  remain clean. No proof/audit status was changed and no job was restarted.
- An asynchronous user question requests permission to omit only stale
  `attribute [-simp]` directives in derived build files, preserving original
  benchmark files and every logical contract/gate. **No answer yet; no such
  normalization has been made.** Continue unaffected proof jobs meanwhile.
- Manager memory/I/O pressure is high (not solely this experiment). Baseline
  PID2780465 and probe session70821 / lean PID2949737 remain live; do not restart
  them merely for elapsed time. Preserve unrelated workloads.

## Follow-up checkpoint, 09:17 UTC — first Lean candidate at real comparator

- First child#22 reached `rlcr-lean` on hoa43. Its isolated worker worktree is
  `.swarm-worktrees/79e26a5fbde03f2e3c2f/fermat-p04`; RLCR receipt records container
  `396e3b581ef9`, PID731, start_ticks60395481 and round
  `.humanize/rlcr/2026-10-07_09-07-35`. Actual Swarm task remains Running.
- Candidate **3e7de243c3b4f85adaaa4b648f1c938fdc2ab6fb** appends a19-line proof of
  `Submission.p04_eq_zero_of_prime_avoiding_annihilators`, retaining the inherited
  parent source byte-for-byte. Worker logs report isolated Lean compilation with
  warnings-as-errors and only standard axioms. This is NOT comparator acceptance.
- The real private verifier now has two running requests (actual PIDs checked):
  `2702e791219d48f4a4f4d867d5bbc8c0`, PID3008683, the#22 candidate above;
  `5fdcbbd61fac4022ab7ab2b275855246`, PID3007503, a p05 root/context probe at
  2fdd42759f4ab17640ac773289b521dd69d4b26e. Inspect SQLite `verifications` and its
  private logs for completion; do not restart them on observation timeouts.
- p01 published three children (#23–#25); one is independently claimed. p09
  passed prose review. p03 was sent back to natural proof because decomposition
  review exposed real unproved torsion/uniformization obligations, not just the
  import packaging error. Do not freeze that rejected argument as accepted.
- Campaign75a6368 pushed and status observer restarted (only the publisher,
  not proof workers). Seven feed tests pass. Current prose count now excludes
  roots in natural-proof/natural-review even if an old passing artifact remains;
  dashboard labels them revising/under review instead of treating historical
  approval as current acceptance. Earlier counts of7 included p03's old record.
- No user response yet to the build-directive repair question. No directives
  removed. The pure diagnostic Lean `autoImplicit false`/undeclared universe
  probe is live as session97093; collect before deciding whether child challenge
  generation also needs explicit universe declarations. Original full-Mathlib
  probe session70821 remains live. Manager memory/I/O contention is confirmed;
  large unrelated Codex/Lean/search processes are NOT this experiment and must
  not be killed or modified.
