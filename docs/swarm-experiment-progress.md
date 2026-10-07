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

- At09:20 the undeclared-universe probe97093 finished with the expected compiler
  error `unknown universe level u`. Added child-challenge construction that
  carries only the frozen source's explicit universe declarations across the
  Submission import boundary. This adds no hypotheses and changes no simp
  directives. Ten focused challenge/remote-verifier tests pass. The matching
  positive Lean syntax probe (with `universe u`) remains live in session23527.
  **Do not stage this verifier-file change while existing checks are running**:
  active verifications pin the checker file digest. Local source differs from
  staged runtime2e30c71 intentionally until those requests finish.
- At09:18 the live feed showed8 current reviewed root proofs,10 active jobs,
  and128 running pollers. p01 child#24 owner is hoa123, Swarm task
  `z51i7ikksog42ron5peo4lysu`. Both verifier requests had reached their real
  sandboxed `lake --no-cache build Challenge` subprocesses; they are not stalled
  in a broker queue. All proof acceptance/merge counts remain zero.

## Follow-up checkpoint, 09:26 UTC — comparator resource contention

- Original baseline `fermat-contract-build.service` was deliberately stopped at
  09:24, after confirming it was this campaign's `lake build Fermat`. Its frozen
  unsolved scaffolds are already known to have stale-attribute errors, and every
  real candidate independently builds its own challenge. Stopping the redundant
  baseline released about4GiB; retained build outputs and logs remain available.
  `inactive`, MainPID0, Resultsuccess means an orderly operator stop, NOT a
  successful baseline build. Do not silently restart this redundant job.
- Proof workers and both actual comparator jobs were left running. At09:26
  request2702… was compiling Def_GroupCohomology_TateCohomology with Lean
  PID3022273; request5fdc… was compiling Def_HopfAlgebra_HopfKer with PID3022279.
  Parent verifier PIDs3008683/3007503 remain live. Manager memory/I/O contention
  persists from unrelated jobs, which remain untouched.
- Positive universe syntax probe session23527 completed exit0 (only an unused
  variable warning); negative probe97093 failed with unknown universe level as
  expected. The corresponding source fix0e31559 is pushed but intentionally NOT
  staged over the active checker file. Runtime is still2e30c71.
- At09:26 the current feed reported9 reviewed root prose proofs,10 active issue
  jobs,128 pollers, and0 formally verified/integrated roots. Build-directive
  permission remains unanswered; original and derived directives remain intact.

## Follow-up checkpoint, 09:43 UTC — worker activity versus prepared DAG state

- Stopped only the redundant standalone Mathlib import diagnostic PID2949737
  after confirming its exact command/parent/cwd and the same scaffold error in
  independent worker evidence. Session70821 is terminal exit143; it did NOT pass.
  The actual comparator PIDs3007503/3008683 were left running and remained live.
- p02 published child issues and a new poller on hoa67 claimed#26 (primitive
  existence), task `gdxb5z9up8cca2etiic34ampz` confirmed Running. p01's worker
  published further descendants, released#24, and hoa6 independently claimed#23
  (finite-dimensionality), task `vl9ziscv6pzenltsyja6sbotv` confirmed Running.
- Campaign0449e32 and Pages30a0121 pushed; Pages reports built. Observer restarted
  without restarting proof jobs. Nodes now expose only the observed worker name
  and an executing boolean, derived from Running Swarm tasks and fresh working
  heartbeats. Prepared nodes no longer automatically look like active workers.
  Root links use canonical original campaign issue IDs, not repaired duplicates.
  Nine feed tests and two real-browser regression tests pass.
- Current09:43 feed:26 theorem nodes,10 observed executing nodes,128 pollers,
  5 current reviewed root prose proofs,0 verified/integrated roots. Root review
  counts can legitimately fall when later decomposition audits require revision.
  Both private verification requests remain running, not successful or terminal.
- Local benchmark inspection found no supplied directive-repair procedure; the
  manifest calls these statement extracts requiring pinned source dependencies.
  User permission for the proposed narrow build repair remains unanswered.

## Follow-up checkpoint, 09:54 UTC — repair proposal prepared but disabled

- Added pure `_recursive_lean/frozen_build.py` and five regression tests. It
  validates the entire input against a controller-supplied SHA256, defaults to
  returning unchanged source, and optionally prepares an in-memory copy omitting
  only standalone header `attribute [-simp]` commands. It records every omitted
  line and both source hashes. Comments, strings, declarations, assumptions,
  imports, options and proof text are preserved; there are **no runtime callers**.
- Fifteen focused frozen-build/frozen-challenge/remote-verifier tests pass. A
  read-only, in-memory preview across the ten campaign contracts found11 such
  directives in8 files; p02 andp08 have none. All other bytes were checked equal.
  No original, candidate, or derived build file was rewritten, and no repair was
  enabled. User permission is still pending. Do not describe this proposal as a
  tested full-project compile fix or as proof acceptance.
- At09:54 both existing verifier requests are still running. The unchanged
  checker file in staged runtime2e30c71 must remain intact until those checks
  finish. The campaign feed reports29 nodes,128 pollers,10 active jobs,5 currently
  reviewed root arguments and0 verified/integrated roots. No proof PR is accepted.
- Pages30a0121 was independently checked in a real public mobile browser at09:44:
  26 nodes,20 edges,10 active-node indicators,16 inactive indicators, no script
  errors and no document overflow. Screenshot `/tmp/fermat-swarm-observed-workers.png`.

## Follow-up checkpoint, 10:10 UTC — idle-node verifier feasibility established

- Previous goal turn was a verified wait: actual verifier/Lean PIDs were alive
  and public deployed feed was checked directly (no queued nodes). This turn
  adds executable diagnostic coverage; it does not count as a theorem solution.
- Added `scripts/swarm-verifier-selftest.py`, a fixed-fixture-only diagnostic
  with no broker/runtime callers and no candidate arguments. It imports the
  existing verifier, reuses all ten comparator fixtures unchanged, and replaces
  only the manager-specific systemd launcher with Landlock plus an inherited
  libseccomp filter denying all socket creation. Missing filter support fails
  closed. The diagnostic requires a non-root process. Four regression tests
  pass, including real socket-denial checks and refusal of candidate arguments.
- Launched credential-free service `fermat-verifier-probe-20261007` on idle
  hoa0, task `l9l350r9p7x4vuq9cyo4wjdra`. It has read-only root/tool/source
  mounts, UID1000, no capabilities, no host control sockets, no credentials,
  private tmpfs, CPU2/memory4GiB limits, and restart disabled. Swarm reports
  terminal **complete, ExitCode0** at10:09:35. All ten comparator cases passed
  their expected acceptance/rejection outcomes in103.49seconds. Private-file,
  AF_UNIX, AF_INET and socketpair denial probes passed. The expected renamed
  child export panic was correctly rejected, not accepted as a proof.
- This proves the pinned binaries and fixed-fixture sandbox can run on an idle
  node. It does NOT deploy remote acceptance, test a full Mathlib candidate, or
  solve ownership/evidence transport. Before production use, preserve immutable
  checker/input hashes, controller-owned challenge/evidence, exact registered
  candidate identity, dependency integrity, and durable job ownership/recovery.
  No Docker socket may be exposed to candidate code. Existing in-flight checks
  must finish under their original immutable checker, not be moved/restarted.
- Both actual verifier requests5fdc…/2702… remain running under original
  PIDs3007503/3008683; Lean PIDs3100384/3100390 have increasing CPU time. Manager
  memory and I/O pressure is independently confirmed. Runtime remains2e30c71;
  neither the universe fix nor disabled scaffold adapter was hot-deployed.
- At10:09 the observed feed has39 theorem nodes,128 pollers,10 active jobs,
  7 currently reviewed root arguments and0 verified/integrated roots. p01#41
  (coset norm bound) is now in real RLCR Lean formalization on hoa38; p04#22
  remains in real verification. `gh pr list --state all` returned no PRs.
  No scaffold directives were removed; the pending user decision is unchanged.

## Follow-up checkpoint, 10:28 UTC — immutable candidate packet diagnostic

- Split the source verifier into `prepare_verification()` and
  `verify_prepared()`, while preserving the default `verify()` entrypoint and
  all comparator, axiom-report, dependency and checker-identity checks. A
  preparation is explicitly `checking`, never proof acceptance. The packet
  binds both complete Lean source trees, candidate/base/frozen revisions,
  checked theorem names, dependency manifest/revisions and verifier SHA256 to
  a controller-retained digest. Links, source mutations, metadata substitution,
  and mismatched evidence are rejected. No contract normalization was added.
- Added a credential-free packet receiver, not connected to broker acceptance.
  It uses the already-tested Landlock/socket-denial launcher and only copies
  the validated source allowlist, not candidate build/config artifacts. All
  project packages and binaries are mounted read-only. Fifteen packet tests,
  two receiver guard tests, four launcher tests, eight frozen-build/challenge
  tests and seven remote-verification tests pass (36 focused tests total).
- Prepared an actual p01#41 candidate from registered request
  `6729df4ab16941009fb752bfccc3d3d8`, exact revision
  `b181a13231ad4b2da1be9936fbc21c719b41d12e`, in private directory
  `/mnt/data/zhengyang-workspace/fermat-verifier-packet.fWWQ5B`.
  `receipt.json` records its root and controller digest
  `764ee50c17abce618a30011ed31588a69c2a370c5b45f55befaa6413ab4a347c`.
  The scripts were copied into that private directory BEFORE preparation;
  source edits must not change the active diagnostic's immutable code copy.
- Diagnostic service `fermat-verifier-packet-p01-20261007`, task
  `p3lna6h8mgwz8o3go77evjnap`, is confirmed Running on hoa0 at10:28. It has no
  secrets or host control sockets, UID1000, no capabilities, read-only root,
  private tmpfs, CPU2/memory6GiB limits and restart disabled. It validated the
  packet and compiled twelve dependency build steps, then remained compiling.
  Output is retained under the private directory's `output/result`.
  **No terminal verification result yet.** Do not promote this diagnostic to
  an accepted broker result, close its issue, or restart it on polling timeout.
- The broker remains untouched: two original manager checks are running under
  PIDs3007503/3008683, with live Lean PIDs3100384/3100390. Request6729… remains
  queued. A fourth request980abb29cd8f4974be5179e6a0251ac4 is also queued for
  the SAME p01#41 theorem, at new revision15db3ef9f625c734560304ce3e21a07b20056041.
  The new commit changes only .gitignore, not Submission.lean. Nevertheless,
  evidence for the old exact revision must not be relabeled as the new one.
- At10:26 the public observation contains46 nodes,128 live pollers,10 active
  jobs,8 currently reviewed root arguments and0 verified/integrated roots.
  Production runtime stays2e30c71. No verifier hot-deploy, issue takeover,
  acceptance bypass, scaffold directive repair or worker restart occurred.
- Next: collect this exact diagnostic task's result, then implement and test
  durable queued-request dispatch/evidence correlation before enabling remote
  production acceptance. Preserve both existing running requests. Pending
  permission for derived-copy obsolete simp directives remains unanswered.

## Follow-up checkpoint, 11:10 UTC — first real remote request completed

- User requested one website graph per problem. Delivered campaign main5b9961b
  and Pagesac5ab90; Pages reports built. Ten independent graph panels have
  status/prose/Lean/integration summaries, P01–P10 jump links, local scrolling,
  unique arrow markers, explicit shared prerequisites and isolated error
  handling. Mobile views initially center the root and preserve scroll on
  refresh. Six real-browser tests and nine feed tests pass. Public mobile
  check at10:44 saw10 graphs,52 nodes, no graph/script errors or page overflow.
  Screenshot `/tmp/fermat-separate-graphs-public-mobile.png`.
- Added opt-in additional verification dispatch using the EXISTING local
  SQLite ledger. `recover_existing=False` preserves all running identities;
  an atomic queued-to-spawning transaction permits only one controller to
  launch a request. Released claims, missing requests, closed readiness and
  capacity exhaustion do not spawn. Reserved exit75 retains uncertain ownership.
  No issue ownership/worker scheduling behavior was changed.
- New controller adapter `scripts/swarm-verify-frozen-node.py` freezes a
  registered request, deploys read-only code/input with no secrets/control
  sockets, and retains the exact service/task/specification/packet/candidate
  identities in a private fsynced operation receipt. Remote exit alone is not
  success: the controller also checks immutable input/code and exact verified
  evidence. Observation failures retry the same handle, never recreate a job.
  `scripts/swarm-dispatch-verification.py` supports an explicit queued-request
  one-shot and a polling mode. **Only the one-shot mode has been deployed**;
  no fleet-wide verifier migration or continuously polling extra daemon yet.
- Immutable deployed bundle:
  `/mnt/data/zhengyang-workspace/fermat-verifier-dispatch.ZfocBD/deployment`.
  Do not change its files in place. Real end-to-end fixtures on hoa1 passed:
  valid request03b3ebdee98540eea1653c7742beff97, servicepqvwitzb5sxqdpp0lj9rpjvdc,
  taskq5927612qc3xscnooghkukn35 accepted with kernel replay/axiom evidence;
  changed-statement requestdf48089c5b9a4e679114304aa1ae70ba,
  servicexxb9h4cx24nr5pg8pmi7d88zf, taskwil085jyhgj883odmxlryh14o rejected.
  Fixtures/receipts/logs are under that bundle parent's `roundtrip/`; no campaign
  claims, issues or PRs were involved. Full source suite:224 tests pass with
  one optional Playwright test skipped (campaign browser tests ran separately).
- Original requests5fdc… (p05) and2702… (p04#22) are now terminal exit1, not
  still running. Actual errors reference absent header constants:
  `HopfAlgebra.HopfKerHopf.instHopfAlgebra`, `HopfAlgebra.HopfKerHopf.ι₂_comulK`,
  `Representation.TateResCor.cosetDecomp_apply`. Both failed before candidate
  acceptance. PIDs3007503/3008683/3100384/3100390 are gone.
- P01 old-revision request6729… and p02 old-revision requestd56e… were rejected
  by the manager for candidate HEAD mismatch. The worker had committed further
  changes and registered new exact revisions. The attempted p02 one-shot saw
  the old request already finished and made no state change. Its transient
  unit `fermat-swarm-verify-p02-20261007` exited/was collected. Never equate the
  unit's orderly exit with proof success.
- Real p06 child#52 request47d8781c81b34609bc160667cf21954f, candidate
  b3769c61fd862a46417a0c4f57c5a335c3a9e3ad, was atomically claimed and checked
  on hoa1 through the real broker ledger. Serviceu7ndex9cnxwzyqw6r2w1i2ha6,
  taskn8bzekhojlkeqo4buq3usnt58 completed **failed, exit1**; the controller
  receipt is `terminal`, not uncertain or verified. Its log and failure result
  are available to the owning issue worker normally. Missing header constants:
  `AlgebraicCurve.IsCurveOver.instNontrivialKaehler`,
  `AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply`,
  `AlgebraicCurve.SemilinearAut.coe_torsion_smul`.
  Receipt: `.../fermat-verifier-dispatch.ZfocBD/jobs/47d8781c81b34609bc160667cf21954f/operation.json`.
- P01 diagnostic taskp3lna6h8mgwz8o3go77evjnap also terminal failed1. It built
  the full pinned dependency closure, then rejected absent `[-instance]` and
  `[-simp]` targets in Submission.lean. Its old-revision diagnostic is NOT a
  broker acceptance result. Real newer p01 request980a… subsequently failed1.
- Last live manager request:739e7f62cd194f3888ebf43c1aab0ed0 for p02#45,
  candidate2ced4d3abd9f318f5490841e5e6ce28d9dfb7944, verifierPID3255572.
  Confirm it on the next turn. Production manager runtime stays2e30c71 while
  that checker runs; do not hot-deploy over its pinned checker file.
- User decision is still pending. Asked again via async input to omit only
  references to MISSING constants in obsolete `[-simp]` AND `[-instance]`
  header directives in derived copies, preserving valid directives, original
  files, statements, assumptions and all gates. No repair is enabled. The old
  disabled whole-simp-command helper is NOT sufficient for this narrower
  missing-name-only policy; do not enable it as-is on mixed valid/invalid names.
- At11:05:128 pollers,10 active issue jobs,52 nodes,7 current reviewed root
  arguments,0 verified/integrated roots. GitHub PR list remains empty.

## Follow-up checkpoint, 11:21 UTC — first actual candidate passes verification

- The real manager request739e7f62cd194f3888ebf43c1aab0ed0 is terminal
  `finished`, returncode0. Its original PID3255572 and final axiom-report
  process are gone. The private evidence is `verified` for p02 child issue#45,
  node `root.scalarization_modular-a1.holomorphic_scalarization-a1`, theorem
  `Submission.p02_es_177ebb5a_sm_holomorphic`, exact candidate
  `2ced4d3abd9f318f5490841e5e6ce28d9dfb7944` and base
  `f433f505e209a0721abf52e908d34801732a2e70`. Comparator and Lean kernel replay
  succeeded; the axiom report contains only propext, Classical.choice and
  Quot.sound. Frozen root remains1f74c284b125d4c45f527f2d621597fcf1e103a9.
- Evidence lives under the original private verification directory recorded
  above, in `root-scalarization_modular-a1-holomorphic_scalarization-a1-_i554f3s`.
  This is an author candidate check, NOT final outer acceptance or integration.
  The root's inherited scaffold warning does not describe the selected child's
  transitive axioms. No header repair, theorem weakening or gate bypass occurred.
- The owner independently collected the result and recorded its Round1 receipt
  at11:16:45. Its isolated worktree remains clean at the exact checked commit.
  Humanize's independent Round1 reviewer has started, as shown in the active
  `rlcr-process-v1.log`; fresh outer review/comparison and PR integration remain.
  The original worker taskr3ssmou3jiwm6qisb2x56m80s on hoa76 is still Running.
  No replacement, ownership takeover or worker-to-worker notification was used.
- At11:20 the fleet is128/128 Running, ten claims remain active and the ten
  current DAGs contain54 nodes. GitHub still has no solution PR. Keep issue#45
  open until the verified merge gate finishes; do not mark the experiment done.
- Reconfirmed that the canonical Pages URL serves separate per-problem graphs.
  Source5b9961b and Pagesac5ab90 remain deployed. Header-repair permission is
  still unanswered, and no normalization has been enabled.

## Follow-up checkpoint, 11:32 UTC — independent verification advancing

- P02#45's Round1 independent implementation review passed at11:23 with no
  remaining findings. It corroborated the original tool response and exact
  candidate receipt, inspected the finite-sum argument including n=0, and
  checked the pinned dependencies. Finalization then passed a fresh warning-fatal
  exact-type Lean check with permitted axioms, without changing the candidate.
  The nested RLCR loop has a `complete-state.md` and `finalize-summary.md`.
- The outer workflow itself advanced the node to `comparing` at11:30:05.
  Its fresh manager request9c015b0258d7494c8ab41762d51682c8 runs under
  PID3360163 for the same candidate2ced4d3abd9f318f5490841e5e6ce28d9dfb7944.
  This process is confirmed alive; the outer comparator has NOT finished.
  Do not confuse nested implementation completion with final proof acceptance.
- P07 child issue#60 (`root.curve_ring_equiv-a1.group_law_rebase-a1`, transport
  of a relative group law across a ring isomorphism) submitted real request
  8eed87142d7c425cae62a455a6d5e861 for candidate
  be37a2bac41bbeb5a672319ca281dbf3c367ce34. VerifierPID3347466 and challenge
  build supervisorPID3348079 are confirmed alive. Its challenge preserves the
  exact universe-zero child contract. No terminal result yet.
- Both current requests use the unchanged production checker. No controller
  restart, checker hot-deploy, duplicate verification or ownership transfer
  occurred. Preserve these exact running handles on the next turn.
- Read-only diagnosis confirms P03 feedbackv7 and P10 feedbackv12 repeat the
  missing-header-constant/context-repair blocker, not new mathematical gaps.
  Asked again for the narrow missing-name-only derived-copy repair; no user
  approval has arrived, and originals/derived headers remain unchanged.
  GitHub still has no solution PR; no theorem issue was closed as proved.

## Follow-up checkpoint, 11:41 UTC — queued recheck offloaded; storage diagnosis

- Both manager requests8eed… (p07#60, PID3347466) and9c015… (p02#45,
  PID3360163) remain Running. Their challenge builds are run-u447.service
  and run-u448.service, with Lean processes3349095/3349098 and3362466/3362539.
  Targeted kernel-stack inspection found `ceph_filemap_fault`/`filemap_fault`
  waits in the compiler threads, not a terminal process failure. CPU time and
  memory use continue changing. Host load was27 on8 CPUs with about12GiB
  available memory; no OOM result was observed. Preserve these jobs.
- Read-only sizing found14GiB of pinned packages and2.9GiB of Lean toolchain
  on shared Ceph. No artifact-cache copy, runtime change or live-process restart
  was made. A future local cache is only a performance possibility, not deployed.
- New real requestcd203d12717944b78318395950a03bfc arrived queued for p01#41,
  the SAME candidate15db3ef9f625c734560304ce3e21a07b20056041 previously rejected
  on header references. Checked its current HEAD, verified hoa1 Ready/Active
  with no active proof claim or other running verifier, and dispatched exactly
  this registered request through the existing immutable one-shot adapter.
  No issue ownership or worker start notification changed.
- Unit `fermat-swarm-verify-p01-20261007-1139.service`, dispatcherPID3387156,
  verifierPID3387184. Remote servicevnqf6z1ztqels8ju82rvp8ig7, task
  kchqtd21zojkdwgy4e2dc9w73 on hoa1 are Running. Private receipt is
  `fermat-verifier-dispatch.ZfocBD/jobs/cd203d12717944b78318395950a03bfc/operation.json`.
  Packet digestdd3297d24a578c356ffdf44a099f2201e336dd30b98d7dc43a0a9fd073e571cc.
  This is a recheck, not a new proof; no successful result or PR yet. Header
  repair remains unapproved and disabled. Collect these exact handles next.

## Follow-up checkpoint, 11:51 UTC — builds advance; artifact mirror in progress

- All three registered verification requests above are still live, not terminal.
  The earlier manager compiler PIDs3349095/3349098/3362466/3362539 finished their
  modules normally. P02's coefficient-cohomology/matrix-action builds took
  721/723s; its binary-form module subsequently built. P07's finite-adele module
  took991s and its two quaternion modules subsequently built in298s each.
  The enclosing verifier PIDs3347466/3360163 retain their request identities.
- Attempted one bounded low-priority sequential read of the already mapped,
  pinned `.olean` artifacts to warm the controller page cache. The first attempt
  did no reads because its compiler had already exited normally. The second,
  using live compiler3396694's maps, finished exit0 (tool session60279 closed).
  No file was changed. Do not attribute the earlier module completions to this
  read; they occurred first. Shared-filesystem delays persisted afterward.
- Started a private, LOW-PRIORITY artifact mirror copy for future diagnostics:
  `/var/tmp/fermat-verifier-reference.Z0kXAn` (0700). It copies the existing
  pinned `fermat-example/.lake/packages` then the4.33.1 toolchain, preserving
  contents/metadata. Original files, running verifier code and paths are unchanged.
  Tool exec session22163 is still running; shellPID3414512, copyPID3414513.
  At11:50 about3.5GiB was copied. **The mirror is incomplete and unvalidated;
  no verifier uses it.** Resume this exact copy handle, never consume a partial
  mirror or promote a diagnostic result to campaign proof acceptance.
- After copying completes, compare it byte-for-byte against the pinned source
  before any diagnostic. A local import benchmark may establish whether a future
  immutable verifier deployment benefits; any production cache integration still
  needs explicit identity binding/tests. No such integration has been implemented.
- GitHub PR list remains empty. P01 remote taskkchqtd21zojkdwgy4e2dc9w73 is
  confirmed Running; no new claim, check restart or header normalization occurred.

## Follow-up checkpoint, 12:04 UTC — outer check passed; remaining review and header failures

- P02#45 outer request9c015b0258d7494c8ab41762d51682c8 is now terminal
  finished0, with private evidence `verified`, kernel acceptance and permitted
  axioms for unchanged candidate2ced4d3abd9f318f5490841e5e6ce28d9dfb7944.
  Its PID3360163 is gone. The workflow advanced to `lean-review` at11:54:14.
  The final reviewer's OWN comparator request4edce24fdb124c73b1b49469f0fac33a
  is Running under PID3435979. Preserve it; no final review verdict or PR yet.
- P07#60 request8eed87142d7c425cae62a455a6d5e861 is terminal failed1, not
  still compiling. After building its dependency closure, frozen Submission
  failed on absent header constants `AlgebraicGeometry.Scheme.Hom.opensMapFinal`,
  `GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase`, and
  `RegularLocalRingQuotientAscent.dualNumberFst_apply`. This is a context failure,
  not evidence that the candidate theorem is false. PID3347466 is gone.
- P04 same-candidate recheck56f8cd9699284a04b0fd7cc6947db2cd was started
  by the broker in the freed slot, then finished1 with the same missing
  `Representation.TateResCor.cosetDecomp_apply` header reference. PID3433786 gone.
- P06 request0030da9d7cfe41b8802bedc2a94eeb81, candidate
  61cc48830412d5ca1b81a5dba52212816ebd51a5, subsequently ran under PID3449796
  and finished1 on the same three missing constants recorded at11:10. The new
  candidate only adds the injected-runtime ignore rule; no header repair was
  made. PID3449796 gone. No repeated failing check was promoted to acceptance.
- P01 remote requestcd203… and taskkchqtd21zojkdwgy4e2dc9w73 are still Running.
  The adapter PID3387184 retains the same service/task identities on hoa1.
- Local mirror copy session22163 finished0. Its Lean executable reports4.33.1,
  commit819816b2e0a3bf405af45ae5c7af2491d8f5bee6. Read-only Git checks confirmed
  all nine copied dependencies clean at their pins (`--no-optional-locks`).
  Full byte comparison against the original packages and toolchain is still
  running: tool session16862, shellPID3447598, package diffPID3447603. No
  differences have been reported, but that is NOT yet a completed validation.
  Mirror remains `/var/tmp/fermat-verifier-reference.Z0kXAn`, unused by verifiers.
- Added private `ImportProbe.lean` in that mirror for a future timing diagnostic
  (`import Mathlib`, an existing-theorem check, one trivial anonymous example).
  It has NOT run. Wait for the existing byte comparison to finish before using
  it. Neither a benchmark nor a copied cache is campaign proof evidence.
- No production verifier code was changed, no worker was restarted or notified
  to start an issue, no solved issue was closed, and no solution PR exists yet.
  Missing-name-only derived-header repair still awaits explicit user approval.
