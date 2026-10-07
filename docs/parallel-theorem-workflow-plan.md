# Reusable parallel theorem workflow

## Goal

Carry the user's session requirements in the reusable GitHub theorem workflow,
not only the Fermat deployment. Run independent theorem issues concurrently
within and across problems, using all available authorized workers up to the
configured fleet capacity (128 in this deployment). Finish each original problem
through its own verified solution PR; a completed child is not a completed root.

## Acceptance criteria

- **AC-1 — Ready-node concurrency.** Different ready issues in the same project
  can hold claims simultaneously; the same issue and worker cannot. Prerequisites
  must be accepted/integrated according to the existing gates. Workers poll and
  choose issues themselves; parent workers never send start notifications.
  - Test 128 simultaneous claims for one issue: exactly one winner.
  - Test distinct ready issues in one project: multiple winners.
  - Test dependent, obsolete, unpublished, and already owned nodes: not offered.
- **AC-2 — Shared-state safety.** Concurrent workers cannot lose DAG updates,
  overwrite accepted proofs, duplicate named helpers, or race on Git integration.
  - Test independent process writers starting from stale snapshots.
  - Test conflicting writes fail closed; completed states cannot regress.
  - Test project-wide operations serialize while leaf proof processes overlap.
  - Validate filesystem locking across two actual cluster nodes before rollout.
- **AC-3 — Safe transition.** Existing exclusive claims and running verifier
  identities are retained. Legacy and parallel runtimes never write the same
  project concurrently. No timeout-based claim takeover or duplicate checks.
  - Test migration of the current ledger with live claims and restart/replay.
  - Test old-client inserts cannot bypass legacy/parallel exclusion barriers.
  - Use immutable runtime versions; preserve active proof worktrees and receipts.
- **AC-4 — Complete theorem lifecycle.** Every root and every named subtheorem has
  an issue containing its exact Lean goal/context and honest natural proof, and a
  dedicated verified solution PR. Recursive decomposition preserves an acyclic
  prerequisite DAG. Reuse issues/PRs on retry instead of creating duplicates.
  - Retain exact comparator, dependency, transitive-axiom, independent-review,
    and integrated-tree checks.
  - In the explicitly authorized session profile, merge the exact verified PR,
    confirm the remote tree, then close the issue. Never force-merge.
- **AC-5 — Live visualization.** Reusable status publication provides a readable
  per-problem dependency graph, issue/PR links, actual worker activity, and live
  progress. Waiting stages must not look like executing workers. Network/CDN
  failures preserve the last observation and expose staleness, not fake resets.
  - Test multiple simultaneous workers within one problem and waiting leaves.
  - Test one independent graph per problem and truthful proof/merge counters.
- **AC-6 — Reusable configuration.** Publish a documented workflow/profile and
  regression tests covering these requirements. Repository, problem contracts,
  worker capacity, deployment paths and authorized authentication home are explicit
  inputs, not private Fermat-only assumptions. The session deployment uses Ubuntu,
  `/home/ubuntu/.codex`, no web search, and never rust.cat.
  - New invocations using the session profile retain the requested behavior.
  - Generic workflows retain explicit merge authority rather than silently granting
    permission on unrelated repositories.

## Boundaries

- Preserve frozen statements, assumptions, source revisions and all proof gates.
- Missing-name header repairs are a separate unanswered approval request; this
  concurrency change does not authorize or enable them.
- Do not remove the project claim restriction before replacement shared-state
  protection and legacy migration tests are in place.
- Do not hot-edit active verifiers, force-release live claims, or alter unrelated
  Swarm services or drained nodes.

## Implementation sequence

1. Audit shared writes and add regression tests that expose the current project
   bottleneck and stale-snapshot races.
2. Implement opt-in per-issue claims with explicit legacy exclusion barriers.
3. Implement process-safe DAG/state and Git/publication coordination; retain
   isolated proof workspaces and independent proof execution.
4. Wire the new protocol through the reusable broker, runtime configuration,
   runner and example/session profile. Update generic status activity semantics.
5. Independently review, run unit/process tests and cross-node smoke tests.
6. Roll out immutable versions safely, preserving existing ownership and receipts.
   Verify multiple actual workers proving different leaves of one problem.
7. Continue the experiments through verified root PR integration. Deployment or
   scheduler tests alone do not satisfy mathematical completion.

## Current state

Reusable source and parallel runtime deployed (2026-10-07):

- Opt-in per-issue ledger claims, preserving legacy exclusive grants and old-client
  INSERT/UPDATE barriers. Contention tests include 128 issue owners and duplicate
  issue exclusion, mixed legacy/parallel races and concurrent constructors.
- Opt-in process-safe Store with three-way merge, in-place node refresh, conflict
  rejection, accepted evidence binding, graph checks and serialized wiki updates.
  Tests include actual spawned processes starting from the same stale snapshot.
- Persistent workflow requirements and an authorized merge/close configuration
  are linked from the reusable entry-point documentation.

Independent review found an accepted-contract hybrid merge and a wiki index race;
both were fixed with negative regression tests. Independent re-review passed the
13 shared-store and 19 claim tests then present. A subsequent positive lifecycle
test covers accepted integration through PR merge and issue closure, and two
configuration tests cover authorization persistence. The complete suite passed
267 tests with one optional browser test skipped, no failures/errors (2026-10-07).
The shared Store is now wired into the opt-in runtime. Selected-issue ownership,
shared bootstrap/Git/publication locks, exact integration-SHA receipts, per-issue
failure isolation, broker/runner generation checks and physical-node exclusion
are implemented. The complete suite subsequently passed 279 tests, with one
optional browser skip. A real cross-node flock test on hoa0 and hoa3 confirmed
shared inode identity and exclusion; actual P04 sibling jobs then ran together.

Immutable runtime `math-lean-flow-parallel-v1` was archived from `dabeb2c`.
The new 128-node fleet polls through a separate TLS broker, sharing the durable
claim ledger but filtering verification requests by protocol generation. Legacy
project intake was disabled, exact legacy containers and their exact checker
sandboxes were stopped, and only authoritative terminal evidence permitted claim
release. Original worktrees and RLCR receipts were preserved; cancellation did
not count as proof acceptance. No legacy project-wide grant remains as of 14:59
UTC. At that observation 29 issue jobs ran on 29 distinct machines, across nine
problems; all 128 pollers had fresh heartbeats. P09 remained disabled because its
complete theorem issue exceeded GitHub's body-size limit; that publication repair
is separate from scheduling readiness.

The live observer now merges both fleet snapshots, validates actual Swarm task
identity and freshness, and deduplicates idle daemons by physical node. The public
feed confirmed all 25 ready leaves of P01/P02/P04/P06/P07 executing concurrently
at 14:57:58 UTC; the four remaining root jobs resumed afterward. Available pollers
are not reported as running proofs. The status URL is
https://zhengyangzhang06.github.io/fermat-swarm-experiments/ .

Mathematical completion remains outstanding: child issue45/PR65 was verified,
merged and closed, but no original root was complete at rollout. Continue all
ordinary review, comparator, axiom, integration and merge/close gates.

The oversized-record publication fix was subsequently deployed from immutable
`math-lean-flow-parallel-v2` (`9d2ec18`). Full records use exact UTF-8 continuation
comments with digest-addressed identities; the current manifest switches only
after complete publication. Durable pending-create intents prevent duplicate
comments after an uncertain response and stale listing. P09 issue9 independently
claimed a worker on hoa25 and resumed real agent execution, bringing the active
ready-job count to 30 across all ten problems. Future claims use v2; existing jobs
keep their original immutable version. The old idle polling service was retired
only after no legacy grant or checker remained; proof files remain intact.
The final combined regression suite passed 299 tests with zero failures/errors
and one optional browser skip. This validates workflow behavior, not theorem
acceptance or completion of the ten original mathematical problems.

## Leaf review policy: Git diff and comparator-input integrity

The user's replacement policy keeps natural-language and decomposition reviews,
but removes mathematical/code-quality review from the nested Lean RLCR reviewer.
The reviewer adapter replaces official regular/full-alignment review prompts with
the scoped integrity audit and preserves Humanize's setup schema and completion
protocol. Generic final code review stays disabled. Outer review independently
reruns the exact comparator and attests a controller-pinned issue/candidate/input
identity. The controller rejects modified source, history, frozen contracts,
selected issue identity, or retained root dependency interfaces before acceptance.

Unit/integration regressions exercise the real Humanize bridge and reviewer
protocol as well as wrong-candidate, changed-contract, child-handoff, Git mutation,
and matching-attestation cases. A read-only canary accepted P02 issue51's actual
immutable child handoff. These are workflow checks, not new theorem acceptances.

Deployment uses a new immutable archive and the broker's `--runner-runtime`
startup override for future claims only. Old proof jobs retain their recorded
runner and review policy. This avoids editing a live catalog concurrently with
quarantine updates. Never restart a broker with owned live checkers or remove
`--preserve-existing-verifications` during an additive handover. Deployment
confirmation must be recorded separately from source/test completion.

Deployment confirmed 2026-10-07 16:10 UTC: immutable `math-lean-flow-integrity-v4`
contains workflow commit `86a7786`, pushed to the authorized workflow branch.
The final suite passed 369 tests (one optional skip); a completed hoa0 preflight
matched the archived Python source hashes. Only the recovery broker was restarted,
after verifying it had no owned live checker. Its authenticated health check
passed; all 69 existing job commands and all four live checker PID/start identities
were preserved. The broker now selects v4 for new claims without rewriting the
catalog. At this checkpoint no new claim had yet arrived, so this confirms routing
and deployment, not an observed v4 proof completion. Natural/decomposition reviews,
the immutable verifier and the decomposition depth limit are unchanged.

### Dedicated verifier capacity: source support, not deployment

The broker supports repeatable `--reserve-node hoaN` startup reservations for
dedicated verification capacity. A frozen, validated set rejects fresh proof
grants only; held claims, their immutable jobs, observation, release and all proof
acceptance gates remain unchanged. The shared catalog is not rewritten. Tests
cover physical-node exclusion, sibling grants, held-job recovery, terminal
safety, immutable configuration and CLI wiring. Before production use, configure
every intake-enabled broker and independently verify that each selected node has
no active or uncertain proof owner; reservations do not evict existing jobs.
See [the reference-cache deployment gates](verifier-reference-cache.md).

Source validation on 2026-10-07: all 395 tests passed (one optional skip),
including nine new reservation tests and existing broker/claim/verifier coverage.
Independent review confirmed held-claim recovery precedes reservation rejection.
No reservation deployment or campaign proof acceptance is implied by these tests.
