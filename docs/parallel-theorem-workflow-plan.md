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

Reusable source foundations implemented, not deployed:

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
The Store is deliberately not wired into the production runtime yet. Selected-issue
scope, shared bootstrap/Git/publication locks, multi-worker activity reporting,
failure isolation, broker/runner wiring, cross-node tests and safe rollout remain.
Production still enforces one active claim per problem. No live claim policy has
been changed and no active proof worker/verifier has been restarted.
