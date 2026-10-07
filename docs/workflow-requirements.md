# Persistent autonomous theorem workflow requirements

These are requirements of the reusable `github-theorem-prover` workflow, not
exceptions for a particular Fermat experiment. Read this document when installing,
changing or launching the workflow. A new problem must not silently lose the
issue lifecycle, live visualization, ownership protections or parallel scheduling.
Implementation and deployment status are tracked separately in
[the parallelism plan](parallel-theorem-workflow-plan.md).

## Mathematical records and delivery

- Use the user-selected GitHub repository and a separate workflow development
  branch. Do not substitute an upstream repository as the publication destination.
- Freeze each original Lean problem, context, assumptions, definitions and pinned
  revisions. Give every root, recursively introduced subtheorem and named helper
  a stable identity, its own issue and its own solution PR.
- Every issue includes the exact Lean goal with its context, natural-language
  statement and proof, honest proof status, parent/root links and explicit
  prerequisite links. A proposed argument with gaps is not a finished proof.
- Create child issues before child proof execution. Preserve the reviewed
  immutable parent-to-child proof contract and an acyclic dependency graph.
- Keep independent natural-language and Lean review, exact statement comparison,
  pinned builds, kernel/transitive-axiom checks and integrated-tree verification.
  `sorry`, extra axioms, weakened statements or missing checks cannot be accepted.
- Once authorized for the configured repository, merge each exact verified PR
  through normal repository rules, verify the remote merge tree, then close its
  theorem issue. Preserve idempotent reconciliation after an uncertain API result.
  Root completion requires the root solution PR; solved children are insufficient.

## Autonomous, dependency-aware parallel workers

- Workers poll open issues and select ready work themselves. No other worker
  sends a start notification or assigns a leaf. Parent publication is a durable
  mathematical handoff, not a scheduling message.
- Eight pollers are the same-host default. For a supplied fleet, capacity is an
  explicit deployment input; this session requested all 128 authorized nodes.
  Multiple independent leaves of the **same problem** must be eligible together.
  Newly ready work must not wait for an unrelated slow problem or sibling.
- One authoritative durable claim per repository/issue and one job per worker
  prevent duplicate launches. Idle pollers are not reported as active proof jobs.
  A stale heartbeat never grants permission to take over live or uncertain work.
- Proof work uses isolated branches/worktrees. Shared DAG/name allocation,
  publication, bootstrap and Git integration require process/shared-filesystem
  coordination, not just Python thread locks or atomic whole-file replacement.
- Keep integration serialized where required, but not the entire proof process.
  A failed issue must not unnecessarily stop independent siblings. Preserve
  accepted proof checkpoints through retries, integration repairs and restarts.
- A legacy exclusive writer and a parallel writer must never mutate one project
  together. Validate cross-node locking and an actual two-leaf run before fleet
  rollout. If runtime support is incomplete, report it explicitly; do not call
  one-worker-per-problem scheduling the requested parallel workflow.

## Live website, not a fixed screenshot

- Publish a readable website for every problem and expose its actual URL alongside
  the workspace repository and workflow branch. For multiple problems, provide
  navigation and one independently readable dependency DAG per problem.
- Use contrasting node/edge colors, a legend, zoom/scroll, issue/PR links and
  distinct states for dependencies, proof review, verification and remote merge.
  An all-black or unreadable graph is a visualization failure.
- Separate the saved proof stage from current activity: queued/dependency-blocked,
  executing, verifying, integrating, merged, or needing intervention. A stored
  `decomposing` stage alone must not imply an active worker.
- Update from current durable DAG state and observed worker/claim/verification
  evidence. Show observation time and stale/unavailable data explicitly. Keep
  the last successful observation during outages; do not reset progress to queued.
- During additive worker-generation rollouts, observe every configured generation
  with a present catalog, validate current tasks and fresh heartbeats, and count
  each physical node once. Unpublished child contracts must be labeled pending
  issue publication, never presented as ordinary ready work or running jobs.
- Publish source changes and confirm deployment separately. Local HTML, a Git
  push and an actually deployed website are different completion claims.

## Reuse, configuration and authority

Repository, exact contracts, worker capacity, paths, authentication home and
integration authority are deployment inputs, not hard-coded experiment identities.
Keep credentials out of Git, issues, prompts, logs and the public status feed.
Use Ubuntu for this session and the authentication home authorized by applicable
current user/project instructions. Never use `rust.cat` or any endpoint below it;
keep network search disabled for this experiment. Direct authorized GitHub access
is not web search.

Copy [the ordinary configuration](../config.github-theorems.example.yaml) for
unapproved repositories, or [the authorized lifecycle configuration](../config.github-theorems.authorized.example.yaml)
when the user has authorized merge and closure for the chosen repository. Keep
that configuration with the problem so future invocations retain the same policy.
Do not copy integration authorization to a different repository implicitly.

Workflow changes belong in reusable code, configuration, documentation and
regression tests, followed by a separately verified deployment. Never fix only
one experiment's live files, silently hot-edit a pinned verifier, or claim that a
recorded requirement is already implemented. Pending changes remain visible in
the implementation plan until tested and deployed.
