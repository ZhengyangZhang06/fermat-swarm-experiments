# Swarm issue-resolver extension

- The user explicitly authorized `/home/ubuntu/.codex` on 2026-10-07 for the new
  Fermat experiments. Use that local authentication and API configuration.
- Never use rust.cat or any endpoint under it. Keep network search disabled.
- Preserve existing theorem acceptance gates: exact frozen contracts, independent
  prose/Lean review, the real comparator, transitive axioms, and verified PR trees.
- Do not deploy the same-host IssueWorkerPool unchanged across machines.
- Scope deployments to this experiment. Do not alter other Swarm services or
  reactivate drained nodes.

## Reusable workflow policy

- Read `docs/workflow-requirements.md` before changing or launching this workflow.
  The user's issue/PR, autonomous parallel scheduling, verified merge/close and
  live per-problem DAG requirements apply to future runs, not only this campaign.
- Put fixes in reusable code, configuration and regression tests before deployment.
  Preserve repository-scoped integration authority; the authorized configuration
  is not permission to merge in an unrelated repository.
- Keep `docs/parallel-theorem-workflow-plan.md` accurate about tested source versus
  live deployment. Per-issue ledger support alone does not make the runtime safe
  for concurrent writers. Never remove legacy exclusion before shared-state,
  selected-issue ownership, Git/publication and cross-node tests are satisfied.
