# Fermat: distributed issue-and-PR experiments

Ten frozen problems from [humanfia/lean-test-problems](https://github.com/humanfia/lean-test-problems/tree/d8c69c0aae9dadbb9d0b4817ffc99ea07c2f7e99/Fermat),
using the theorem issue/PR workflow with 128 autonomous Swarm pollers.

## Current status

**Setup in progress; no theorem is claimed solved and issue resolvers are not yet
launched.** All 128 target nodes passed the credential-free readiness probe.
Readiness probes are not proof workers. This status will be replaced by observed
resolver and proof state when deployment is active.

The source contracts are in `Fermat/`. Their `sorry` terms are explicitly unsolved
specifications, never accepted solutions. The upstream definition library is
pinned by `Fermat/manifest.json`; the extracts are not standalone Lean projects.

## Required workflow

1. Each problem has a root issue carrying its frozen Lean contract and prose proof
   status. Decomposition creates an issue for every new named subtheorem.
2. Node workers poll the GitHub-backed issue list and claim eligible work through
   one transactional authority. No parent-to-worker start notification is used.
3. The initial deployment serializes mutations within each problem. Independent
   problems may run concurrently; idle pollers do not consume model sessions.
4. Solutions require exact-statement/context checking, transitive axiom checking,
   independent prose and Lean review, and a solution PR per theorem.
5. The exact verified solution is merged before its issue is closed. Parent/root
   acceptance checks the combined solution and every retained child interface.

The campaign is complete only when all ten roots and all introduced prerequisites
are verified and integrated. A website with the live dependency DAG is required;
no website is claimed deployed at this initial checkpoint.

## Provenance

- Benchmark revision: `d8c69c0aae9dadbb9d0b4817ffc99ea07c2f7e99`.
- Formalization revision: `6e837e75355538c7f80bab5b956861e86c4eacc2`.
- Lean: `leanprover/lean4:v4.33.1`.
- Mathlib: `db584cd6d46c92f209a44c0f1c829460d327499d`.
- Workflow development branch: `feature/swarm-issue-resolvers`.
- Node readiness: 128/128 distinct `hoa0`–`hoa127` tasks succeeded.

See `Fermat/LICENSE` and `Fermat/NOTICE` for source attribution and licensing.
