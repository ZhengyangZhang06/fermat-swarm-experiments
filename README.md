# Fermat: distributed issue-and-PR experiments

Ten frozen problems from [humanfia/lean-test-problems](https://github.com/humanfia/lean-test-problems/tree/d8c69c0aae9dadbb9d0b4817ffc99ea07c2f7e99/Fermat),
using the theorem issue/PR workflow with 128 autonomous Swarm pollers.

## Current status

The campaign is running. The [live dashboard](https://zhengyangzhang06.github.io/fermat-swarm-experiments/)
reports observed workers, dependency waits, verification and merged proofs.
Root completion requires the final checked solution; activity or solved children
alone do not establish it. The dashboard separates current activity from saved
stages: `Saved: decomposing` does not mean a worker is currently decomposing.
Arrows point from prerequisite to dependent: A → B means B uses A.

The source contracts are in `Fermat/`. Their `sorry` terms are explicitly unsolved
specifications, never accepted solutions. The upstream definition library is
pinned by `Fermat/manifest.json`; the extracts are not standalone Lean projects.

## Required workflow

1. Each problem has a root issue carrying its frozen Lean contract and prose proof
   status. Decomposition creates an issue for every new named subtheorem.
2. Node workers poll the GitHub-backed issue list and claim eligible work through
   one transactional authority. No parent-to-worker start notification is used.
3. Independent ready theorem issues may run concurrently within each problem.
   Git integration remains coordinated; idle pollers do not consume model sessions.
4. Solutions require exact-statement/context checking, transitive axiom checking,
   independent prose/decomposition review, and a solution PR per theorem.
   Lean leaves use deterministic Git identity gates and the exact comparator;
   non-leaves retain Lean integrity review.
5. The exact verified solution is merged before its issue is closed. Parent/root
   acceptance checks the combined solution and every retained child interface.

The campaign is complete only when all ten roots and all introduced prerequisites
are verified and integrated. [Root issues](https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues)
are recorded in `campaign.json` and `proofs/`. The dashboard source is in
`site/`; its deployment observation must not be confused with live proof progress.
The explicit [Pages workflow](.github/workflows/pages.yml) deploys `site/` and
`campaign.json` from `main`; the separate `status-live` branch supplies observations.
Activity labels expire after three minutes without a fresh published observation;
this reports stale monitoring data, not stopped proof workers. The publisher uses
a temporary Git index for each attempt and stages only the current observation's
three files. It preserves the checkout index and any unrelated staged changes,
retries failed pushes, and never removes an unknown Git lock automatically.

## Provenance

- Benchmark revision: `d8c69c0aae9dadbb9d0b4817ffc99ea07c2f7e99`.
- Formalization revision: `6e837e75355538c7f80bab5b956861e86c4eacc2`.
- Lean: `leanprover/lean4:v4.33.1`.
- Mathlib: `db584cd6d46c92f209a44c0f1c829460d327499d`.
- Workflow development branch: `feature/swarm-issue-resolvers`.
- Node readiness: 128/128 distinct `hoa0`–`hoa127` tasks succeeded.

See `Fermat/LICENSE` and `Fermat/NOTICE` for source attribution and licensing.
