# Round 0 Contract

## Mainline objective

Implement and verify only `Submission.p09_af497904fe_ff_cyclotomic_supply` at the selected node's exact frozen type, preserving the accepted proof, current DAG, dependencies and protected inputs.

## Target ACs

- AC1: Exact, source-safe implementation in `Submission.lean`.
- AC2: Warning-clean, committed, clean-worktree candidate passing the configured selected-node comparator.

AC3 supplies the required audit record for these targets.

## Blocking side issues in scope

- The sandbox command launcher cannot start because bubblewrap is missing. Request escalation for necessary commands; do not change unrelated environment services.
- Any concrete Lean or comparator failure preventing AC1 or AC2, including compiler-copy diagnostics handled strictly under the pinned operator policy.

## Queued side issues out of scope

- TaskCreate/TaskUpdate/TaskList are not exposed. Use the goal tracker's tagged task ledger and disclose this limitation.
- Unrelated cleanup, parent/sibling verification, new helper nodes, and scaffold or proof revisions.
- Fresh reviewer comparator, wiki publication and DAG transition are subsequent outer-controller responsibilities.

## Round success criteria

The exact selected declaration is implemented, warning-fatal checks and source-safety review pass, its committed clean tree passes only the configured node comparator with exit zero and `Your solution is okay!`, and the final tracker and summary accurately cite evidence and the single local-project reference source. Pending or failed verification must be recorded honestly.

## Task execution discipline

Tasks T1–T5 are `[mainline]`, default routing `coding -> claude` as requested. Read `.humanize/bitlesson.md` before each task; its initial empty knowledge base yields selection `NONE`. Do not create untracked named helpers or change loop-control state.
