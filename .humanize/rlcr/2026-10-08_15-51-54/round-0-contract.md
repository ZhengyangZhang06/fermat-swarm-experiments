# Round 0 Contract

## Mainline objective
Implement the exact atomic theorem `Submission.p04_ht_restricted_standard_comparison` and produce a clean committed candidate passing the selected-node author comparator. Consume the accepted proof without changing decomposition.

## Target ACs
- AC1: Exact Lean proof of the frozen selected declaration.
- AC2: Warning-fatal validation and successful exact-node comparator at a clean committed SHA.

AC3 applies throughout as the provenance and scope constraint.

## Blocking side issues in scope
- The sandbox launcher lacks bubblewrap. Use the tool's explicit escalation mechanism for necessary shell execution.
- Any Lean/API, dependency-integrity, axiom, source-safety, or exact-node comparator failure that prevents AC1 or AC2.

## Queued side issues out of scope
- TaskCreate/TaskUpdate/TaskList are unavailable; maintain the goal tracker's task ledger instead.
- Unrelated cleanup, parent/sibling proofs, alternative DAG designs, new helper nodes, wiki publication, independent reviewer rerun, and DAG transitions.

## Round success criteria
1. Only the tracked theorem is newly declared; its type matches the frozen contract.
2. Pinned local references and accepted prose support the implementation; record exactly one `reference_use` entry with source `local-project`.
3. Warning-fatal Lean checks, source review, and permitted transitive axiom checks pass.
4. Commit the candidate, confirm a clean worktree, and run only the configured comparator for this node. Require exit zero and `Your solution is okay!`.
5. Finalize the tracker and summary with truthful evidence and pending outer review; return control without waiting for outer-controller actions.

## Task routing and lessons
T1–T4 are `[mainline]`, `coding -> claude` as required by the plan's routing convention. The actual executing agent is Codex. Read `.humanize/bitlesson.md` before each task; initial selection is `NONE` because it contains no lessons.
