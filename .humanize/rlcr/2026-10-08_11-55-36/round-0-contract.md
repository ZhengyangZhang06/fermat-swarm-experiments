# Round 0 Contract

## One mainline objective

Implement and verify the exact atomic theorem `Submission.p06_9e0f5043ff_dmc_cokernel_units` using the frozen parent-supplied natural proof and pinned library infrastructure.

## Target ACs

- AC1: Exact, safe implementation with no additional named helper theorems.
- AC2: Warning-clean, source-audited, committed candidate with a clean worktree and a passing exact-node comparator.

## Blocking side issues in scope

- The sandbox launcher cannot run because bubblewrap is unavailable. Use the explicit escalation mechanism for required local commands.
- Any Lean elaboration, source-safety, clean-tree, or exact-node comparator defect in this theorem.

## Queued side issues out of scope

- Task-system tools are unavailable; track the same task metadata in the goal tracker.
- Historical scaffold changes, other DAG nodes, unrelated source cleanup, and root or whole-benchmark validation.
- Independent reviewer comparator, theorem-wiki publication, and DAG `proved` transition are outer-controller responsibilities after this implementation returns.

## Round success criteria

1. Read the accepted proof and frozen problem and search the pinned local-project snapshot; record exactly one `local-project` reference-use entry.
2. Implement only the exact selected declaration, using no unapproved dependencies or new named helpers.
3. Run warning-fatal Lean checks and inspect the complete source diff and transitive axioms.
4. Commit the candidate; run only the configured child comparator at a clean SHA; require exit zero and `Your solution is okay!`.
5. Record the candidate and evidence in the summary, mark reviewer verification pending, and return immediately to the recursive controller.

## Task routing and BitLesson

T1–T5 are `[mainline]`, `coding`, owner `claude` as required by the plan's routing convention. Re-read `.humanize/bitlesson.md` before each task; initial selection is `NONE` because the knowledge base contains no lessons.
