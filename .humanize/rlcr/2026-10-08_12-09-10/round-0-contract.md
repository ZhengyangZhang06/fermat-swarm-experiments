# Round 0 contract

## One mainline objective

Repair the exact selected node's comparator-input evidence handoff so the existing exact theorem candidate can be independently audited at its committed SHA, then return control to the recursive controller.

## Target ACs

- AC1: Retain and audit the exact tracked theorem and complete source diff without changing its proof boundary.
- AC2: Produce a Git-clean committed candidate, successful warning-fatal selected-node validation, and accessible authentic comparator input/output evidence.

AC3 is the reporting requirement supporting this objective.

## Blocking side issues in scope

- The prior review's controller-owned prepared.json, evidence.json, and actual generated inputs are unavailable at its reported path.
- The sandbox launcher lacks bubblewrap; required shell commands need escalated execution.

## Queued side issues out of scope

- TaskCreate/TaskUpdate/TaskList tools are unavailable; maintain equivalent task records in the goal tracker and report the limitation.
- Independent outer reviewer rerun, theorem-wiki publication, DAG proved transition, and issue/PR integration are controller responsibilities after this invocation returns.
- No decomposition, source-layout refactor, proof redesign, or unrelated theorem validation.

## Round success criteria

1. Audit accepted handoff, immutable node type, pinned local-project provenance, and complete source diff.
2. Retain authentic controller evidence and actual challenge/solution files in storage accessible to the reviewer, with provenance and candidate binding recorded.
3. Commit all candidate changes and verify a clean worktree at the compared SHA.
4. Run the prescribed exact node comparator; require exit zero, `Your solution is okay!`, warning-fatal compilation, and permitted transitive axioms.
5. Finalize the goal tracker and round summary with evidence and BitLesson selection `NONE`, explicitly leaving independent acceptance to the outer controller.

No Lean implementation edit is planned unless a permitted integrity or comparator failure requires it. No specialized code simplifier agent is exposed; an unchanged Lean proof does not need optimization.
