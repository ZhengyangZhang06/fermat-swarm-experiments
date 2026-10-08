# Round 0 Contract

## Mainline objective
Implement the atomic selected node `Submission.p06_9e0f5043ff_sdp_clear_first_column` using the accepted parent-supplied proof, then obtain a committed, clean, warning-clean candidate passing its exact configured comparator.

## Target ACs
- AC1: Exact frozen theorem, accepted proof, and pinned local-project provenance.
- AC2: Warning-fatal build, source/dependency/axiom audit, committed clean candidate, and successful exact-node comparator.

## Blocking side issues in scope
- Sandbox execution fails because bubblewrap is unavailable; request escalated execution for necessary local commands.
- Any build, frozen-contract, source-safety, dependency, clean-tree, or exact-node comparator defect in this selected node.
- Recovered B2: earlier comparator request/process states require authoritative reconciliation; service restoration is unconfirmed.
- Recovered B3: inherited frozen Submission attribute errors require trusted environment resolution; preserve the frozen source.

## Queued side issues out of scope
- Task tools are unavailable; preserve equivalent task status and coding/claude routing in the goal tracker.
- Parent/sibling proofs, alternative decomposition, source-layout refactors, unrelated cleanup, wiki publication, and DAG transitions.

## Round success criteria
- The one selected declaration is implemented without additional named helper theorems or protected-file changes.
- Warning-fatal Lean verification and transitive axiom checks pass against pinned dependencies.
- The complete candidate diff is reviewed, committed, and clean at the verified SHA.
- Only the selected-node comparator is run; it exits zero and prints `Your solution is okay!`.
- The tracker and summary provide provenance, validation evidence, and BitLesson Delta (currently NONE). Independent review and outer-controller acceptance remain pending.

## Task discipline
All mainline work is tagged `coding`, owned by `claude` as required by the plan's routing convention. Read BitLesson before each task; no lessons currently exist. AC3 records the handoff evidence for this objective.

## Round 0 evidence update
The existing HEAD already contains the selected implementation. Audit it and retain it if correct. Prior review records recovered during T1 establish external verification concerns; do not manufacture a new source change or comparator request to bypass those concerns. The objective and acceptance criteria are unchanged.
