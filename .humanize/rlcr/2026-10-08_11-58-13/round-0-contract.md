# Round 0 contract

## Mainline objective
Implement the exact atomic node `Submission.f036cc6b1f_hecke_commute` in `Submission.lean` and produce a clean committed candidate that passes its configured comparator. Consume the accepted parent proof without revising it or the DAG.

## Target ACs
- AC1: Exact implementation and pinned local-project provenance.
- AC2: Warning-fatal validation, source/axiom audit, clean committed candidate, and exact selected-node comparator success.

## Blocking side issues in scope
- Sandbox execution is unavailable because bubblewrap is missing; approved escalated execution already works.
- Any actual local build, contract, or pinned-dependency defect that prevents verification of this node; do not modify protected files.

## Queued side issues out of scope
- TaskCreate/TaskUpdate/TaskList are unavailable; maintain equivalent persistent task records in the goal tracker.
- Historical scaffold changes, sibling/root proofs, repository cleanup, and other unrelated issues.
- Independent reviewer rerun, theorem-wiki publication, DAG `proved` transition, and issue/PR integration are outer-controller tasks.

## Round success criteria
Only the tracked new theorem is implemented with the frozen type. Warning-fatal Lean validation, full source-diff inspection, and transitive axiom checks pass. The clean committed candidate passes only `HUMANIZE_NODE_ID=root.good_hecke_commute-a1` through the prescribed comparator, exiting zero with `Your solution is okay!`. Record the candidate SHA and evidence, maintain honest pending-review status, and return control.

## Task routing and lessons
All T1–T4 tasks are `[mainline]`, tagged `coding`, with owner `claude` as prescribed by the user routing convention. Read `.humanize/bitlesson.md` before each task; current selection is `NONE` because it contains no lessons.
