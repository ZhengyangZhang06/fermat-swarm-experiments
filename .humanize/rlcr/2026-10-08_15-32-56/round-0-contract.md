# Round 0 Contract

## Mainline objective
Implement exactly `Submission.p04_tia_tate_neg_one_transfer` and produce a clean committed candidate accepted by this node's configured author comparator.

## Target ACs
- AC1: exact, safe Lean proof with pinned provenance and warning-fatal verification.
- AC2: clean committed candidate and successful selected-node comparator.

## Blocking side issues in scope
- The sandbox launcher lacks bubblewrap; run necessary commands through the approved escalation mechanism.
- Any actual type, proof, build, axiom, protected-file, cleanliness, or selected-node comparator defect.

## Queued side issues out of scope
- Task system tools are absent; use the goal tracker task table with required lane/routing metadata.
- Different DAG shapes, extra helper nodes, scaffold revisions, unrelated parent or sibling declarations, and source-layout cleanup.
- Independent reviewer rerun, wiki publication, and DAG transition belong to the outer controller.

## Round success criteria
The exact atomic declaration is implemented without additional named helper theorems; warning-fatal Lean and source/axiom checks pass; its exact committed clean candidate passes the configured node comparator with exit zero and `Your solution is okay!`; tracker and summary preserve evidence and mark outer verification pending.

## Task execution
Use `[mainline]` task entries with `coding -> claude` routing. No BitLesson entries exist, so the selected lesson IDs are `NONE` for the initial task. Re-read the lesson file before each subsequent task.
