# Round 0 contract

## Mainline objective

Implement and locally certify only the frozen atomic declaration `Submission.p04_eq_zero_of_prime_avoiding_annihilators`, then return the committed candidate to the recursive controller.

## Target ACs

- AC1: Exact theorem, accepted proof, no additional named helpers or protected-file changes.
- AC2: Warning-fatal checks, source/dependency/axiom audit, clean committed SHA, and successful exact-node comparator.

AC3 records the evidence and handoff for this same objective.

## Blocking side issues in scope

- The sandbox launcher lacks bubblewrap. Required shell commands use the available escalation mechanism.
- Any Lean, pinned-dependency, source-safety, cleanliness, or exact-node comparator defect that prevents AC1 or AC2.

## Queued side issues out of scope

- TaskCreate/TaskUpdate/TaskList are unavailable; track tasks and routing in the goal tracker.
- Historical scaffold changes, new decomposition nodes, unrelated parent/sibling proofs, wiki publication, DAG transitions, and external integration. The latter acceptance actions belong to the outer controller.

## Round success criteria

The exact selected theorem is the only new named theorem; warning-fatal verification and source/dependency/axiom checks pass; a clean committed candidate passes the configured selected-node comparator with exit zero and `Your solution is okay!`. The tracker and summary identify the candidate and evidence, use exactly one local-project reference entry, and leave independent acceptance pending. BitLesson selection is NONE because the knowledge base currently has no lessons.
