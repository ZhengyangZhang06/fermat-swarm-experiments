# Round 0 Contract

## Mainline objective

Implement the exact frozen atomic declaration `Submission.p07_cre_group_law_857cd4d38c`, and produce a clean committed candidate passing its configured comparator.

## Target ACs

- AC1: exact single-declaration implementation, with local proof steps only.
- AC2: warning-fatal compilation, source/dependency/axiom audit, and passing selected-node comparator at a clean commit.

## Blocking side issues in scope

- The sandbox launcher lacks bwrap; use the execution tool's explicit escalation path for necessary commands.
- Any actual Lean, exact-contract, source-safety, or comparator failure for this selected node.

## Queued side issues out of scope

- TaskCreate/TaskUpdate/TaskList are unavailable; maintain their required task-state information in goal-tracker.md.
- Unrelated theorem work, historical scaffold interfaces, source-layout cleanup, and new decomposition.
- Independent reviewer rerun, wiki publication, DAG transition, and PR integration belong to the outer controller.

## Round success criteria

The single tracked theorem proves its frozen proposition without placeholders, new axioms, unsafe mechanisms, protected-file changes, or untracked named helpers. Warning-fatal compilation succeeds. The configured comparator runs only for this node at a clean committed SHA, exits zero, and prints `Your solution is okay!`. Record the exact evidence and return control without claiming outer acceptance. BitLesson selection is NONE (the knowledge base has no entries).
