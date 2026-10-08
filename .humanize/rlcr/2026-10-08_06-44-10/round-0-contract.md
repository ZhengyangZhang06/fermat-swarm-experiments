# Round 0 Contract

## One mainline objective

Implement the exact atomic theorem `Submission.p06_9e0f5043ff_llm_localized_residue_factors` and produce a clean committed candidate accepted by its configured selected-node comparator.

## Target ACs

- AC1: Exact atomic implementation using the accepted proof and pinned local-project references.
- AC2: Warning-fatal build, source and axiom audits, clean committed SHA, and exact comparator success.

## Blocking side issues in scope

- The shell sandbox cannot launch because bubblewrap is absent. Execute necessary commands through the tool's explicit escalation mechanism.
- Any concrete type, library compatibility, build, source-safety, dependency, or comparator failure that prevents this exact node from passing.

## Queued side issues out of scope

- TaskCreate/TaskUpdate/TaskList are unavailable; maintain equivalent task metadata in the required goal tracker.
- Other DAG nodes, alternative decomposition, scaffold changes, general cleanup, root comparator, wiki publication, and DAG state transitions.

## Round success criteria

The sole new named theorem matches the frozen contract; warning-fatal compilation and transitive axiom checks pass; protected files and pinned dependencies remain unchanged; the committed clean candidate passes only the selected-node comparator with exit zero and `Your solution is okay!`. Record evidence and reference use in the round summary, mark independent verification pending, and return control immediately. BitLesson selection is NONE (the knowledge base has no lessons). AC3 is the administrative handoff requirement.
