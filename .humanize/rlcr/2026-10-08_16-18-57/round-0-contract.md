# Round 0 contract

## Mainline objective

Implement the single frozen atomic theorem `Submission.p06_9e0f5043ff_wll_length_sum_factors`, then produce a clean committed candidate passing its configured author comparator.

## Target ACs

- AC1: Exact frozen declaration and accepted proof, with no new named helpers.
- AC2: Warning-fatal build, source/protected-file and transitive-axiom audits, clean committed candidate, and exact selected-node comparator exit zero with `Your solution is okay!`.

## Blocking side issues in scope

- Missing sandbox launcher: run necessary commands through the escalation mechanism.
- Any actual compilation, exact-type, source-safety, dependency-cleanliness, or comparator failure that prevents this node from passing.

## Queued side issues out of scope

- Unavailable TaskCreate/TaskUpdate/TaskList tooling: maintain equivalent task records in the goal tracker.
- Historical inherited-attribute report unless reproduced in current source.
- Parent/sibling theorem work, DAG redesign, source-layout refactors, wiki publication, and outer independent acceptance.

## Round success criteria

The only new named theorem is the requested declaration; its warning-fatal build and source/axiom audits pass; its committed candidate has a clean worktree; the exact node comparator exits zero and prints `Your solution is okay!`. Record the evidence and local-project provenance, then immediately return control for outer review. AC3 documents this handoff without expanding the round's implementation scope.

## Task discipline

All plan tasks are `[mainline]` and `coding -> claude` per the requested routing convention. Read `.humanize/bitlesson.md` before each task; currently it contains no lessons, so selection is `NONE`. Preserve the accepted natural proof and frozen operational contract.
