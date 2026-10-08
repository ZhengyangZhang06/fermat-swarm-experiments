# Round 0 Contract

## Mainline objective
Implement and verify exactly `Submission.p03_tate_uniformization_68cf3476` under the controller's frozen selected-node contract, using its approved dependencies and existing pinned library infrastructure.

## Target ACs
- AC1: Exact, safe theorem implementation with warning-fatal Lean checks.
- AC2: Clean committed candidate accepted by the selected-node comparator with complete required evidence.

## Blocking side issues in scope
- The sandbox command launcher lacks bubblewrap. Use the required escalation mechanism for necessary commands; preserve workspace boundaries.
- Any actual frozen-input, build, or comparator failure directly preventing AC1 or AC2; record concrete evidence before classifying it.

## Queued side issues out of scope
- Native TaskCreate/TaskUpdate/TaskList tools are absent. Maintain the task table as the available fallback.
- Unrelated cleanup, sibling/root validation, alternative DAG designs, new named helper nodes, proof/scaffold revision, and outer-controller review/publication/transitions.

## Round success criteria
1. The exact tracked theorem is implemented without prohibited source or protected-input changes.
2. Warning-fatal Lean checking and complete source-diff auditing succeed.
3. A clean candidate SHA passes only the configured `root.tate_uniformization-a1` comparator with exit zero and `Your solution is okay!`.
4. Supporting reference, policy, and BitLesson evidence is reported accurately, and control returns immediately after the implementation gate.

## Task routing and lessons
All implementation tasks route as `coding -> claude`, as required by the supplied plan. The BitLesson file was read before setup and contains no lesson entries; selection is `NONE`.
