# Round 2 Recovery Contract

## Recovered mainline objective
Restore a valid execution path for the exact selected-node verification and obtain its required warning-fatal build and comparator acceptance, preserving the frozen contract and selected declaration.

## Target ACs
- AC1: Exact selected theorem, unchanged hypotheses and conclusion, safe source, and warning-fatal Lean build.
- AC2: Clean committed candidate, trustworthy exact comparator inputs, exit zero, and `Your solution is okay!`.

## Root cause of stagnation
The proof candidate exists, but compilation fails in the independently prepared frozen challenge before solution comparison. Candidate-only proof edits cannot repair that input. The previous round documented the failure and missing remote provenance without obtaining the controller-owned repair or artifacts. Audit completion was not mainline acceptance progress.

## Truly blocking issues
- B1: The frozen attribute commands reference unavailable constants. No authorized reconciliation of the independently prepared challenge has been supplied to the worker.
- B2: The actual failed-request packet, checker identities, and request-specific endpoint authorization remain unavailable; the known read-only exporter excludes failed requests.

## Queued and out of scope
- Additional audit packaging, documentation-only source commits, proof simplification, inherited lint/deprecation cleanup, unrelated theorem validation, and infrastructure refactors.
- New named helper declarations, decomposition changes, edits to frozen inputs or checker policy without controller authorization, service or claim changes, and false success/loop-state updates.
- Task tools are unavailable; retain the required lane/routing metadata in the goal tracker.

## Success criteria for ADVANCED
An authoritative controller repair or already-authorized runnable input policy is available and its exact application resolves B1; inspectable controller-bound evidence resolves B2; the selected declaration passes its warning-fatal build and the exact-node comparator on a clean committed candidate with the required success marker. Merely rechecking files, adding audit artifacts, or repeating the same failing comparator does not qualify.

## Bounded recovery procedure
Check only for a newly supplied authoritative repair, relevant handoff, or exact-request export. If none exists, there is no credible worker-executable implementation step that can satisfy this contract under the current constraints. Record that fact and the concrete controller prerequisites in the required summary; do not create another audit-only source commit or run an unchanged comparator to simulate progress.

The user-required recovery contract, summary, and mutable tracker may be committed as workflow records. Such a commit is not implementation progress or comparator acceptance.

## Tasks and routing
- [mainline] R2-T1 Determine whether an authoritative unblocking input is now available — coding; claude; BitLesson NONE.
- [mainline] R2-T2 Apply only an authorized reconciliation and run the exact acceptance gates — coding; claude; BitLesson NONE; dependent on R2-T1 finding a valid path.
- [blocking] R2-Q1 Supply the controller-authorized input reconciliation and failed-request provenance export — analyze; codex if repository evidence cannot settle it.

No implementation starts before this contract exists. The Goal Tracker immutable section is unchanged.
