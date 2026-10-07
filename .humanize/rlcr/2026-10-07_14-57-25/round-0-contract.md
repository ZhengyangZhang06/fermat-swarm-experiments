# Round 0 Contract

## Mainline objective

Implement and validate only `Submission.f036cc6b1f_fd_norm_bound` against the authoritative frozen child type, following its accepted parent-supplied natural proof.

## Target ACs

- AC1: Exact safe implementation with pinned local-project provenance.
- AC2: Warning-clean, axiom-audited, committed clean candidate passing the selected-node comparator.

## Blocking side issues in scope

- Shell sandbox lacks bubblewrap. Required commands use tool escalation; no project or controller state is changed to bypass it.
- Any actual selected-node elaboration, source-safety, dependency, or comparator failure.
- Confirmed during the round: frozen attribute commands reference two unavailable declarations. Diagnose and report this context blocker; preserve the protected proof base and accepted child statement.

## Queued side issues out of scope

- TaskCreate/TaskUpdate/TaskList tools are unavailable; record task states in the goal tracker.
- Root/sibling proofs, historical scaffold interfaces, new decomposition, unrelated cleanup, theorem-wiki publication, independent reviewer rerun, and DAG transitions.

## Round success criteria

The exact selected theorem is the only new named theorem; accepted proof and protected context remain unchanged. Warning-fatal Lean validation and transitive axiom checks succeed. The complete diff is inspected, candidate committed and clean, and the configured node comparator exits zero with `Your solution is okay!`. Evidence and remaining independent review are documented before returning control. BitLesson selections are NONE because the supplied knowledge base contains no lessons.
