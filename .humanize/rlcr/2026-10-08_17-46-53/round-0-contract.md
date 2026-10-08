# Round 0 Contract

## One mainline objective

Retain and validate the existing implementation of the frozen atomic theorem `Submission.p04_pb_60221840b0_noncentral_cancellation` and return its clean committed candidate after the exact node comparator passes.

## Target ACs

- AC1: Exact frozen theorem, complete proof, and no additional named helpers.
- AC2: Warning-fatal build, complete source/integrity audit, clean committed candidate, and configured comparator exit zero with `Your solution is okay!`.

## Blocking side issues in scope

- Sandbox launcher lacks `bwrap`; use approved escalated execution for required local commands.
- Any actual type, elaboration, warning, source-integrity, dependency, or comparator failure preventing AC1/AC2. Earlier runs failed in the controller-owned frozen challenge import; only the current configured comparator can establish whether that failure remains.

## Queued side issues out of scope

- Task API tools are unavailable; maintain their task records in the goal tracker.
- Unrelated cleanup, other DAG nodes, new decomposition, root comparator, independent outer rerun, wiki publication, and DAG state transition.

## Round success criteria

The single tracked theorem preserves the frozen type and compiles warning-fatally. The reviewed diff contains no placeholders, new axioms, unsafe mechanisms, extra named helpers, or protected-input changes. The configured child comparator succeeds on a clean exact commit. The tracker and summary contain accurate evidence, local-project reference provenance, and BitLesson selection `NONE`; outer verification remains explicitly pending.
