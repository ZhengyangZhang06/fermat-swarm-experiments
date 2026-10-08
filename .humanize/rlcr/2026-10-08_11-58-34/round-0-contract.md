# Round 0 Contract

## Mainline objective
Deliver the exact atomic theorem `Submission.p07_flp_point_equiv_857cd4d38c` in `Submission.lean`, with warning-fatal Lean verification and a successful configured comparator at a clean committed candidate.

## Target ACs
- AC1: Exact implementation of the sole frozen declaration using the accepted proof and pinned proof base.
- AC2: Warning-clean source, reviewed diff, clean committed candidate, and successful exact-node comparator.

## Blocking side issues in scope
- The local sandbox launcher lacks bubblewrap. Use the approved escalation mechanism for necessary local commands; preserve the filesystem and network restrictions.
- Discovered during verification: unchanged frozen `Submission.lean` attributes name three unavailable constants, and its inherited root declaration contains `sorry`. Diagnose and record these failures, preserving frozen context; only the configured exact-node comparator can establish acceptance.

## Queued side issues out of scope
- TaskCreate/TaskUpdate/TaskList are unavailable. Record task status in the goal tracker; adding a task service is outside this theorem's scope.
- Parent/sibling proofs, DAG reshaping, scaffold revisions, infrastructure cleanup, wiki publication, PR integration, and independent controller acceptance are outside this nested implementation round.

## Round success criteria
1. The frozen statement is implemented without additional named declarations or unsafe proof mechanisms.
2. Pinned local references are inspected and their provenance and compatibility recorded.
3. Warning-fatal Lean checks and source/axiom/dependency checks pass.
4. The exact selected-node comparator exits zero and prints `Your solution is okay!` at the committed candidate, with a clean worktree.
5. Goal tracker and summary record actual evidence, BitLesson `NONE`, and pending outer review; return control immediately after successful author verification.

All plan tasks route `coding -> claude` as required by the supplied routing convention. No decomposition or proof-authoring gate is reopened.

## Round outcome
The selected proof passes an isolated warning-fatal exact-type diagnostic and transitive axiom checks. Round success is **not achieved**: the literal source check fails, and the configured exact-node comparator exits 1 while compiling the unchanged frozen challenge's three invalid attribute references. Return this blocker to the recursive controller without changing the frozen source or claiming proof acceptance.
