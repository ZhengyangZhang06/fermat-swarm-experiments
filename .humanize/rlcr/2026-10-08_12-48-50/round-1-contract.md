# Round 1 Contract

## Mainline objective

Resolve the selected node's comparator-input integrity blockers using existing controller-owned evidence, preserving the exact candidate theorem and frozen contract, so the configured comparator can establish acceptance of the committed candidate.

## Target ACs

- **AC1:** Preserve the frozen boundary and establish the actual checker/challenge input provenance.
- **AC3:** Obtain trustworthy exact-candidate comparator evidence and record an accurate controller handoff.

## Blocking issues in scope

- The author comparator exited 1 while compiling its frozen challenge, before candidate comparison, on three unknown attribute targets.
- The existing packet and actual deployed checker/source hashes were not available to the reviewer.
- The wrapper has an uncommitted endpoint-override change; provenance and authorization of the deployed configuration must be established.

## Queued issues out of scope

- Protected imported modules' existing style/deprecation warnings and unavailable TaskCreate/TaskUpdate/TaskList tools remain documented from Round 0.
- Proof refactors, decomposition changes, new theorem nodes, parent/sibling/root verification, wiki publication, DAG transitions, and unrelated service or worker changes are out of scope.

## Success criteria

Locate and audit existing controller-owned packet contents, actual challenge source hashes, and deployed checker identities for request `dd68dd8a2e544dc896fe934231484345` and candidate `5ac520c36a3e8629d2403b56926f2f4b50c1f85c`. Establish authorization for the configured wrapper/endpoint or explicitly retain the unresolved blocker. Any challenge-input correction must be controller-authorized and preserve the frozen mathematical contract; no candidate-side alteration of protected inputs is permitted. Exact-node acceptance still requires exit zero and `Your solution is okay!` for the clean committed candidate. Do not issue another nested verification run merely to fill provenance gaps. If controller-owned evidence or correction cannot be obtained within the authorized scope, document precisely what is missing and leave acceptance unmet.

## Tasks, routing, and lessons

The mainline tasks are read-only evidence acquisition, targeted integrity analysis, and evidence finalization. Executed tasks use `coding -> claude`; questions unresolved by repository evidence use `analyze -> codex` and are stated in the summary. BitLesson selection is `NONE` because the required knowledge base has no entries. Task-system tools remain unavailable; maintain task states in the goal tracker.
