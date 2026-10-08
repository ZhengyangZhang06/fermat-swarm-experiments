# Round 1 contract

## Mainline objective
Resolve the selected node's failed author-verification gate by locating and auditing controller-authenticated inputs for request `3c23c64cf708425894ed055e65e97df9`, then applying any controller-authorized reconciliation that preserves the frozen contract and permits exact-node verification.

## Target ACs
- AC2: Successful warning-fatal and exact-node verification at a clean committed candidate, with authenticated comparator-input provenance.
- AC4: A concrete, accurate handoff of results and any remaining controller-only blocker.

## Blocking issues in scope
- The failed request's prepared challenge/candidate sources, packet, selected declaration/configuration, and checker/toolchain/dependency identities are not yet available for audit. The expected candidate is `b0ad04bde368623b3856a4a8c4bc5a22cbb80ac0` and reported packet digest is `5d6f827a86b081735a0577d66517d8ce7565f3af15d87a0e4dd8248d785e69dc`.
- The comparator's independent challenge fails on the frozen missing `Representation.TateResCor.cosetDecomp_apply`; the local full-file warning-fatal build also rejects the inherited root placeholder. Reconciliation must preserve the frozen mathematical contract and come through the authorized controller boundary.

## Queued issues out of scope
- No queued code issues were identified by the reviewer. Task-system tools remain unavailable; retain lane, routing, and owner metadata in the tracker.
- Proof refactors, new named helpers, DAG/decomposition revisions, parent/sibling work, cluster service changes, outer reviewer comparator, wiki publication, PR lifecycle, and acceptance-state transitions.

## Success criteria
Obtain read-only, controller-authenticated evidence binding the exact failed request to its original prepared inputs and executed checker identities; audit those bytes against the immutable selected-node contract. If an authorized reconciliation is available, verify its scope, commit the candidate, and require the configured exact-node comparator to exit zero with `Your solution is okay!`. If those external prerequisites remain unavailable, document the actual access checks and a precise controller artifact request; do not claim AC2 success or manufacture verification evidence. Keep the tracker immutable section unchanged and finalize this round's summary with one local-project reference_use entry and BitLesson Delta.

All execution tasks use `[mainline]`, routing `coding`, owner `claude`. BitLesson selection: `NONE` (empty knowledge base).
