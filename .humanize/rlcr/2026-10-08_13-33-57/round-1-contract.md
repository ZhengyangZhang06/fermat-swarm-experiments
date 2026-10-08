# Round 1 Contract

## Mainline objective

Resolve the selected node's exact-comparator verification blocker by obtaining and auditing controller-authenticated inputs for failed request `20cace6a340046d5ad4d0884dd3a16f9`, and complete the required author gate if an authorized frozen-context reconciliation is available.

## Target ACs

- AC2: A clean committed candidate must pass the configured exact-node comparator; isolated compilation and terminal logs alone cannot satisfy the gate.
- AC3: Retain a reviewable, accurately bound evidence handoff and clear unresolved blockers.

## Blocking issues in scope

- The failed request's actual prepared packet, challenge/solution sources, and checker identities are absent from the currently mounted evidence directory.
- The frozen challenge fails on `Representation.TateResCor.cosetDecomp_apply`; the full-file warning-fatal boundary also includes the inherited root sorry. Any reconciliation must come through the authorized controller boundary and preserve the frozen contract.

## Queued issues out of scope

- TaskCreate/TaskUpdate/TaskList are unavailable; maintain the lifecycle and coding/claude routing in the goal tracker.
- Proof refactors, new named helpers, decomposition changes, unrelated nodes, cluster service changes, wiki publication, reviewer comparator, issue closure, and DAG acceptance transitions.

## Concrete success criteria

The failed request's controller-authenticated read-only bundle binds candidate `b92f7f6a88b239299fb61797260421ce450a2272` and packet digest `9fb2a32a215c2639092ad79ad997486560998f5f62cd264695db23d77428849f` to actual inputs and checker hashes. Any supplied reconciliation is checked against the frozen declaration, with no protected-input substitution. The configured comparator must then exit zero and print `Your solution is okay!` for a clean committed candidate before AC2 can be marked complete. If the required controller artifacts or reconciliation are unavailable, record the exact access limitation and required handoff; do not manufacture evidence, modify verification state, or repeat unchanged failing checks as a substitute for progress. BitLesson selection: NONE (no entries).
