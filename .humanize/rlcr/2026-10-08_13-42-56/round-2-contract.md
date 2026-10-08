# Round 2 recovery contract

## Recovered mainline objective

Obtain configured exact-node comparator acceptance for the clean committed candidate of `Submission.p04_pb_60221840b0_noncentral_cancellation`, with the comparator inputs authenticated and the frozen contract preserved.

## Target ACs

- AC1: preserve the exact theorem and protected inputs; resolve request-specific comparator-input integrity with controller-owned evidence.
- AC2: run the configured selected-node comparator on the exact current clean SHA and require exit zero plus `Your solution is okay!`.

## Root cause of stagnation

The candidate already compiles locally, but the configured comparator fails while compiling its separate frozen challenge. Prior rounds added documentation and retrieved a failure response without repairing that controller-owned input or obtaining its private packet. Those records did not satisfy AC2, and additional documentation commits made the saved comparator result stale with respect to HEAD.

## Truly blocking issues

- The frozen challenge references missing `Representation.TateResCor.cosetDecomp_apply`. The worker is not authorized to alter that protected challenge, pinned dependencies, or checker.
- The reviewer needs the controller's actual request-specific operation receipt, packet/evidence/source inventories, generated challenge/solution files, checker copies/hashes, and toolchain/reference identities. The available worker interface does not expose them.
- The previously requested controller export/reconciliation location has not been supplied. Check once for newly available evidence, then use the configured comparator on a stable committed candidate to establish the current gate result. Do not treat another failure as advancement.

## Queued and out of scope

- Additional historical-response documentation, standalone evidence utilities, theorem refactoring, decomposition changes, unrelated cleanup, sandbox installation, and unavailable Task-system tooling.
- Parent/sibling/root comparators, independent outer review, wiki publication, issue closure, merge, and DAG transitions.

## Success criteria for ADVANCED

The exact-node comparator accepts the current clean SHA with exit zero and the required marker, and authenticated controller evidence resolves the comparator-input integrity objection. A running job, fresh failed request, consistent local log, or documentation commit does not meet these criteria. If the same protected challenge still fails and no authenticated export is available, report that this worker cannot credibly achieve ADVANCED without controller intervention; preserve the real failure and stop expanding the evidence-documentation work.

BitLesson selection: NONE; the knowledge base contains no entries.
