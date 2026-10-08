# Round 2 Recovery Contract

## Recovered mainline objective
Complete the configured exact-node author comparison for `Submission.p04_hct139_coset_average_laws` after the controller supplies authenticated retained inputs and a contract-preserving reconciliation of its reported challenge-compilation failure.

## Target ACs
- AC2: the prescribed selected-node comparator exits zero and prints `Your solution is okay!` at a clean committed candidate, with its required integrity and axiom checks.
- AC1: both frozen contracts, the accepted proof, the dependency boundary, and protected source/configuration remain unchanged throughout recovery.

## Root cause of stagnation
The local theorem and integrity checks already pass. The author comparator instead reports an unknown constant in its generated frozen challenge. Its actual input trees and executed checker identities have not been published to this worker. Rounds 0 and 1 produced evidence and access findings without obtaining the controller-owned prerequisite. Treating repeated access audits or documentation commits as implementation progress would perpetuate that stagnation.

## Truly blocking issues
1. No controller-published receipt/packet/source/checker/configuration/toolchain export is available for request `57ab107b6cbe4d8fa357f54f85cbc10f`, compared candidate `3a27a31217cf316378e3f369c07be89d2d782359`, reported packet digest `8eae94f717e28255d24d18e41693afb40379dc34e87052c7226021273d6e215b`.
2. No supported reconciliation has been supplied for the reported missing `Representation.TateResCor.cosetDecomp_apply` in the generated challenge. Changing protected inputs or inventing a candidate shim is outside the selected-node contract.

## Queued and out of scope
No queued code defects. Runtime Task-tool availability, exporter feature work or deployment, more evidence-inventory audits, proof refactoring, new helper nodes, controller service changes, and unrelated comparisons are out of scope. Required local reporting is not mainline progress.

## Concrete criteria for ADVANCED
An actual controller-provided export is obtained and authenticated against the failed request; a supported reconciliation preserves both frozen contracts; and the prescribed exact-node author comparison succeeds at a clean committed candidate. An inventory count, unchanged failure, local compilation, or reporting-only commit cannot qualify.

## Present feasibility and stop condition
There is no presently executable builder-only recovery path: the reviewer requires artifacts and reconciliation owned by the controller, and the pending request for their location has no answer. If that prerequisite is not supplied, report BLOCKED with AC2 unmet, preserve the failed verdict, and return the exact required input. Do not claim this round advanced, start an unchanged duplicate comparison, or edit loop state.

## BitLesson selection
NONE. The knowledge base has no entries; no fix is currently justified.
