# Round 1 Contract

## Mainline objective

Advance exact-node verification of `Submission.p04_tz91_invariant_restriction_norm_range` by resolving the existing request's evidence gap and determining whether an authorized frozen-context reconciliation is available, while preserving the exact candidate theorem and frozen inputs.

## Target ACs

- AC2: a clean committed candidate and successful warning-fatal, exact-contract verification.
- AC3: reviewable evidence and an accurate handoff to the recursive controller.

## Blocking issues in scope

- The author comparator failed before candidate comparison because the immutable challenge references `Representation.TateResCor.cosetDecomp_apply`, absent from its imported context.
- The existing request's prepared packet, source snapshots, and deployed checker/toolchain identity are not yet available to the reviewer.
- The explicit warning-fatal check rejects the unchanged frozen root `sorry`.

Investigate available controller artifacts and documented read-only evidence retrieval. Do not alter protected inputs, verifier code, accepted proof, DAG, or loop state. Do not create a replacement packet or rerun the comparator merely to replace the existing evidence.

## Queued issues out of scope

- TaskCreate/TaskUpdate/TaskList remain unavailable; maintain requested task metadata in the goal tracker.
- Cleanup, source-layout changes, proof simplification, unrelated theorems, new helper nodes, wiki publication, and DAG transitions.

## Concrete success criteria

1. Locate and integrity-check the existing request's actual prepared evidence, or document the exact missing artifacts and access boundary after inspecting available retrieval mechanisms.
2. Determine whether the controller has supplied a reconciliation compatible with the frozen contract. If so, follow that authorized path and require the original acceptance gates; otherwise preserve the candidate and report AC2 as blocked.
3. Keep the tracker immutable section unchanged, record one local-project reference_use entry and BitLesson Delta, and finalize Round 1 evidence without claiming acceptance from a digest, build, or prior audit alone.
