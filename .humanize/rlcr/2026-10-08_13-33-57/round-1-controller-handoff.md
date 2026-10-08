# Required controller handoff

This is an artifact request, not an evidence receipt, authorization, or proof acceptance.

## Exact failed operation

- Request: `20cace6a340046d5ad4d0884dd3a16f9`
- Candidate: `b92f7f6a88b239299fb61797260421ce450a2272`
- Node: `root.tate_index_annihilation-a1.tate_zero_transfer-a1.invariant_restriction_norm_range-a1`
- Reported packet digest: `9fb2a32a215c2639092ad79ad997486560998f5f62cd264695db23d77428849f`
- Recorded exit: 1; no success marker.
- Recorded failure: independent challenge `Submission.lean:10:18`, missing `Representation.TateResCor.cosetDecomp_apply`.

## Required read-only artifacts

Expose a controller-authenticated diagnostic copy of the existing operation, preserving its actual failure state and original bytes:

1. The nonsecret operation identity/receipt binding request, candidate, packet digest, service/task identity, reference-cache identity, copied checker hashes, and terminal return code. Do not publish ledger request bodies or authentication/claim tokens.
2. The original `prepared.json`, `evidence.json`, and every challenge/solution Lean input enumerated in `source_sha256`, including both comparator entrypoints and imported Submission files. Preserve original relative paths. If a failed operation lacks a final evidence file, state that absence rather than fabricate verified evidence.
3. The request's actual copied `code/verify-frozen-node.py`, `code/swarm-verifier-packet.py`, and `code/swarm-verifier-selftest.py`, bound to the receipt's `code_sha256` values. A currently installed checker is not a substitute for the executed copy.
4. The retained terminal task/result evidence and pinned reference/toolchain/dependency records needed to audit the environment binding.
5. A controller-supplied manifest and read-only mount location binding these copies to the original operation. Existing successful request exports cannot substitute for this failed request.

The inspected remote verifier implementation retains these under its private `FERMAT_SWARM_VERIFIER_DIRECTORY/<request-id>/` directory, with `operation.json`, `code/`, the packet path recorded in the receipt, and `output/result/`. That controller directory is not mounted in this worker. This describes the inspected protocol; it does not establish the deployed checker identity of the failed request.

## Why the current export path cannot serve this request

`/runtime/operator-review-evidence-f116f3cae2f8/export-review-evidence.py:203` and `/runtime/operator-review-evidence-3155d2fa0d3e/export-review-evidence.py:153` select only finished requests with returncode 0. Both also require a verified operation receipt (lines 46–48). Running either unmodified cannot export the recorded exit-1 operation. No export code, verifier code, ledger row, or original evidence was modified in this round.

## Subsequent reconciliation

After the authentic inputs are available, the controller must provide an authorized reconciliation for the frozen challenge's absent attribute target and the full-file warning-fatal boundary, while preserving all frozen mathematical assumptions, definitions, and conclusions. The worker cannot fix an independently built challenge by modifying only the selected theorem. Any repaired candidate still requires the configured exact-node author comparator to succeed at its exact clean committed SHA; the current isolated type/axiom diagnostic is insufficient.
