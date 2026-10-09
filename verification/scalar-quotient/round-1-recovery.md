# Round 1 recovery audit

The author comparator gate remains failed for request `55a4a8c2acda411e956a98fab12bc763`, candidate `8e2496040595a4dddb246106fc5dba84db961735`, node `root.local_norm_order-a1.dvr_determinant_length-a1.scalar_quotient_length_order-a1`. This document and the adjacent JSON are local observations, not a remote receipt or acceptance record.

## Recovery findings

1. `/runtime/review-evidence/55a4a8c2acda411e956a98fab12bc763` remains absent. A scan of mounted `review-export.json` receipts found no request-ID or candidate-SHA match. The adjacent JSON records the observed count and file hashes. A path search beneath the mounted project/problem evidence and `/mnt/data/zhengyang-workspace/fermat-example/.humanize` did not recover this request's packet or operation receipt.
2. The newer `/runtime/operator-review-evidence-f116f3cae2f8/export-review-evidence.py` adds support for local-controller successes, but still excludes this failed remote request. `main` selects only `state='finished' AND returncode=0`; `collect` requires a zero-returncode request and `state='verified'` operation; `collect_inputs` requires a verified result. It exports hashed Lean inputs and an export receipt, not the actual checker implementation. The earlier `3155d2fa0d3e` exporter also supports only successful remote results.
3. Neither exporter was executed. They are controller-only publishers that write the destination and append to authoritative terminal logs. Running or weakening them in the worker would neither recover inaccessible private inputs nor establish their provenance. In particular, the failed request must never be marked verified to satisfy exporter predicates.
4. The mounted broker source exposes GET `/issues` and `/health`; `/verify` submits or polls checks. There is no artifact download route in that inspected copy. Its source is not authenticated as the implementation used for this request, so this is a finding about available local retrieval mechanisms, not proof about every remote endpoint. No broker request was sent this round.
5. `/runtime/flows/math-lean-flow/scripts/verify-frozen-node.py` lacks `verify_prepared`; the archived `math-lean-flow-missing-candidate-v1` copy contains it. The traceback alone cannot identify either copy as the executed checker. Their hashes are recorded as local observations only. The unrelated operator observation script can inspect a container's state; it cannot export its proof inputs or checker identity.
6. No controller-approved frozen-context reconciliation was found in the inspected selected-node contracts/identity records or runtime documentation. The pinned project still places `instNontrivialKaehler` in `Definitions/Def_AlgebraicCurve_IsCurveOver.lean:41` and `coe_torsion_smul` in `Definitions/Def_AlgebraicCurve_BaseChangeGalois.lean:311`, outside the frozen import chain. `rg -n 'frobNormRingHom' project/Definitions` returned no matches in the pinned local-project snapshot.

The selected theorem and 5,160-byte frozen prefix remain unchanged. The Round 0 log hash is unchanged. No new Lean code, helper, axiom, dependency change, comparator input substitution, controller change, or service action was made. No new comparator run was started because neither blocking prerequisite changed. The previous failed result is not being attributed to this audit commit.

## Required controller handoff (analyze -> codex)

Provide a read-only export of the existing failed request with:

- `prepared.json` whose canonical packet digest matches the logged `9bdfe6be7bdefdb821f3eb2c3f1d2903c57cbd6cd715c75fa3e1548d43b63769`, retaining candidate `8e2496040595a4dddb246106fc5dba84db961735` and this exact node.
- Every challenge and solution source file named by that packet, with byte hashes, plus the original operation receipt and terminal failure result. Preserve exit code 1 and the failure verdict.
- The actual executed verifier, packet runner, isolation launcher, and pinned tool identities, with request-specific bindings that let a reviewer distinguish executed code from an unrelated readable archive. Export no credentials.
- An explicit controller decision on reconciling unavailable frozen attribute targets while preserving the authoritative statement and context. Specify any authorized derived-input policy and its integrity check; the worker cannot infer permission to delete attribute lines, introduce stubs, replace the frozen source, or reframe the child theorem.

These are unresolved questions for the reviewer/controller, not instructions already executed. Once the prerequisites are resolved, the planned warning-fatal check and exact-node comparator must still succeed on a clean committed candidate. The separate reviewer comparator, publication, and DAG transition remain outer-controller work.

## Drift recovery handoff

Round 2 requested the missing controller repair policy and read-only failed-request export directly from the user. A single availability check found the export still absent and all previously recorded local verification mechanisms unchanged. There is no worker-only code change within this node's frozen boundary that can repair the independent challenge or establish the missing remote provenance. Resume implementation after those authoritative inputs arrive; do not treat another audit, commit, or unchanged comparator retry as mainline advancement. The acceptance gates remain unmet.
