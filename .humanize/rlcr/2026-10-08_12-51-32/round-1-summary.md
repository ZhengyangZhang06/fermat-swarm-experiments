# Round 1 Summary

## Outcome

**AC2 remains blocked; the theorem is not accepted.** The investigation found why the existing failed request's inputs are not available through the review-evidence mount: both available operator export implementations select only successful requests and require verified receipts. No authorized reconciliation of the frozen challenge or warning-fatal boundary was found.

Theorems: only `Submission.p04_tz91_invariant_restriction_norm_range` (issue #134). No Lean proof, frozen context, dependency, verifier, accepted proof handoff, DAG, or loop-state file was edited. The original plan and Round 1 contract remain the scope authority. The requested round documents are the only changes being committed.

## Existing request identity

| Field | Value |
|---|---|
| Request | `3c4734b1a32a4102ad85c0665a7e97af` |
| Candidate tested in Round 0 | `3489ec1665d22e9d9eea739e5be2f02ed6c9d489` |
| Validated packet digest reported by that request | `aecc4eabbbd9042ed080ebc98826b573c4e80d46be4272c9257e946d71690aa0` |
| Existing author result | Exit 1; no success marker |
| Failure | `challenge/Submission.lean:10:18`: unknown constant `Representation.TateResCor.cosetDecomp_apply` |

The Round 0 reviewer independently confirmed local source integrity. This round did not repeat the comparator or warning-fatal build: the reviewer requested the existing request's actual inputs, and no relevant source/context change justified another run. The previous warning-fatal failure on the inherited root `sorry` remains unresolved. Neither a packet digest nor the runtime code inspected below is presented as the missing request's actual prepared evidence.

## Evidence investigation

1. The remote paths `/input`, `/output`, `/reference`, and `/verifier` remain absent in this worker. The selected node's local directory contains older `comparison-identity-v1/v2.json` and `comparator-v1/v2.log` artifacts; these are not the current failed request's prepared packet. A request-ID search found the current execution transcript in `rlcr-process-v3.log`, not its remote inputs.
2. A bounded `rg --files --hidden` search under `/mnt/data` and `/runtime`, excluding dependency and Git trees, located `/runtime/review-evidence`. Its 114 `*/prepared.json` manifests were inspected only for the selected node/request identity. There was no match; `/runtime/review-evidence/3c4734b1a32a4102ad85c0665a7e97af` does not exist. No unrelated theorem was validated.
3. `/runtime/operator-review-evidence-f116f3cae2f8/export-review-evidence.py:203` selects `WHERE state='finished' AND returncode=0`. Lines 46–49 also reject nonzero results or operations without verified status. `/runtime/operator-review-evidence-3155d2fa0d3e/export-review-evidence.py:153` has the same success-only selection, with the same guards at lines 46–49. Thus neither inspected exporter can publish this exit-1 request. The active deployment identity of either script has not been established; the observed missing request and both available implementations are the evidence.
4. `/runtime/flows/math-lean-flow-missing-candidate-v1/scripts/swarm-verify-frozen-node.py:141–171` documents the private retained layout: `FERMAT_SWARM_VERIFIER_DIRECTORY/<request-id>/operation.json`, copied checker files under `code/`, prepared inputs under `prepared/`, and execution artifacts under `output/result/`. The operation receipt records `packet`, `packet_digest`, and `code_sha256`.
5. `/runtime/flows/math-lean-flow-missing-candidate-v1/scripts/verify-frozen-node.py:481–506` validates `prepared.json`, its canonical digest, all `source_sha256` entries, checker identity, reference-cache binding, and `evidence.json`. Lines 434–449 show that the child challenge still imports `Submission`; they provide no reconciliation of the missing frozen attribute target. These files explain the protocol, but have not been bound to the failed request's deployed copies.
6. `/runtime/flows/math-lean-flow-missing-candidate-v1/_recursive_lean/swarm_broker.py:331–355` exposes GET `/issues` and `/health`, with no artifact-download route. `/verify` uses the submission protocol; no speculative request or replacement verification was sent.

The runtime and controller evidence remained read-only throughout. A concise information request for a readable controller export or authorized handoff was submitted; no answer or artifact path was available when this summary was finalized.

## Required controller handoff

Expose a read-only diagnostic copy of the **existing failed request**, retaining its actual exit and status, including:

- The request's `operation.json` identity fields, original `prepared.json`, `evidence.json`, and every challenge/solution Lean source listed in `source_sha256`.
- The exact `code/verify-frozen-node.py`, `code/swarm-verifier-packet.py`, and `code/swarm-verifier-selftest.py`, bound to the receipt's `code_sha256` values.
- The pinned reference-cache/toolchain/dependency identity records used by that request and its retained terminal task/result evidence. Omit credentials and claim tokens.

Bind the copy to the request ID, candidate SHA, and digest listed above. Do not mark the failed request verified or edit an existing successful export to make it qualify. Once available, its actual sources and identities can be audited against the frozen contract. Separately, the controller must supply an authorized reconciliation of the challenge's unknown constant and the selected-node warning-fatal boundary while preserving the problem. This implementation invocation cannot repair the independently built frozen challenge by editing only the selected theorem.

## Local integrity checks

At the start and end of the investigation, tracked source diffs against `3489ec1665d22e9d9eea739e5be2f02ed6c9d489` were empty. Before the documentation commit, HEAD and frozen base `bdf84353b3f38a42e108b54861b6fb18b5085996` both had tree `03626ca9262a23a25b3d99922a1be86f00fecd32`. The documentation commit does not claim a fresh comparator result for its new SHA.

| Local artifact | SHA-256 |
|---|---|
| `Submission.lean` | `c13498ba0ba606ad1da2307c84868e59e3d64a4119de6b9358295200516f02c0` |
| Frozen `Fermat/Thm_Rep_isZero_tateCohomology_of_forall_sylow.lean` | `42953c937798c4a4ff8c5a5266936d11cb7f7836ede7175b49e6d157bd9e9551` |
| `Definitions/Def_GroupCohomology_TateCohomology.lean` | `e9fe2119399354d446f25bad2407a330ae5c5eee0cd6ef3d1a2c131364724b24` |
| Local `/runtime/flows/math-lean-flow/scripts/verify-frozen-node.py` | `30954f9ae216d73e4fb125cae5c04795a8aae08b799dfbc779c7fd6a2f9af433` |

The local checker hash is explicitly a local identity, not the unavailable remote checker identity. The Tate definition file matches both the reference snapshot and original frozen commit byte-for-byte.

## Reference use

`reference_use` contains exactly one entry: source **local-project**.

Snapshot: `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8`. Its manifest pins project `2475a3790d7ba0c3b10be8086001b154a45be597` and mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`.

Ran `rg -n 'normBar|normToInvariants|import|TateResCor|cosetDecomp_apply'` on the snapshot's `project/Definitions/Def_GroupCohomology_TateCohomology.lean` and inspected lines 1–60. The file imports Mathlib and defines `normToInvariants`, `normBar`, and `normBar_mk` at lines 30–43. No `TateResCor` or `cosetDecomp_apply` match occurs in that file. Its exact bytes match both the current worktree and frozen source commit, confirming this round did not repair the failure by changing the imported definition. The full frozen problem was reread; no network search or alternative problem acquisition occurred. No new upstream declaration was reused, and no transitive-axiom acceptance is claimed.

## Task and file status

- T5 evidence-location investigation completed, pending reviewer verification; its findings leave the evidence-access blocker unresolved.
- T3 exact-node verification remains blocked. AC2 is unsatisfied.
- T6 finalized the requested Round 1 contract, summary, and mutable goal-tracker updates. The immutable tracker section is unchanged.
- TaskCreate/TaskUpdate/TaskList remain absent from exposed tools; the tracker preserves lane and coding/claude routing metadata.
- No code was written or changed, so there was no code-simplifier review to perform. No outer-controller proof acceptance, publication, merge, or DAG transition was attempted.

## BitLesson Delta

- Action: none
- Lesson ID(s): NONE
- Notes: the BitLesson file has no entries and was reread before task execution. The export limitation was diagnosed but not repaired, so no resolved-failure lesson was added.
