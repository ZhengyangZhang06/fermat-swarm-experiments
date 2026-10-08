# Controller handoff: exact norm-range verification blocker

This document requests retained evidence and controller reconciliation. It is not an evidence receipt or an acceptance record.

## Failed operation to export

- Request: `3c23c64cf708425894ed055e65e97df9`
- Candidate: `b0ad04bde368623b3856a4a8c4bc5a22cbb80ac0`
- Node: `root.tate_index_annihilation-a1.tate_zero_transfer-a1.invariant_restriction_norm_range-a1`
- Declaration: `Submission.p04_tz91_invariant_restriction_norm_range`
- Reported packet digest: `5d6f827a86b081735a0577d66517d8ce7565f3af15d87a0e4dd8248d785e69dc`
- Reported terminal result: exit 1 during the independent challenge build, missing `Representation.TateResCor.cosetDecomp_apply`; no success marker.

Provide a controller-authenticated read-only copy of the original operation, preserving the failed status and original bytes:

1. A nonsecret receipt binding request, candidate, node, packet digest, original checker hashes, reference-cache identity, service/task identity, and terminal result. Exclude claim tokens, authentication headers, and private request bodies.
2. Original `prepared.json`, all challenge/solution Lean inputs in `source_sha256`, selected declaration/configuration, and retained `evidence.json` or an explicit statement that a final evidence file does not exist. Preserve original relative paths.
3. The executed `code/verify-frozen-node.py`, `code/swarm-verifier-packet.py`, and `code/swarm-verifier-selftest.py`, bound to the original operation's `code_sha256`. Include the actual compiler/comparator configuration and toolchain/dependency/reference identities. A newly installed checker is not a substitute.
4. An operator manifest binding the exported files to that exact operation, plus the readable mount path.

The inspected controller runner retains `operation.json`, `code/`, a packet path, and `output/result/` under its private per-request directory. This documents the protocol; it does not identify the checker actually executed for the failed request. The existing exporter selects only finished requests with returncode 0 and verified receipts. It cannot export this failed operation unchanged. Supply a diagnostic export path that preserves failure rather than relabeling the operation verified.

## Newly staged possible reconciliation

Read-only archive `/runtime/flows/math-lean-flow-header-policy-v1` matches all 131 file hashes in its `DEPLOYMENT.json`, which records commit `6d906c02a82427d7213acd18fffcd522e0696aef`. Its verifier hash is `7f49056d55f7f0732554c94e7eb654634a11a8e0396fa7c552b01785a335dac9`.

Read-only guidance `/runtime/operator-header-policy-v1/policy.json` has digest `96fc18eb6b8cbdad1beec37ca318ab2cf08ac1dda8ebf7cbfe1d6d51abf32f96`. The p04 entry binds source revision `2475a3790d7ba0c3b10be8086001b154a45be597`, root `Rep.isZero_tateCohomology_of_forall_sylow`, and complete contract hash `42953c937798c4a4ff8c5a5266936d11cb7f7836ede7175b49e6d157bd9e9551`; these match the local frozen source. Its sole omitted line is header line 10, in private compiler copies only.

The code retains reversible original/derived hashes and requires a Lean absence probe for every omitted target, while preserving exact comparison, kernel replay, dependency, and axiom gates. The documentation records authorization for the narrow repair but states that production rollout requires further preflight and an immutable checker transition. No active deployment receipt was available here. Both worker guidance fields and the project's policy configuration fields are absent. The public guidance explicitly grants no verifier authority and permits no committed header edits.

The controller must provide the actual rollout/verification-path identity before this worker can rely on that policy, and establish the appropriate warning-fatal boundary for the selected child while retaining the frozen root placeholder. Do not change this node's type, accepted proof, or empty dependency list. Once the authorized path is active, rerun only the configured selected-node author comparator on the exact clean committed candidate. The old failed-operation provenance check remains separate from any new successful request.

## Worker findings

The expected `/runtime/review-evidence/3c23c64cf708425894ed055e65e97df9` mount is absent. A bounded search found no request/candidate/digest match in 588 available metadata files. Controller-only `/input`, `/output`, `/reference`, `/verifier`, `/controller`, and Docker socket paths are absent. The inspected broker exposes no evidence-download route. No controller database, exporter, verifier, runtime policy, frozen source, automatic loop state, or running service was modified.
