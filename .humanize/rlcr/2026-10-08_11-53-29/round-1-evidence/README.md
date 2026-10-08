# Existing failed verifier request: evidence handoff

This directory records a fresh authenticated lookup of the existing finished request. It is not a new comparator run, a reconstructed packet, or proof acceptance.

| Identity | Value |
|---|---|
| Request | `27fd3948c4be48cba0db03b6310d8b8d` |
| Candidate | `62bf03d3d829c00f23001f66cbe936b3ae5c37b7` |
| Node | `root.tate_index_annihilation-a1.cohomology_transfer-a1.hom_complex_transfer-a1.hom_coset_average_laws-a1` |
| Reported packet digest | `73650432c983cebce7710a75aae780626ff6a7433c4d41fa48b6e819a02afaff` |
| Result | Finished, exit 1; no `Your solution is okay!` |

`existing-request-result.json` contains only the public result fields returned through the broker's authenticated `/verify` interface; no request credentials were retained. `existing-request.log` is its exact output field. `evidence-index.json` records their SHA-256 digests and the limits of this evidence.

The result identifies the error as `/output/result/challenge/Submission.lean:10:18`, unknown `Representation.TateResCor.cosetDecomp_apply`. The run stopped while building the challenge; no candidate comparison result was produced. The fixed proof base `bcd46b8accac96c56c6f3c3a4eba8516986e7d3f` contains that attribute reference, and the pinned Tate definitions do not define the symbol.

## Evidence still required from the controller

Expose read-only copies of the retained artifacts for this exact request:

1. Its `operation.json` receipt, including the request/candidate/packet binding, `code_sha256`, service/task identity, and reference-cache identity.
2. The receipt's packet directory, including `prepared.json`, `evidence.json`, and all challenge/solution sources covered by `source_sha256`.
3. The executed code directory containing `verify-frozen-node.py`, `swarm-verifier-packet.py`, and `swarm-verifier-selftest.py`, checked against the receipt's hashes.
4. The corresponding remote `output/result` sources and retained checker/toolchain binary or reference-cache identity evidence.

The packet's canonical digest must equal `73650432c983cebce7710a75aae780626ff6a7433c4d41fa48b6e819a02afaff`. Do not substitute the available `comparison-identity-v3.json`: it describes candidate `b111ca1b6059bb13c5f6948208e3ec5aa40daf18`.

## Access and repair boundary

The mounted broker source exposes `/issues` and `/health` GET routes and `/verify` POST results, without a packet-download route. Its finished-request result contains only request ID, revision, state, return code, and output. The shared project/reference evidence search found no packet for this request; `/var/tmp` is empty, and `/verifier`, `/input`, and `/output/result` are not mounted locally. The dispatcher source retains packet/code/output data in a private operator directory outside worker projects. Available runtime archives are not evidence of which archived code actually executed.

The available verifier sources copy the challenge from the frozen proof base and the solution from the candidate separately; child challenges import that base's `Submission`. Therefore editing this node's proof cannot repair the observed challenge-side failure. The controller must reconcile the invalid challenge input while preserving the selected frozen contract and authoritative dependency context, then run the configured exact-node comparator. This handoff makes no alteration to the frozen context, checker, or acceptance state.

The reconciliation decision and evidence export remain unresolved controller actions. A repeated request with identical invalid inputs would not resolve either blocker.
