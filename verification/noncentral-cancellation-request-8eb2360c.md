# Noncentral cancellation: failed-request evidence for Round 1

This record addresses the input-integrity review for issue #167. It neither
changes the selected proof nor asserts comparator acceptance.

## Authenticated terminal response

The existing request `8eb2360c9c1944858de2904f4bc03cff` was retrieved from the
configured broker's `/verify` endpoint at `2026-10-08T15:44:36.108222+00:00`,
using its original identity and the live claim. No new request was created.
TLS certificate validation remained enabled; credentials were not persisted.

- Checked candidate: `4dd65597e744bf62fda9781085a91cf7598d0b2e`.
- Selected node:
  `root.tate_index_annihilation-a1.cohomology_transfer-a1.restricted_standard_homotopy-a1.equivariant_prism_homotopy-a1.prism_boundary_identity-a1.noncentral_cancellation-a1`.
- Reported packet digest:
  `81732769fc85cefe02bf663e984e1f7a9582ed96b886cb7e3cc9114c2838c232`.
- State: `finished`; return code: **1**; success marker absent.
- [Exact response bytes](noncentral-cancellation-request-8eb2360c-response.json).
- [Retrieval metadata](noncentral-cancellation-request-8eb2360c-retrieval.json).
- Response SHA-256:
  `02fb32f2b8e45a65c5b1111be1221f763a2e3e72d92d2722ea6588e8ad1dc084`.
- Output SHA-256:
  `98de232817c0dd641ffebf435fa23500d5ba47ae4e3407912e042eb1c380cf44`.

The response's request and revision, and its packet-validation line's node,
candidate and digest, were checked against the saved Round 0 result. Its output
is byte-identical to the corresponding suffix of that round's comparator log.
It fails exporting the frozen challenge with
`Submission.lean:10:18: Unknown constant Representation.TateResCor.cosetDecomp_apply`.
This authenticated response is not a signed export of the packet or checker.

## Why the published evidence does not cover this failure

The read-only `/runtime/review-evidence` tree has no directory for this request.
Searching its JSON/Markdown/text metadata for the exact request and packet digest
found no match. Searching `review-export.json` receipts for the selected node
also found no match. No evidence belonging to another node was substituted.

The visible controller publisher explains this gap:

- `/runtime/operator-review-evidence-f116f3cae2f8/export-review-evidence.py:203`
  queries only finished rows with `returncode=0`.
- Lines 46–48 additionally require a successful ledger row and an operation
  receipt in state `verified` with return code zero. The local-controller path
  at lines 66–67 likewise rejects failed requests.
- This publisher's SHA-256 is
  `f116f3cae2f8a8397c6e0cbbb4030804133b8b1c7807fd2b9941be86721d6ec7`.
- The older publisher at
  `/runtime/operator-review-evidence-3155d2fa0d3e/export-review-evidence.py`
  imposes the same successful-request restriction at lines 46–48 and 153.

Thus these publishers cannot export this failed request unchanged. This is a
finding about the visible publisher code, not proof of the private deployment's
identity. Neither publisher was executed or modified by this worker.

The visible recovery-v3 broker exposes no artifact-retrieval route; terminal
`/verify` responses contain only request, revision, state, return code, and
output. The mounted transport wrapper has SHA-256
`f3202ba84d3096d6e05a494f073e454e5aa82c4383a08b171832acbc28c5d9b2` and is a
read-only recovery-v3 bind mount. These observations do not identify the actual
private checker copies or authenticate the packet's source inventory.

## Required controller handoff

Provide an authenticated export tied to the request, candidate, and reported
packet digest above, covering:

1. Actual `operation.json` with request/candidate identity, terminal state,
   service/task/specification identity, packet digest, and checker hashes.
2. Actual `prepared.json`, `evidence.json`, source inventory, and generated
   challenge/solution Lean inputs and configuration/dependency identities.
3. The deployed `verify-frozen-node.py`, `swarm-verifier-packet.py`, and
   `swarm-verifier-selftest.py` copies or independently authenticated identities.
4. A controller-authorized reconciliation of the frozen challenge import that
   preserves the frozen theorem contract, followed by the configured exact-node
   comparator on a clean committed candidate.

The existing successful-request publisher is insufficient for item 1–3; a
controller export capable of preserving failed-operation evidence is needed.
The worker requested the location of this export and authorized reconciliation.
No such input was available while preparing this record. No protected source,
accepted proof, dependency, comparator, or loop state was changed. The theorem
source remains SHA-256
`c54d318b7ff4ae1be82b8513d0d1ec5c1a6607c3e2401b5447878e919628de57`.

## Reference use

`reference_use` contains exactly one entry:

- source: `local-project`
  snapshot: `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8`
  manifest: `manifest.json` pins project
  `2475a3790d7ba0c3b10be8086001b154a45be597` and mathlib
  `db584cd6d46c92f209a44c0f1c829460d327499d`.
  findings: Query
  `cosetDecomp_apply|def cosetDecomp|theorem cosetDecomp|lemma cosetDecomp`
  over `project/Definitions`, `project/Submission.lean`, and `mathlib/Mathlib`
  found only the unresolved attribute reference in `project/Submission.lean:10`;
  no defining declaration was found. Inspected `project/Submission.lean:1–22`
  and `project/Definitions/Def_GroupCohomology_TateCohomology.lean:1–90`.
  No reference proof was copied or new library reuse introduced this round.

## BitLesson Delta

Action: none
Lesson ID(s): NONE
Notes: The knowledge base is empty. Existing instructions suffice for recording
an unresolved controller boundary; no solved implementation lesson was added.
