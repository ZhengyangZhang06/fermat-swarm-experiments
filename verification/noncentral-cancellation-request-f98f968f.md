# Request-specific verification evidence: f98f968ff57b4c4ea7331b756a08868b

This Round 1 record concerns the exact failed author-comparator request for
`Submission.p04_pb_60221840b0_noncentral_cancellation`, issue #167. It does not
claim that the candidate or any later documentation commit passed comparison.

## Authenticated terminal response

On 2026-10-08 at 14:02:26 UTC, the existing terminal response was retrieved from
the configured broker's `/verify` route using the existing claim and request ID.
TLS certificate validation remained enabled. Credentials were neither persisted
nor printed. No new request ID was generated and no replacement job was requested.

- Request: `f98f968ff57b4c4ea7331b756a08868b`.
- Candidate: `113597b5f63b27240b536ed5374d8a91b640c498`.
- Reported packet digest:
  `823ab6a08dd7568ac1a1a4ca6565598ad4cd59bfdcaf111d13cadfb2d1ea34ee`.
- State: `finished`; return code: **1**; success marker absent.
- Exact response bytes: [broker response](noncentral-cancellation-request-f98f968f-response.json).
- Retrieval metadata: [metadata](noncentral-cancellation-request-f98f968f-retrieval.json).
- Response SHA-256:
  `601165b16c1aa35793e8cfebe2977db2c9c5a2cac78ee43c44468351be70ccfb`.
- Output SHA-256:
  `37a58c549d93f31e55029a5c57ee95a5e0e39651ae1f368dcb41a190c60b0529`.

The request/revision fields and the log's packet-validated node/candidate/digest
were checked against the Round 0 identities. The returned output exactly equals
the corresponding suffix of `node-comparator.log`. It fails while exporting the
challenge: `Submission.lean:10:18: Unknown constant Representation.TateResCor.cosetDecomp_apply`.

This is an authenticated retrieval of the broker's terminal response. The saved
JSON is not a signed attestation or an authenticated export of the private packet,
checker copies, or `operation.json`.

## Evidence boundary

The read-only mounted comparator entrypoint still matches the recovery-v3 wrapper
at SHA-256 `f3202ba84d3096d6e05a494f073e454e5aa82c4383a08b171832acbc28c5d9b2`.
The visible recovery-v3 sources show:

- `_recursive_lean/swarm_broker.py:293`: GET supports `/issues` and `/health`;
  POST supports `/heartbeat`, `/claim`, `/observe`, `/release`, and `/verify`.
  No artifact-export route is defined. The newer visible machine-leaves-v5 broker
  also has no export route.
- `_recursive_lean/remote_verification.py:154`: a terminal response contains only
  `request_id`, `revision`, `state`, `returncode`, and `output`, exactly the fields
  returned for this request.
- `scripts/swarm-verify-frozen-node.py:83`: the controller keeps a private
  request directory outside worker projects, with `operation.json`, `code/`,
  `prepared/`, and `output/`. The worker has neither these mounts nor a Docker
  socket. No private evidence was accessed by bypassing that boundary.
- `scripts/verify-frozen-node.py:446`: the generated child challenge imports
  `Submission`. Preparation copies the frozen proof base into the challenge and
  the candidate into a separate solution tree. The observed failure occurs in
  the former, before candidate comparison. Changing the candidate proof would
  not repair that frozen import.

These visible source files explain the available interface and failure path;
they are not evidence of the remote request's deployed checker identity.

## Required controller action

Provide a credential-free authenticated export tied to this request, candidate,
and packet digest, containing:

1. The actual `operation.json`, including service/task/specification identity,
   terminal state, packet path/digest, candidate commit, and copied checker hashes.
2. The actual packet's `prepared.json`, `evidence.json`, full source inventory,
   and generated challenge/solution sources, including `Submission.lean`,
   `Challenge.lean`, `Solution.lean`, and their dependency/configuration identities.
3. The copied `verify-frozen-node.py`, `swarm-verifier-selftest.py`, and
   `swarm-verifier-packet.py`, plus toolchain/reference inventory identities.
4. Authorized reconciliation of the missing frozen-header reference that preserves
   the frozen theorem contract, followed by a fresh exact-node comparator run.

The user was asked for the export/reconciliation location. No location or repair
was available when this record was prepared. Local pinned-reference search found
no `cosetDecomp_apply` declaration in either project definitions or mathlib; it
appears only as a reference in the frozen `Submission.lean` header. The candidate,
protected root source, dependency configuration, accepted proof, and checker were
not modified. The required comparator success remains outstanding.
