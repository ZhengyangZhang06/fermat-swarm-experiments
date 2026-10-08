# Noncentral cancellation: controller verification handoff

This record addresses the Round 0 input-integrity review of
`Submission.p04_pb_60221840b0_noncentral_cancellation`, issue #167. It does not
change or review the mathematical proof and does not assert proof acceptance.

## Candidate and failed request

- Candidate checked in Round 0: `5d35a4405e1bcc47454399defe64dc727e3ca4ca`.
- `Submission.lean` SHA-256: `c54d318b7ff4ae1be82b8513d0d1ec5c1a6607c3e2401b5447878e919628de57`.
- Request: `4725076e12f84857a379bd8dc7d9ea67`.
- Reported packet digest: `9638836a176d1d7c5365547362adc5f0bfa2aaf6f687973e83782a6078e7d605`.
- On 2026-10-08 at 13:11:24 UTC, the same configured broker returned the existing
  terminal response over a verified TLS connection. Request, revision, and node
  identities matched. Its output exactly matches the corresponding suffix of
  the saved Round 0 comparator log. Return code: **1**; success marker absent.
- The failure is in the frozen challenge's `Submission.lean:10:18`:
  `Unknown constant Representation.TateResCor.cosetDecomp_apply`. It occurs
  before exporting or comparing the candidate.
- Authenticated response output SHA-256:
  `a6dc65e5ec8f68afde8f4903370fa962b33e17a77cf8e73b2416be4652c157f3`.

## Explanation of the wrapper discrepancy

The kernel's `/proc/self/mountinfo` identifies the comparator entrypoint as a
read-only bind mount from
`/zhengyang-workspace/fermat-swarm-runtime/flows/math-lean-flow-recovery-v3/scripts/swarm-compare.py`
onto `/runtime/flows/math-lean-flow/scripts/swarm-compare.py`. The full `/runtime`
mount and `/broker.crt` are also read-only.

The entrypoint and the available recovery-v3 wrapper are byte-identical, both
SHA-256 `f3202ba84d3096d6e05a494f073e454e5aa82c4383a08b171832acbc28c5d9b2`.
This overlay explains why Git reports a modification relative to the older
runtime commit `2e30c71a9c74a2d396820e735c64094927f9722c`.

The active broker origin is `https://10.44.0.210:8849`. The runtime deployment
notes, `docs/swarm-experiment-progress.md`, checkpoint “15:37 UTC — recovered
children executing”, record deployment of recovery-v3 to port 8849. The available
`scripts/launch-parallel-swarm.py` explicitly sets `HUMANIZE_SWARM_ENDPOINT` for
new workers and mounts the transport wrapper at the unchanged comparator path.
The wrapper retains certificate validation and checks response request/revision
identity. The mounted public certificate SHA-256 is
`07c999c93e23dffbf7827130ccd2ec567e6bc12ad20e3bc860990f483eac4313`.

These observations establish the visible routing mechanism and authenticate the
retrieved terminal response to the configured TLS endpoint. They do **not**
authenticate the private deployed verifier sources or the packet's contents.

## Outstanding controller evidence and action

The available broker implementation exposes `/issues`, `/health`, `/heartbeat`,
`/claim`, `/observe`, `/release`, and `/verify`; it exposes no artifact-retrieval
route. Its verification adapter deliberately stores receipts and packet/source
copies in a private directory outside worker projects. The worker cannot obtain
the following through its documented interface:

1. The request's `operation.json`, including service/task identity, packet digest,
   code hashes, and service specification hash.
2. The exact packet, generated `challenge` and `solution` inputs, and their
   validated inventory.
3. The copied `verify-frozen-node.py`, `swarm-verifier-packet.py`, and
   `swarm-verifier-selftest.py` actually deployed for the request.
4. Controller-authorized reconciliation of the frozen challenge's missing-name
   failure while preserving the frozen theorem contract.

Provide an authenticated export of those records, then require the exact node
comparator on the clean candidate. Neither removing a frozen attribute locally
nor replacing the checker is authorized by this implementation task. No wrapper,
checker, dependency, frozen source, or theorem proof was changed to produce this
record. The protected original contract still has SHA-256
`42953c937798c4a4ff8c5a5266936d11cb7f7836ede7175b49e6d157bd9e9551`.

The local warning-fatal candidate check passed in Round 0. Exact comparison,
kernel-comparator replay, and final transitive axiom acceptance remain unproven.
