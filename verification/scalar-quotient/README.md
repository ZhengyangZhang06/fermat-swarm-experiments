# Scalar quotient verification audit

This is a local audit of existing failed request `af0506aaa3f0407db2b2eedd0fe9b38f` for candidate `dbe478749afa15b2ac4a65d23df7e64ff2899735`. It is **not** a controller receipt, replacement packet, new comparator run, or proof acceptance.

- [Exact terminal output](af0506aaa3f0407db2b2eedd0fe9b38f.log), extracted from the cited original tool record.
- [Local observations and SHA-256 hashes](af0506aaa3f0407db2b2eedd0fe9b38f.json), including the distinction between inspected runtime copies and the unverified remote checker.

## Frozen input failure

The comparator exited 1 while compiling the independently prepared challenge. Its three unknown attribute targets are `AlgebraicCurve.IsCurveOver.instNontrivialKaehler`, `AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply`, and `AlgebraicCurve.SemilinearAut.coe_torsion_smul`. Solution comparison was not reached.

The candidate preserves the 5,160-byte original contract prefix, SHA-256 `b004dca1496ade3fb13e18207639dd199dcb7aeb7df210061bf8c375960870bc`. No theorem or frozen input was changed during this audit. The exact-node source remains byte-for-byte equal to the checked candidate, SHA-256 `a39a2bb2dc7c9b7d11ae0b637caaecf1c17109793434137a6664f578a0382041`.

The pinned project import closure contains only `Def_AlgebraicCurve_PlacesOverDVR`, `Def_AlgebraicCurve_DivisorPushPull`, and `Def_AlgebraicCurve_DivisorClassGroup`. The first and third missing targets exist in other, unimported modules. Searching the pinned `project/Definitions` for `frobNormRingHom` and `frobNormRingHom_apply` returned no matches. Candidate-only edits cannot repair the separately exported frozen challenge.

## Provenance findings

1. The logged packet digest is `2e37c53ce491ed5e6e33d2004900acf335e092572da67f80bd91d155b12c619f`. The actual `prepared.json` is unavailable in the worker. A digest in terminal output does not supply the packet or establish the remote checker identity.
2. `/runtime/review-evidence/af0506aaa3f0407db2b2eedd0fe9b38f` does not exist. The mounted operator exporter, `/runtime/operator-review-evidence-3155d2fa0d3e/export-review-evidence.py`, requires both a finished exit-zero ledger request and a verified exit-zero operation. Its query and validation exclude this failed request. It also does not export checker implementation files.
3. The available broker source has only `/issues` and `/health` GET routes. `/verify` is a submission/polling interface, not a packet-download interface. No broker call or new verification was made for this audit.
4. `/runtime` and the overriding `swarm-compare.py` are mounted read-only. The wrapper differs from runtime Git commit `2e30c71a9c74a2d396820e735c64094927f9722c` by permitting `HUMANIZE_SWARM_ENDPOINT`; the environment selects port 8849. Mounted deployment notes document an additive TLS broker on that port. These observations explain an intended deployment mechanism but do not prove this request's controller authorization or identify its remote checker.
5. The existing `comparison-identity-v1.json` binds candidate `ee0110eeb25dd35b82b7086bee294c6589a4f29c`. It was preserved and was not relabeled as evidence for `dbe4787`.

## Required controller decisions

- `[blocking]`, `analyze`, owner `codex`: identify the authorized reconciliation of the frozen import/attribute inconsistency. Preserve the original contract and specify any permitted derived-input policy before another check. A worker must not silently remove attributes or manufacture declarations.
- `[blocking]`, `analyze`, owner `codex`: make this failed request's retained `prepared.json`, `operation.json`, hashed challenge/solution inputs, exact checker implementation and tool identities, and request-specific endpoint authorization available through a read-only export. Preserve the failed result; do not mark the operation verified to make it eligible for the current exporter.

The authoritative controller records remain the source of truth. This audit makes the locally available evidence reviewable and identifies why the requested remote evidence is still missing.
