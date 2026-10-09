# Existing root verification evidence

This bundle exposes the already completed controller verification requested in Round 0. It does not run another comparator or supply independent proof acceptance. All controller JSON files are copied byte-for-byte; the audit helper and this explanation are author-written.

| Identity | Recorded value |
|---|---|
| Request | `5e4f5b622c094d1ba9ffe7cbe598dd1c` |
| Verified candidate | `e03397c0ce0433baff5ac5cc10567afbbabd7667` |
| Canonical packet SHA-256 | `5650377b5c3128581f8dfc57783aea07bedb52608ee5b0a5e49df602eaed0ad9` |
| Broker completion | `state = finished`, `returncode = 0` |
| Root | `HeckeEis.eichlerShimuraMap_injective` |
| Checked declarations | Root plus all 56 retained children |
| Original root contract revision | `1f74c284b125d4c45f527f2d621597fcf1e103a9` |
| Controller's challenge-source base | `0459b94175dee79ea28976125254a32de1e93fe6` |
| Verifier source SHA-256 | `67b22fb3424e16a2383043abc68496b521ef45f8536a37ade814fe874d144c1d` |
| Reference-cache digest | `d27914ad50fe438f1ed6f8b512f5ae0dc19950e5527c6afdefba6b9f6a85f5a6` |
| Lean toolchain | `v4.33.1` |
| Remote service | `mbqfed87jscimi4sk50ywy5n7` |
| Remote task | `ma8coh0ag9xbkxyhp3dvy68ze` |

The challenge-source base is the value actually recorded in the controller packet. It is distinct from the author's Round 0 starting worktree revision `8a9b9dc350dca723a3351817b20df5d6ed87e8d7`. The generated root challenge begins with the exact original frozen contract; its remaining declarations are the retained child contracts. The audit checks all 218 nongenerated source inputs against their recorded Git revisions rather than substituting the author's starting revision.

## Authoritative origin

The private result path printed in the original log is not mounted in the worker. The controller later exported the existing successful result to the read-only directory:

`/runtime/review-evidence-extra-v3/5e4f5b622c094d1ba9ffe7cbe598dd1c`

The fresh retrieval of the **same existing request** from the authenticated TLS broker returned `finished`, return code zero, and an explicit `Controller review-artifact export` line naming that directory. No new request identifier was generated. The broker's durable lookup preserves the existing finished result; its execution path starts only queued requests. The retrieved raw response is [broker-result.json](broker-result.json).

The controller export is independently readable at its original mount. Its publisher source, `/runtime/operator-review-evidence-f116f3cae2f8/export-review-evidence.py`, admits only matching successful terminal ledger records and verified remote operation receipts, checks the packet/result relationship and every source hash, and publishes the input bytes with a receipt. The receipt explicitly says the private checker evidence remains authoritative. The author did not invoke or modify that publisher, the controller ledger, operation receipt, or verdict.

## Contents and bindings

- [prepared.json](prepared.json): original prepared packet, containing the 220 source hashes, frozen dependency manifest, 57 theorem names, exact source revisions, permitted axioms, verifier identity and reference-cache identity. Its canonical JSON SHA-256 equals the packet digest above. Its raw file SHA-256 differs because the file contains formatting; the controller export records that raw hash separately.
- [evidence.json](evidence.json): original completed result. It equals the packet's embedded evidence with only `status` changed from `checking` to `verified` by the controller.
- [review-export.json](review-export.json): original controller export receipt tying the request, candidate, packet, service and task to the hashes of all 222 exported files (220 Lean inputs plus the prepared and completed JSON files).
- [inputs.tar.gz](inputs.tar.gz): author-created lossless container for all 220 original Lean input files. The contents retain their original names and bytes, all checked against both controller hash lists. The archive keeps challenge placeholders and historical source copies outside the active Lean source tree. It introduces no Lean declarations into the candidate.
- [checker-source.py.txt](checker-source.py.txt): a byte-identical copy of the installed checker source whose SHA-256 equals the checker identity recorded in the packet. The matching installed file is `/runtime/flows/math-lean-flow-applied-report-v1/scripts/verify-frozen-node.py`. It is included for inspection, not execution. Its `validate_prepared` binds the packet, source hashes, its own source hash and reference-cache digest. Its `verify_prepared` performs isolated comparison, axiom reporting, and before/after reference-inventory checks. The reference-cache digest identifies the controller's deployed tool/dependency inventory; this bundle does not claim to contain the remote binaries themselves.
- [broker-result.json](broker-result.json): raw finished response, including the numeric process return code, success marker, matching `packet-validated`/`packet-verified` records, axiom output, and controller export location.
- [verify-evidence.py](verify-evidence.py): offline integrity audit. It reads the archive without extracting it, verifies all recorded source hashes, compares the nongenerated sources with Git, checks the original root contract and generated solution entrypoint, and authenticates the packet/result/request identities and return code. It never starts Lean, the comparator, a network request, or a controller job.

Run from any directory with the repository and its existing Git history available:

```sh
python3 proofs/github/20261007t081612z-177ebb5a0d/root-verification/verify-evidence.py
```

Successful output reports 220 hashed source files, 218 exact Git source matches, 57 checked declaration identities, return code zero, and the recorded checker/cache digests. This is an integrity audit of existing controller evidence, not a new mathematical verification.

## Handoff boundary

The verified theorem candidate remains `e03397c0ce0433baff5ac5cc10567afbbabd7667`. A later evidence-only commit is not represented as the revision checked by that earlier comparator. `Submission.lean`, all frozen inputs, all dependency pins, and the final prose blob `131917b3299bb53ed2c6dd05647877198223a7a3` remain unchanged. Independent final-prose review, fresh reviewer verification, publication, and DAG acceptance remain with the recursive controller.
