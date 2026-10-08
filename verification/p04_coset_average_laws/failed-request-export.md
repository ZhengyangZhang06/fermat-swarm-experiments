# Controller proposal: export the failed coset-average verification

The successful-request relay cannot publish failed request
`10cb226b397b4480a3aa198129ff68fd`. `export_failed_request.py` supplies a separate
diagnostic export path for operator review and execution. It is not installed in
the controller and has not been run against private verification artifacts.

The preserved failed request is bound to:

| Field | Value |
|---|---|
| Candidate | `e99290cc6b8b3c7b9e121c2890a1eb1e624458dd` |
| Packet digest | `a9f540599491f43bd52bc74f7b986a526e02daef3de3a2714b98d3e070ddb959` |
| Node | `root.tate_index_annihilation-a1.cohomology_transfer-a1.hom_complex_transfer-a1.hom_coset_average_laws-a1` |
| Reported adapter exit | `1` |

The current candidate HEAD may later contain this proposal. The historical
request must continue to use the candidate SHA above; changing its identity is
not a retry mechanism.

## Operator execution

Review the exporter before installing it in a controller-owned location. Supply
these existing trusted paths from the controller's own registration and retained
operation, without giving workers access to the ledger or private directories:

- `controller_database`: the existing controller SQLite ledger.
- `controller_operation_root`: the exact request directory containing
  `operation.json`, `code/`, `prepared/`, and `output/result/`.
- `controller_reference_manifest`: the existing `reference.json` whose bytes
  hash to the cache digest in the operation receipt and prepared evidence.
- `controller_diagnostic_destination`: an existing, separate diagnostic
  directory under an already read-only worker mount, outside private input
  directories. For example, the controller counterpart of
  `/runtime/review-evidence/failed`. Do not use the successful relay's request
  directory or change an existing verdict/export.
- `reviewed_exporter`: the operator-reviewed copy of `export_failed_request.py`.

After setting those shell variables to actual controller paths:

```sh
python3 "$reviewed_exporter" \
  --database "$controller_database" \
  --operation-root "$controller_operation_root" \
  --reference-manifest "$controller_reference_manifest" \
  --destination "$controller_diagnostic_destination" \
  --request-id 10cb226b397b4480a3aa198129ff68fd \
  --candidate e99290cc6b8b3c7b9e121c2890a1eb1e624458dd \
  --packet-digest a9f540599491f43bd52bc74f7b986a526e02daef3de3a2714b98d3e070ddb959
```

The tool opens the ledger in read-only mode and selects only that request. It
requires a finished adapter exit of 1 and a consistent terminal failed-container
receipt. The adapter normalizes nonzero remote exit codes to 1; both original
codes are preserved in the diagnostic manifest.

It checks the private packet against the receipt digest, the result packet
against the private packet, both complete Lean source inventories and hashes,
the three executed checker/launcher copies against `code_sha256`, the checker's
identity against the packet, and the reference manifest against the recorded
cache/toolchain identities. It never executes those checker copies.

Publication creates a directory named after the request, containing the original
operation receipt, prepared packet, failed result evidence, hashed Lean sources,
three executed scripts, reference inventory, terminal log, and a projection of
the ledger identity fields. It excludes the private database, raw registration,
unlisted auxiliary files, and build caches. Generated configuration files are
captured separately when present; their new export hashes are explicitly not
described as original receipt bindings. Missing configuration is recorded as
missing, which is expected if failure preceded its generation. The reference
inventory digest is checked, but the tool does not rescan the entire reference
cache or claim that its contents passed verification.

`diagnostic-export.json` lists copied file hashes and states `acceptance: false`.
This deliberately uses a different filename from the successful relay's
`review-export.json`. Publication uses a lock and atomic directory rename, sets
files/directories to `0444`/`0555`, and refuses conflicting existing copies,
links, special files, or changed publication permissions. No private original,
terminal log, claim, or verdict is updated. No verifier or service is launched.

Return the worker-visible export path to the recursive controller/reviewer.
The operator's trusted originals and read-only publication establish provenance;
a worker-generated copy or a self-consistent hash manifest alone does not.

## Recovery after actual publication

Authenticate the real receipt, packet, source, checker, and reference bindings.
Then reconcile the reported frozen-challenge compilation failure without changing
the frozen theorem contract. Commit any authorized candidate change and run the
prescribed exact-node author comparator at a clean SHA. Only exit zero plus
`Your solution is okay!` satisfies that author gate. This diagnostic exporter and
its tests cannot accept the theorem.

The proposal targets the inspected cached Swarm adapter receipt format. It fails
closed if the retained operation differs or lacks required artifacts; it does
not reconstruct missing receipts, invent code identities, or relabel failures.

## Local transport tests

```sh
python3 -m unittest discover \
  -s verification/p04_coset_average_laws -p test_export_failed_request.py -v
```

All fixtures are synthetic. Tests cover immutable bindings, altered hashes,
failed-verdict preservation, omission of private registration/auxiliary data,
nonterminal and successful request rejection, unsafe paths, and publication
integrity. They do not run Lean, contact the controller, or authenticate the real
failed request.
