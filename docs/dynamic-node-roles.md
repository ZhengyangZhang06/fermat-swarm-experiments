# Durable operator node roles

Proof workers continue polling independently. A trusted controller may temporarily
reserve any available authorized `hoa0` through `hoa127` for verification through
the controller-local `ClaimLedger`, without permanently excluding idle fleet
capacity. This API is not exposed through worker HTTP and adds no daemon or launch.

`reserve_node(node=..., reservation_id=..., owner=..., purpose="verification")`
returns a durable reservation or `None` when unavailable. Persist an unpredictable,
unique reservation ID and stable controller identity before requesting the role.
The same exact active identity recovers the same grant after a lost response;
changed identities cannot steal it. Released IDs never become new grants.

Reservation and fresh proof claim decisions share SQLite `BEGIN IMMEDIATE`.
Reservation refuses every owned proof claim on that physical node, including
uncertain owners and other worker generations. A reserved node refuses fresh proof
claims; existing held claim recovery and immutable job definitions are preserved.
Database triggers also deny older SQL claim writers a reserved node. With no
reservations the previous scheduling behavior is unchanged. This requires the
authoritative controller-local database, never a replica or a shared NFS database.

Before spawning a verifier, the controller must hold both this node role and its
durable per-node verifier/request ownership. Node reservation alone is not proof
acceptance, Docker placement evidence, or permission for duplicate verifier jobs.
There is no expiration or heartbeat takeover. Controller crashes leave reservations
held; recovery must reconcile the exact task/container and verification request.

`release_node(node=..., reservation_id=..., owner=...)` is operator-only and requires
the exact recorded identity. The caller must first establish every associated
verifier process terminal (or establish that no process was ever launched).
Uncertain launch, missing container, timeout, or controller loss is not sufficient.
An exact repeated release is harmless and cannot free a newer reservation.
Successful release makes the node eligible for fresh proof claims; do not launch
another verifier without a new reservation ID. Active inventory is available via
`active_node_reservations()`, and released identities/timestamps remain in
`node_reservation_history` for audit. Nothing automatically cancels a proof job,
releases a proof claim, or disables proof/comparator/integration acceptance gates.

This source change and its unit tests are not a deployment. Roll out controller
support separately after review and require exact terminal evidence before reusing
any presently occupied node. Static broker `--reserve-node` exclusions continue to
apply independently until an explicitly reviewed deployment removes them; this API
does not modify their startup configuration or any job catalog.

## Provision an explicit guarded dispatcher fleet

`scripts/provision-remote-verifier-dispatchers.py --config /private/fleet.json
--unit-directory /home/ubuntu/.config/systemd/user` performs a read-only plan.
The private operator JSON has these required fields:

```json
{
  "nodes": ["hoa3", "hoa4"],
  "database": "/private/claims.sqlite",
  "workflow_root": "/private/immutable-workflow",
  "python": "/absolute/resolved/python3",
  "readiness_directory": "/private/node-readiness",
  "packet_directory": "/private/shared-verification-packets",
  "reference_cache": "/private/trusted-reference-cache",
  "reference_digest": "<original 64-character SHA-256>",
  "reference_volume": "operator-seeded-cache"
}
```

An optional `unit_prefix` defaults to `fermat-guarded-verifier`. Nodes must be an
explicit unique subset of the authorized fleet. Interpreter and workflow paths
must be resolved, absolute and free of symlink ancestors and systemd substitution
characters. All three private directories and the user unit directory must already
exist and be operator-owned mode0700. The ledger and immutable scripts must exist.

`--apply` exclusively installs missing unit files, per-node packet directories and
`<readiness_directory>/<node>.json` gates initially containing `verifier_ready:false`.
It never resets existing gates. Add `--start-new` only when authorized to start the
units newly created by this invocation. Existing units are never replaced, restarted
or started; mismatched files, loaded commands/environments, drop-ins and ambiguous
runtime identities require reconciliation. An uncertain start remains a durable
unit-file intent and is not retried automatically. Other newly installed nodes in
the same batch still receive their independent initial start attempts. A crash
between installation and start requires operator reconciliation of those exact
units, not deletion/reinstallation or a speculative restart.

Fleet units opt into `--require-bound-readiness`. A true gate must bind the actual
Docker node ID, original cache digest, named volume, immutable checker SHA-256,
diagnostic configuration hash, service specification hash and exact diagnostic
service/task IDs. The dispatcher freshly inspects the sole diagnostic task and
requires terminal exit zero on the bound physical node before dispatch. It passes
the expected physical NodeID to the adapter, which rejects hostname replacement.
False gates may remain minimal while seeding/diagnostics run. True gates are written
only by the trusted diagnostic controller after all real comparator, inventory and
isolation checks; presence of a file or an unbound boolean cannot start fleet work.

This provisioner does not seed caches, attest diagnostics, enable login startup,
change existing running deployments, release proof owners, or treat installed
units as active comparison jobs. Publish actual task/ledger observations separately.
