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
