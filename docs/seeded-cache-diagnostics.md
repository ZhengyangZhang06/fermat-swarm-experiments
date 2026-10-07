# Automatic bounded diagnostics after trusted cache seeding

`scripts/launch-seeded-cache-diagnostics.py` observes explicit seed services and
runs the existing immutable `cache-selftest.py` wrapper only after successful
full-inventory seed receipts. It never overwrites volumes or restarts tasks.
Source tests do not authorize or establish a deployed rollout.

The operator-owned private JSON manifest supplies:

- `template_service_id` and `template_spec_sha256`: the complete reviewed existing
  diagnostic service specification, hashed as sorted compact JSON.
- `code_sha256`: absolute paths and SHA-256 for the immutable wrapper, checker,
  comparator fixture driver and seeder. `tools_directory` identifies the trusted
  read-only comparator/landrun mount; no credentials or Docker socket are mounted.
- `reference_digest`, `archive_sha256`, `inventory_entries`, `volume`: the original
  trusted cache and complete seed inventory, not worker-provided coordinates.
- `authorization_label`: the explicit Swarm node label whose value must be `true`.
- `nodes`: explicit records containing `node`, `node_id`, `seed_service`,
  `seed_service_id`, `seed_spec_sha256` and a unique `diagnostic_service` name.

Each seed must have exactly one retained task on the exact physical node, matching
the pinned specification, a consistent terminal zero result and the exact
full-inventory receipt. Diagnostics clone the pinned template with only the name
and placement constraint changed: UID1000, readonly reference/code/tools, private
tmpfs, dropped capabilities, pinned image, 12GiB, two CPUs and no restart.

Prepare private state and readiness directories outside worker projects. Dry-run
is the default. `--apply --database <existing-ledger> --watch --max-active <bound>
--readiness-directory <private-directory>` polls every30 seconds. The ledger's
node-reservation migration must already be deployed. Reservations are atomic with
new proof claims; an owned or uncertain proof job is never preempted. Intent is
fsynced before create. Missing/ambiguous submissions retain capacity and are never
blindly retried; errors on one node do not block independent bounded slots.

Readiness remains false until the exact diagnostic task terminates successfully
and logs contain exactly one each of the readonly pre-inventory receipt, pinned
checker identity, private-file/socket-denial marker, ten comparator fixtures and
matching post-inventory receipt. The readiness file binds node/NodeID, configuration
digest, cache digest/volume, checker SHA and diagnostic service/task/spec identities.
Only then is the diagnostic reservation released. A separately provisioned guarded
dispatcher observes this gate and atomically reacquires capacity; proof workers
may win that race safely. A missing gate is not readiness; accepted diagnostic
evidence is not acceptance of any campaign theorem.

Pass `--watch` only for a manifest whose full bounded parallelism is authorized.
Do not include already manually launched untracked diagnostics: reconcile those
separately, or the launcher will correctly refuse to adopt them. Keep source and
deployment evidence separate; no selftest or cache copy changes frozen contracts.
