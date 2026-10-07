# Optional controller-local reference cache

The default verifier still uses the original pinned reference artifacts. An
operator may opt a **new** verifier process into a private local mirror to avoid
shared-filesystem page-fault delays. This changes storage locations, not theorem
contracts, source assumptions, compiler versions, or proof acceptance gates.

## Establish provenance first

Copy the trusted pinned packages and complete Lean 4.33.1 toolchain into a new
operator-owned directory with mode `0700`, outside all worker projects:

```text
reference-root/
  packages/
  lean-4.33.1-linux/
```

Compare both copied trees byte-for-byte against the trusted originals (including
symlink targets), and verify the copied dependency checkouts are clean at the
frozen manifest's revisions. Use `git --no-optional-locks` for read-only checks.
Do not treat a manifest that hashes itself as proof of artifact provenance.

Only after those checks pass, run the verifier's operator-only
`--seal-verified-reference-cache /absolute/reference-root` command with the
registered `FERMAT_VERIFIER_PROJECT` set. This inventories every regular file's
SHA-256 and mode, plus internal symlink targets. Symlinks outside the two
inventoried trees and special files are rejected. The command creates
`reference.json` exclusively: an existing
manifest is never overwritten. Retain its printed digest in private controller
configuration, not in worker-supplied request data.

## Opt in a new, immutable verifier deployment

Supply both of these **operator-controlled** environment variables:

```text
FERMAT_VERIFIER_REFERENCE_CACHE=/absolute/reference-root
FERMAT_VERIFIER_REFERENCE_DIGEST=<controller-retained SHA-256>
```

The verifier checks the private directory, manifest digest, complete inventory,
and frozen dependency revisions before compilation. It checks the inventory
again after comparison and the axiom report, before writing verified evidence.
The cache digest is part of the immutable prepared packet and final evidence;
another cache, a missing cache, or changed artifacts cannot inherit acceptance.
Missing one configuration variable fails closed. With neither set, caching is off.

Run the real positive/negative comparator fixtures and isolation tests for a new
deployment, in addition to unit tests. Do not overwrite a running checker's code,
repoint its libraries, alter issue ownership, or reuse a proof receipt for another
candidate. A mirror or successful diagnostic is not a solved campaign theorem.

## Optional node-local remote verification

### Reserve capacity before production dispatch

New broker processes accept repeatable startup arguments such as
`--reserve-node hoa126 --reserve-node hoa127`. Reservations are validated against
the authorized `hoa0` through `hoa127` fleet and frozen for that process; the
default is empty. They deny only **new proof claims** on those physical nodes,
without editing the shared catalog or manufacturing ownership records. Existing
owners still recover their original jobs and can observe and release normally.
Reservations neither cancel work nor establish that a node is already idle.

Before enabling remote production verification, reserve its selected nodes in
**every broker generation that can grant new work**, and verify from the shared
ledger plus live task/process evidence that no active or uncertain proof claim
remains there. A `24G` proof job and a `12G` verifier exceed a `32G` node's budget;
do not rely on idle polls or stale heartbeats to establish spare capacity. Preserve
held jobs until authoritative terminal evidence permits their ordinary release.
Deploy a new immutable broker only after reconciling its owned live verification
processes; never restart a checker-owning broker merely to add a reservation.
The source option and unit tests are not a deployed capacity reservation or a
successful remote verification. Record those operational gates separately.

The remote packet adapter now supports an explicitly seeded **named Docker
volume** on the selected authorized node. The volume must contain the identical
`packages/`, `lean-4.33.1-linux/` and `reference.json` trees described above, with
the volume root owned by verifier UID/GID `1000:1000` and mode `0700`. Seeding is
an operator operation outside proof workers, using trusted staged input outside
worker-mounted directories. A volume name or seed receipt is not proof of
provenance: retain the original controller cache digest and validate the entire
copied inventory. Never reseal an untrusted copy to make its digest pass.

The reusable `scripts/seed-verifier-reference.py` takes an operator-staged plain
tar containing `reference.json`, `packages/` and `lean-4.33.1-linux/`:

```text
python3 /verifier/seed-verifier-reference.py --archive /stage/reference.tar \
  --root /reference --digest <original-controller-manifest-digest> --owner 1000
```

Run this trusted seeding operation separately from verification. Mount only the
immutable seeder code, the private completed archive read-only, and a new empty
node-local volume writable at `/reference`; do not mount credentials or Docker
sockets. Preserve relative symlinks when staging, and use tar `--hard-dereference`
if the source has hard-linked files (not `--dereference`, which changes symlinks).
Do not consume a partial archive from a live staging process.

The seeder validates every header against the pinned manifest before extracting,
checks the headers again before second-pass writes, hashes each file, and validates
the complete destination inventory. It preserves file modes and internal symlinks,
sets UID/GID 1000 and private directory permissions, and retains an exclusive seed
receipt. Failure leaves an explicitly incomplete volume; neither successful nor
partial nonempty volumes are overwritten or blindly retried. The verification
receiver still independently checks the full inventory; a seed receipt is not an
acceptance shortcut.

Configure only a **new immutable** remote adapter process with the existing
controller-local cache path and digest, plus:

```text
FERMAT_SWARM_VERIFIER_REFERENCE_VOLUME=<operator-seeded node-local volume>
FERMAT_SWARM_VERIFIER_NODE=<authorized ready active node>
FERMAT_SWARM_VERIFIER_DIRECTORY=<private shared controller packet directory>
```

The controller prepares the immutable packet using its private trusted mirror.
The remote job receives only the selected named volume, mounted read-only with
`volume-nocopy` at `/reference`, and the controller's fixed digest. No digest or
volume choice comes from the candidate or proof worker. The receiver points its
synthetic project's dependency path at `/reference/packages`; the **unchanged**
checker still validates the complete inventory before and after compilation,
the frozen dependency source revisions, exact packet/code identity, comparator,
kernel replay and transitive axioms. Cache-backed jobs have a `12G` memory limit;
the uncached path retains `6G`. Both retain the isolated unprivileged sandbox,
socket denial, two-CPU limit and no credentials/control sockets.

The adapter resolves the requested hostname to its actual Docker NodeID before
submitting work, records it with the volume and digest in the private operation
receipt, and refuses task placement on another node. The node must already be
ready, active and explicitly labeled for this experiment; it is never undrained.
Unassigned pending tasks are observed without being mistaken for terminal work.
Service/task identity and specification remain bound throughout observation;
exit75 still requires reconciliation, not timeout-based takeover. Remote success
also requires exact returned evidence matching the controller's original packet.

### Durable remote dispatch capacity

The controller dispatcher must be invoked with both `--remote-node hoa127` and
`--remote-directory /operator/private/packets` for a remote adapter. The ordinary
local dispatcher defaults remain unchanged; remote environment variables without
these flags are rejected. The packet directory must be private, operator-owned,
outside worker projects and free of symlink ancestors. Environment coordinates
must match the flags exactly.

The authoritative ledger's parent contains `remote-verifier-slots/<hostname>.lock`
and a durable JSON slot. Every controller for that node and ledger uses this fixed
location even when supplied another packet directory. A process lock prevents two
dispatchers from operating the same physical node concurrently. Before launching
the exact queued request, the dispatcher fsyncs its request identity, ledger request
hash, packet directory and Docker NodeID. The slot persists across controller loss;
it must not be deleted or relocated to bypass an uncertain remote job.

The remote path runs one verification synchronously and only advances after the
ledger is finished and the adapter has a matching verified/terminal receipt, with
a fresh inspection of the exact service specification, sole task and physical node
confirming terminal container exit. An explicit pre-submit preparation failure may
also free the slot, but only with no submission identifiers in its receipt. Exit75,
a live task, missing receipts, changed identities, lost observations and controller
loss retain the slot and stop that dispatcher; they never start the next request.
An idle record preserves the last completed identity instead of deleting history.

Before execution, the dispatcher also obtains an operator-only ledger node-role
reservation, atomic with proof claims. A node already owned by a proof job is not
preempted. The stable owner and fresh per-cycle reservation ID are persisted before
reservation; no worker supplies them. The role remains reserved across controller
loss and uncertainty, and across consecutive queued checks. Only a known-idle slot
plus an empty eligible verification queue releases its exact role reservation.
The next cycle uses a new reservation ID, allowing the node to return to proof work
between verification batches without permanent static reservation of the fleet.

Before **first** activation on a node, operators still must reconcile any earlier
manual or legacy remote work and establish the capacity reservation described above.
The slot only reconciles its own known request; it does not adopt historical jobs,
cancel tasks, release proof claims, or infer inactivity from age. All cooperating
dispatchers must use the same authoritative ledger and immutable deployment.

For a package-backed transport canary, invoke the standalone
`scripts/test-swarm-verifier-roundtrip.py` with both `--mathlib-fixture` and
`--dependency-manifest /operator/trusted/lake-manifest.json`, in addition to its
ordinary adapter/directory/node arguments. Select the original trusted pinned
manifest, never one supplied by a proof worker. The script validates it before
creating fixture directories and freezes its exact bytes into both disposable
projects. Both challenge and candidate import `Mathlib.Data.Nat.Basic`, exercising
cached compiled imports and the unchanged verifier's pinned dependency-source
checks. The original positive `True` and negative `False → False` cases remain;
the negative case additionally requires the comparator's explicit statement-
mismatch diagnostic for `toy`, not merely an exit code from an unrelated failure.
The default without either option retains the cheap no-package fixtures. Neither
fixture creates campaign claims or counts as a proved campaign theorem.

This source support does **not** seed any node, enable extra dispatchers, restart
existing checkers or attest a campaign proof. A cache-enabled remote canary with
real positive/negative comparator fixtures, private-file/socket denial and exact
task/packet/cache evidence is still required before production activation. Deploy
additively only after those checks, retaining old jobs and their immutable code.

### Pilot validation checkpoint: 2026-10-07 17:03 UTC

The authorized `hoa127` pilot now has a separately seeded named reference volume.
The seed task completed with exit zero and verified all 173,439 inventory entries
against the original operator-retained digest. The unchanged checker then passed
all ten real comparator fixtures, private-file/socket denial, UID/GID 1000 and
mode-0700 checks, a read-only-volume check, and full inventory checks before and
after execution. The diagnostic task completed with exit zero. These fixtures
are infrastructure evidence, not campaign theorem solutions.

The recovery broker now runs immutable reservation source `eb552d2`, reserves
`hoa127` from new proof claims, and still routes new proof jobs through the
integrity-review archive. Other broker generations have intake disabled. Its
authenticated health check passed; all 71 prior job definitions and all four
running checker process identities were preserved. The reserved node had no
active proof claim. The full reservation suite passed 395 tests (one optional
skip), and the package-backed roundtrip additions passed eight targeted tests.
The workflow branch contains both changes through `044c2ae` after a transient
GitHub push failure recovered.

The package-backed exact-packet roundtrip is currently running under the durable
`fermat-cache-roundtrip-20261007.service` controller. It must accept the original
positive fixture, reject the changed statement with the actual comparator
diagnostic, and return matching packet/task/cache evidence. Production dispatch
is still disabled pending those terminal results. Do not infer completion or
start another canary from elapsed time; reconcile this exact controller and its
recorded task identities first.

## Controller pilot (2026-10-07)

An additive pilot uses a private Git archive of workflow revision `7c0cdf0` at
`/var/tmp/fermat-cached-verifier-pilot.EcQSVm`. Its checker SHA-256 is
`17360b2ac18e997034d13017a50a6bfe476c7100a5d8ef0569dbc3ac8fb87197`, identical
to the version tested with the sealed local mirror. Private-file and Unix-socket
denial were also checked using this deployed checker and its actual sandbox.

The user timer `fermat-cached-verifier-pilot-20261007.timer` invokes the existing
dispatcher with `--once` every 30 seconds after the previous invocation finishes.
The service is `fermat-cached-verifier-pilot-20261007.service`. It has at most one
verification in flight, uses `recover_existing=False`, respects catalogue
readiness, and atomically claims only queued requests with live issue claims.
It cannot register requests or restart running/uncertain requests. The original
broker, runtime code and running checks were not modified or restarted.

Stopping the timer prevents future pilot polls without interrupting an active
check. Do not stop its service while it owns a live verification: wait for the
specific request's terminal result. A successful idle poll is not verification
evidence, and no performance improvement is claimed until actually measured.

At 13:21:47 UTC the pilot claimed its first real request,
`190da91e9f554b0d9ec6ece90fa5ad0d`, for P02 issue51 candidate `411a83a`.
The timer was then stopped to bound evaluation to this one request; its service
and checker were running at that historical checkpoint. Reconcile the current
receipt before enabling further pilot polls; the observation above does not
establish their present liveness. Ordinary broker work was not interrupted.
