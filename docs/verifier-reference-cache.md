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

## Optional node-local remote verification (source support; not deployed)

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

This source support does **not** seed any node, enable extra dispatchers, restart
existing checkers or attest a campaign proof. A cache-enabled remote canary with
real positive/negative comparator fixtures, private-file/socket denial and exact
task/packet/cache evidence is still required before production activation. Deploy
additively only after those checks, retaining old jobs and their immutable code.

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
and checker remain running. Assess that exact receipt before enabling further
pilot polls. The ordinary broker continues serving other requests unchanged.
