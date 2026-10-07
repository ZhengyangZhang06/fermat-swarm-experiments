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

The current remote packet launcher does not automatically transport a local
cache or its operator configuration. A cache-bound packet must not be sent to an
unconfigured receiver: the cache-binding check rejects it. This option is for
explicit controller-local deployments until remote cache transport is separately
implemented and verified.

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
