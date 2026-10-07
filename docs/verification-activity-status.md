# Saved stage versus observed verification activity

The durable DAG's `comparing` stage is recorded before a verification request is
queued. It is not evidence that a comparator is executing. Fleet observers should
use `_recursive_lean.verification_status.observe_verifications` on the controller,
then `attach_verification_activity` on allowlisted per-problem DAG records.
The campaign publisher is an explicit deployment adapter; the helper is reusable
and has no hard-coded repository, database path, authentication or fleet size.

The helper opens SQLite with `mode=ro` and `query_only`, reads one joined snapshot,
and never changes claims or jobs. Matching requires repository, project, issue,
theorem node and an owned claim. Unfinished checks of released owners remain in
aggregate counts, but are not attached to a new claim. Multiple requests and
candidate revisions are retained as counts, never collapsed into a passing
"latest" result. Finished checks do not update proof acceptance or merge fields.

Presentation distinguishes:

- `waiting-verification`: a queued request, not an executing checker.
- `verification-running`: a live controller PID with matching start ticks. This
  includes a remote adapter preparing/waiting for its task, not necessarily Lean
  compilation. It is a point-in-time observation, not a liveness guarantee.
- `starting`: a durable spawning record with no confirmed running handle.
- `needs-reconciliation`: uncertain state, missing/reused/zombie/inaccessible
  recorded process, or conflicting owned attempts. Never automatic takeover.
- `no-active-check`: no current unfinished request observed, regardless of the
  last saved DAG stage. It does not mean the theorem is ready or proved.
- `unavailable`: missing, unreadable, malformed or stale evidence. Never report
  an empty successful queue based on a collection failure.

Preserve `status` and worker observations; `saved_status` and
`verification_activity` are additive display fields. Public output contains no
request bodies, candidate paths, raw logs, process IDs, claim tokens or credentials.
Aggregate counts are requests, not theorem counts. Display observation time and
expire live labels after three minutes, including when refresh requests fail.

Source tests are not deployment evidence. Deploy the updated observer from an
immutable workflow revision and publish the separate website change only after
independent review, tests and a read-only live collection check.
