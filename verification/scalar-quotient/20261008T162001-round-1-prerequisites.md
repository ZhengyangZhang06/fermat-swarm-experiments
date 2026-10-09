# Round 1: request-bound controller prerequisites

This is a local inspection/handoff record, not a controller receipt or proof
acceptance. No Lean source, frozen input, verifier, exporter, claim, service, or
loop-state file changed. No build or comparator was rerun.

## Preserved failed operation

- Node: `root.local_norm_order-a1.dvr_determinant_length-a1.scalar_quotient_length_order-a1`.
- Candidate: `a05303131ca7e934706c6733e235855c91adf64c`.
- Request: `a8ceb2326c1b4c9b9686507ef2056ebf`.
- Reported packet digest: `056b4e1c38daba2700f2dab4cd0d5cb90713f60e29df783654b07f1e19b3b8b2`.
- Exit: **1**, building the frozen challenge; no success marker or axiom acceptance.
- Preserved log SHA-256: `a1cea71a5921dd86203d38241d5ccba9c7e5e10244d05cb3389e2ab46df4401d`.

## Newly located header-policy guidance

`/runtime/operator-header-policy-v1/policy.json` has SHA-256
`96fc18eb6b8cbdad1beec37ca318ab2cf08ac1dda8ebf7cbfe1d6d51abf32f96`.
Its p06 entry matches the frozen source commit
`956e8c600d8b95b46948ae5e37b13930b5f3d06b`, contract path,
contract SHA-256 `b004dca1496ade3fb13e18207639dd199dcb7aeb7df210061bf8c375960870bc`,
and both original/candidate header prefixes. Its line list is `[9, 10, 11]`.

`/runtime/flows/math-lean-flow-header-policy-v2/docs/frozen-header-policy.md`
(SHA-256 `1bbae28f730c6ab4ac73ccc0de7d63505d50423b782678368b1e4aa62e7368dc`)
states that the controller alone supplies the disabled-by-default policy, that
read-only guidance grants no verifier authority or committed header edits, and
that production is not enabled by the source change. Derived private inputs must
retain original/derived hashes and undergo a kernel-checked absence probe.

This identifies a documented reconciliation route; it is not evidence that the
failed operation used it or that it is currently deployed for this node. No policy
environment values were set and no alternate verifier was invoked. The node's
top-level handoff artifacts contained no matching reconciliation/authorization
entry under the recorded search.

## Missing failed-request export

`/runtime/review-evidence/a8ceb2326c1b4c9b9686507ef2056ebf` is absent. None of the
197 inspected `*/review-export.json` receipts matches the request, candidate, or
reported packet digest.

`/runtime/operator-review-evidence-f116f3cae2f8/export-review-evidence.py`
(SHA-256 `f116f3cae2f8a8397c6e0cbbb4030804133b8b1c7807fd2b9941be86721d6ec7`)
requires a finished exit-zero request, verified exit-zero operation, and verified
result evidence at lines 42–50, 66–67, 83–93 and 202–203. It cannot export the
reviewed failure while retaining exit 1. The documented relay is controller-only;
its private database and operation directories must remain inaccessible to proof
workers. The exporter was inspected, not executed or changed.

## Unresolved checker and endpoint binding

The configured local `scripts/verify-frozen-node.py` has SHA-256
`30954f9ae216d73e4fb125cae5c04795a8aae08b799dfbc779c7fd6a2f9af433` and has no
`verify_prepared` or `FROZEN_HEADER_POLICY` match. The local wrapper has SHA-256
`f3202ba84d3096d6e05a494f073e454e5aa82c4383a08b171832acbc28c5d9b2`; its diff from
runtime Git HEAD adds `HUMANIZE_SWARM_ENDPOINT` and the HTTPS check. That environment
key is present; no value or credential was printed. These local observations do
not authenticate the remote implementations or prove tampering.

## Required controller response

Provide a read-only export or authorized retrieval interface binding the original
failed request to its packet, operation receipt, every hashed challenge/solution
input, executed checker/runner/launcher/toolchain identities, and endpoint
authorization. Preserve exit 1 and the original log. Separately supply deployment
and reconciliation evidence applying the matched header policy to this node,
including its absence probe and warning-fatal inherited-placeholder treatment.
These inputs were requested from the user; the questions remain `analyze -> codex`.

The next proof action depends on those inputs. Repeating the same failing gate,
activating a worker-selected checker, editing the frozen header, or fabricating a
successful export is not an authorized repair. AC2 remains unmet.

## Round 2 drift-recovery disposition

One availability check found the exact export still absent among 199 mounted
receipts, the recorded wrapper/verifier/exporter/policy hashes unchanged, and no
reconciliation authority in the selected node's handoff. The prior request for
controller inputs remains unanswered. There is no credible worker-only route to
ADVANCED under these inputs. No source change, build, comparator retry, or new
audit bundle was made; this disposition is not proof progress. Resume only after
the controller supplies the authorized reconciliation and request-bound evidence.
