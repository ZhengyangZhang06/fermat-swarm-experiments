# Round 1 Summary

## Outcome

**AC2 remains blocked by controller-only prerequisites.** No authenticated bundle for failed request `3c23c64cf708425894ed055e65e97df9` is mounted, and the existing exporter cannot export a failed operation. A newly staged frozen-header policy matches p04's original contract, but its activation in the production verification path is not established. No Lean code or frozen input changed, and no new comparator request was submitted.

Re-read the original v6 plan, tracker, Round 0 summary, and latest integrity review before writing `round-1-contract.md`. The round retained one objective: audit authentic failed-request inputs and obtain an authorized reconciliation of the selected node's verification blocker. The immutable tracker section is unchanged.

## Theorems and reviewer findings

`theorems`: [`Submission.p04_tz91_invariant_restriction_norm_range`] only, tracked by issue #134. Dependencies remain empty. The preceding reviewer passed the local Git/frozen-input checks; no mathematical re-review or new helper was requested or performed.

Mainline gap: the author comparator for candidate `b0ad04bde368623b3856a4a8c4bc5a22cbb80ac0` failed before candidate comparison. Blocking side issues: unavailable authentic failed-operation inputs and unresolved production frozen-header reconciliation. No queued code issues were found. Task tools remain unavailable; the tracker maintains `[mainline]`, `coding -> claude`, and task status.

## Evidence investigation

1. `/runtime/review-evidence/3c23c64cf708425894ed055e65e97df9` is absent. An `rg --files --hidden` search of mounted evidence and `/mnt/data`, bounded to prepared/evidence/export/operation JSON and excluding Git, dependency, reference-snapshot, and node_modules directories, found 588 metadata files. Parsing their values found no exact request, candidate, or reported packet digest match; no read/parse error occurred. See `round-1-evidence-search.json`.
2. `/runtime/operator-review-evidence-f116f3cae2f8/export-review-evidence.py:46` rejects nonzero and non-verified operations; line 203 selects only `state='finished' AND returncode=0`. The documented export interface in `/runtime/flows/math-lean-flow-header-policy-v1/docs/review-evidence-export.md` confirms these restrictions. Running the unmodified exporter cannot retrieve this failed request. Its private database and operation storage are not mounted here.
3. The inspected runner `/runtime/flows/math-lean-flow-header-policy-v1/scripts/swarm-verify-frozen-node.py:149` retains `operation.json`, copies and hashes executed checker files at lines 154–160, records the prepared packet at 170–171, and returns on terminal failure at 225–226 before success validation. These are protocol findings, not a claim about the checker actually executed for the old request. The current `/runtime/flows/math-lean-flow/scripts/verify-frozen-node.py` still lacks `verify_prepared`, confirming it cannot substitute for that executed checker.
4. The inspected broker's GET routes expose only `/issues` and `/health`, with no input-download route. `/input`, `/output`, `/reference`, `/verifier`, `/controller`, and `/var/run/docker.sock` are absent. No speculative API calls, private-state edits, or service changes were made.
5. Newly installed read-only archive `/runtime/flows/math-lean-flow-header-policy-v1` matches all 131 hashes in its `DEPLOYMENT.json`, recording commit `6d906c02a82427d7213acd18fffcd522e0696aef`. Its verifier hash is `7f49056d55f7f0732554c94e7eb654634a11a8e0396fa7c552b01785a335dac9`. See `round-1-runtime-audit.json`. This establishes the mounted archive's identity, not the failed request's executed checker or active production deployment.
6. `/runtime/operator-header-policy-v1/policy.json` has digest `96fc18eb6b8cbdad1beec37ca318ab2cf08ac1dda8ebf7cbfe1d6d51abf32f96`. Its p04 source revision, root name, complete contract hash `42953c937798c4a4ff8c5a5266936d11cb7f7836ede7175b49e6d157bd9e9551`, and header prefix match the frozen source; the sole selected omission is line 10. The policy operates only on private compiler copies, retains reversible original/derived hashes, and checks absence of every omitted target while preserving exact comparator, kernel, dependency, and axiom gates. See `round-1-header-policy-audit.json`.
7. `/runtime/flows/math-lean-flow-header-policy-v1/docs/frozen-header-policy.md` records authorization for that narrow policy but says source installation does not enable production; rollout requires successful preflight and an immutable checker transition. Neither this worker nor the project's configuration has the policy guidance fields set. The guidance explicitly grants no verifier authority and permits no committed frozen-header edits. No deployment receipt was available, so the worker did not enable the policy or invoke an alternative checker.
8. An asynchronous request asked for the authenticated bundle and reconciliation path. None was supplied during the round. `round-1-controller-handoff.md` now specifies the exact original artifacts and bindings needed, distinguishes the staged policy from production rollout, and retains the old operation's failed status.

## Validation and changes

The local tree began at clean `b0ad04bde368623b3856a4a8c4bc5a22cbb80ac0`. Source diffs from that candidate remain empty. The user-requested read-only simplifier independently confirmed no Lean changes and no applicable optimization. No new build, proof, or acceptance claim is made: Round 0's full warning-fatal build and comparator remain failed, while its child type/axiom diagnostic and dependency-source checks remain separately recorded.

The failed request's reported packet digest remains `5d6f827a86b081735a0577d66517d8ce7565f3af15d87a0e4dd8248d785e69dc`. Terminal output is not promoted to authenticated input evidence. Repeating the unchanged comparator would not retrieve that operation's missing artifacts, and no active reconciliation was established to justify another proof run.

This round commits only the requested tracker/contract/summary, precise controller handoff, and three nonsecret audit reports, explicitly staging those files despite `.humanize/` being ignored. Automatic loop-state files remain untouched. The resulting documentation commit is not a comparator-verified candidate; the last author request is bound to `b0ad04b` and failed.

## Reference use

`reference_use` contains exactly one entry:

- **source: local-project**. Re-read the frozen problem and manifest at `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8/manifest.json`, which pins project `2475a3790d7ba0c3b10be8086001b154a45be597` and mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`. Ran `rg -n 'normBar|normToInvariants|TateResCor|cosetDecomp_apply'` on snapshot `project/Definitions/Def_GroupCohomology_TateCohomology.lean` and inspected lines 20–48. The file defines normToInvariants, normBar, and normBar_mk at lines 30–43; no TateResCor or cosetDecomp_apply match occurs. No new library declaration was reused. Round 0's byte-compatibility, clean nine-dependency pins, and `[propext, Classical.choice, Quot.sound]` diagnostic remain evidence for the unchanged source, not comparator acceptance. No network search or alternative problem acquisition occurred.

## Remaining work

T3 warning-fatal validation, T4 successful author comparator, and T6 authentic-input audit remain blocked. T7 completes this round's evidence and handoff with reviewer verification pending. The controller must expose a diagnostic bundle for the original failed request and establish an authorized active verification path that preserves the frozen contract, including the selected child's warning-fatal boundary. Once supplied, inspect those bytes and run only the exact selected-node author comparator at a clean committed candidate.

The outer independent comparator review, wiki publication, PR lifecycle, and DAG proved transition remain controller tasks. No DAG, claim, issue, verifier, policy, dependency, frozen source, accepted proof, or automatic loop state was changed.

## BitLesson Delta
- Action: none
- Lesson ID(s): NONE
- Notes: The empty BitLesson file was reread before the evidence and handoff tasks; all selections were NONE. No repaired failure warranted adding a lesson.
