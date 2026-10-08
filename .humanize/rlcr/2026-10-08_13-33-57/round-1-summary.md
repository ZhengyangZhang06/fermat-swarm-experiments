# Round 1 Summary

## Outcome

**AC2 remains blocked.** The requested failed-operation inputs are not available through the worker's mounted evidence, and both available controller export implementations admit only successful verified requests. No controller-authenticated bundle or authorized frozen-context reconciliation was supplied during this round. The implementation remains unaccepted; another unchanged comparator run would not supply the missing existing-request artifacts or repair its independent challenge.

Re-read the original plan, immutable tracker goal/ACs, Round 0 summary, and the latest integrity review before writing the Round 1 contract. The contract retains one objective: resolve this exact node's comparator blocker through authentic inputs and authorized reconciliation. No Lean, dependency, frozen problem/proof, comparator, cluster service, DAG, or loop-state file was edited.

## Theorems

- `Submission.p04_tz91_invariant_restriction_norm_range` only, issue #134. No new named theorem or helper was added.

## Evidence investigation

1. `/runtime/review-evidence/20cace6a340046d5ad4d0884dd3a16f9` remains absent. A bounded `rg --files --hidden` search under `/runtime` and `/mnt/data`, excluding Git, dependencies, local reference snapshots, and node_modules, found 266 relevant metadata artifacts, including 133 `prepared.json` packets. Parsing only identity fields found no matching request or candidate/node pair. No unreadable file occurred. Results are retained in `round-1-evidence-search.json`.
2. The selected node's `comparison-identity-v1/v2/v3.json` files contain local commit/tree/history/input identity packets. Their digests are respectively `3a3fa0c5fe6013053ec836e1e7b6a9a15d6b28d03c6a4acb9cdae2b9d5f48492`, `7cad14bf291a90ac91d3d134c67dde6a40ac7afb6b239d5e34517f4544a94901`, and `65f2b93c4b87e1b38d5380ec9b83b8dc3e0b19922833fbbb613020c8dd2edc6e`. They are not the reported remote prepared packet `9fb2a32a215c2639092ad79ad997486560998f5f62cd264695db23d77428849f`, and cannot replace it.
3. `/runtime/operator-review-evidence-f116f3cae2f8/export-review-evidence.py:203` and `/runtime/operator-review-evidence-3155d2fa0d3e/export-review-evidence.py:153` select only `state='finished' AND returncode=0`. Both scripts' lines 46–48 reject nonzero results and operations without verified receipts. Their input-copy validation also expects verified evidence. Neither unmodified implementation can publish this failed request. Their active deployment identity was not established; no claim is made that these are the precise exporter copies currently deployed.
4. `/runtime/flows/math-lean-flow-missing-candidate-v1/scripts/swarm-verify-frozen-node.py:141-171` documents controller-private per-request storage of `operation.json`, copied checker files, prepared packet digest, and candidate identity. Lines 216–227 retain terminal status and return on a nonzero result before the success-only evidence checks. These are protocol findings, not an authenticated identity of the executed checker.
5. `/runtime/flows/math-lean-flow/_recursive_lean/swarm_broker.py:253-279` exposes GET `/issues` and `/health`, and the claim/observation/verification POST routes; no artifact-download route exists in this inspected source. No speculative API request or verification job was submitted. The verifier-only paths `/input`, `/output`, `/reference`, `/verifier`, `/controller`, and Docker socket paths are absent in this worker.
6. An asynchronous request asked for the readable authenticated bundle location and authorized reconciliation. The exact required artifacts and binding are now specified in `round-1-controller-handoff.md`; the handoff is explicitly an artifact request, not fabricated evidence or an approval receipt.

## Validation and candidate identity

The existing failed request remains `20cace6a340046d5ad4d0884dd3a16f9`, candidate `b92f7f6a88b239299fb61797260421ce450a2272`, exit 1, without `Your solution is okay!`. Round 0's full-file warning-fatal check failed on the missing frozen attribute and inherited root sorry; its isolated exact-child diagnostic passed with only propext, Classical.choice, and Quot.sound. These are historical results, not fresh acceptance for this round.

At the start of this round and after the evidence investigation, tracked source diffs from `b92f7f6a88b239299fb61797260421ce450a2272` were empty and its worktree was clean. The Tate definition file still matches the pinned snapshot byte-for-byte, SHA-256 `e9fe2119399354d446f25bad2407a330ae5c5eee0cd6ef3d1a2c131364724b24`. The requested simplifier check independently confirmed no tracked source changes and no optimization needed. No new code was written, and no unrelated theorem was checked.

This round commits only the requested documentation and nonsecret evidence-location report. Such a documentation commit does not constitute a successful comparator run at its new SHA. No repeated Lean build or comparator was warranted by a source change, new input, or repaired environment.

## Reference use

`reference_use` contains exactly one entry:

- **source: local-project**. Snapshot `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/local-references/3ffca5d1a6f048c8`, with manifest pins project `2475a3790d7ba0c3b10be8086001b154a45be597` and mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`. Re-read the frozen problem. Ran `rg -n 'normBar|normToInvariants|TateResCor|cosetDecomp_apply'` on the snapshot's `project/Definitions/Def_GroupCohomology_TateCohomology.lean` and inspected lines 1–52. It defines normToInvariants, normBar, and normBar_mk at lines 30–43; no TateResCor or cosetDecomp_apply match exists in that file. Its bytes still match the worktree. No new declaration was reused or new axiom-acceptance claim made; the Round 0 clean dependency and transitive-axiom evidence remains recorded separately. No network search or alternative problem acquisition occurred.

## Task status and remaining work

T3 warning-fatal validation, T4 exact-node acceptance, and T6 authentic-input audit remain blocked, with the investigated access limitation recorded. T7 completed this round's contract, tracker, artifact request, evidence-location report, and summary; reviewer verification remains pending. The tracker's immutable section is unchanged. TaskCreate/TaskUpdate/TaskList remain unavailable, so the tracker retains task lifecycle and coding/claude routing. Only the five requested round documents/report files are explicitly staged despite the broad .humanize ignore rule; automatic loop-state files remain untracked and unchanged.

The controller must expose the retained failed operation's authentic inputs and checker identities without relabeling it successful, then reconcile the frozen challenge and warning-fatal boundary. Only then can an exact clean candidate pass the required author comparator. Independent reviewer rerun, wiki publication, PR integration, issue closure, and the DAG proved transition remain outer-controller tasks.

## BitLesson Delta

- Action: none
- Lesson ID(s): NONE
- Notes: the knowledge base is empty and was reread before the evidence and handoff tasks. The failure-export limitation was inspected but not repaired, so no resolved-failure lesson was added.
