# Goal Tracker

<!--
This file tracks the ultimate goal, acceptance criteria, and plan evolution.
It prevents goal drift by maintaining a persistent anchor across all rounds.

RULES:
- IMMUTABLE SECTION: Do not modify after initialization
- MUTABLE SECTION: Update each round, but document all changes
- Every task must be in one of: Active, Completed, or Deferred
- Deferred items require explicit justification
-->

## IMMUTABLE SECTION
<!-- Do not modify after initialization -->

### Ultimate Goal
Implement only `Submission.f036cc6b1f_fd_norm_bound` with its exact frozen child type and accepted parent-supplied proof, producing a warning-clean, committed, clean-worktree candidate that passes the configured selected-node comparator, then return to the recursive controller.

Source plan: /mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/nodes/root-gamma0-finite-dimensional-a1-coset-norm-bound-a1/rlcr-plan-v3.md

### Acceptance Criteria
<!-- Each criterion must be independently verifiable -->
<!-- The builder must extract or define these in Round 0 -->

1. **AC1 — Exact safe implementation:** `Submission.lean` proves precisely the selected frozen declaration using the accepted proof and pinned upstream infrastructure; no additional named helpers, new axioms, placeholders, unsafe mechanisms, protected-file edits, or changed hypotheses/conclusion. Record local-project provenance and compatibility checks.
2. **AC2 — Reproducible candidate validation:** Warning-fatal Lean checks, complete source-diff inspection, and transitive axiom inspection pass; the committed candidate has a clean worktree and its exact selected-node comparator exits zero with `Your solution is okay!`.
3. **AC3 — Scoped handoff:** Round tracker, contract, and summary document actual evidence, reference_use with exactly one local-project entry, BitLesson selection/delta, and pending independent review. Return without running root/sibling comparators or performing outer-controller publication/transitions.

---

## MUTABLE SECTION
<!-- Update each round with justification for changes -->

### Plan Version: 1 (Updated: Round 1; mathematical plan unchanged)

#### Plan Evolution Log
<!-- Document any changes to the plan with justification -->
| Round | Change | Reason | Impact on AC |
|-------|--------|--------|--------------|
| 0 | Initialize selected-node implementation plan | User-supplied authoritative child contract | AC1–AC3 |
| 0 | Audit the already-implemented candidate instead of adding a duplicate proof | The initial clean HEAD is 11b450d and already contains the exact selected declaration; prior evidence does not establish acceptance | Same AC1–AC3; no decomposition or contract change |
| 0 review | Keep full-context validation and successful comparison active but blocked; separate them from completed diagnostic work | AC2 is a mandatory completion gate, not optional future work. Request 651de54b4e4b4e739e83e4cd79b900b3 is now terminal with exit 1. Controller-only repair is justified, but does not satisfy AC2 | AC2 remains unmet; no change to the acceptance boundary |
| 0 review | Expand the context defect to all 15 attribute targets; move the mitigated shell-launcher problem to queued issues | Independent individual #check commands fail for every name in Submission.lean:9–10. Required shell and Lean commands succeeded using escalation | Accurate repair scope; no protected-source change |
| 0 review | Verify the source audit and scoped records against the current documentation commit | HEAD advanced to 74d39ef only after the failed comparator became terminal; its three changed files are the requested round records and the Lean source is unchanged | AC1 implementation evidence and AC3 reporting verified; no comparator acceptance transferred between SHAs |
| 1 | Execute the gated recovery sequence and preserve reviewer tracker corrections | The reviewer established that all 15 attribute targets are unavailable, not only the two initially reported names. Controller resolution must precede T6/T7 | AC2 remains mandatory active blocked work; AC3 requires the precise controller handoff |

#### Active Tasks
<!-- Mainline tasks only: each task must directly advance the current round objective and carry routing metadata -->
| Task | Target AC | Status | Tag | Owner | Notes |
|------|-----------|--------|-----|-------|-------|
| [mainline] T6 Complete warning-fatal selected-node validation with the frozen context intact | AC2 | blocked | coding | claude | BitLesson: NONE. Resume only after the controller supplies a contract-preserving resolution of the missing-attribute import gate. Require every attribute target to resolve and CheckNode.lean to exit 0. Preserve the selected type, accepted prose, imports, attribute commands, pinned dependencies, and proof base under current authorization. |
| [mainline] T7 Commit the final candidate and obtain successful exact-node comparator evidence for that SHA | AC2 | blocked by T6 | coding | claude | BitLesson: NONE. 651de54b4e4b4e739e83e4cd79b900b3 finished with exit 1 for 11b450d. Neither reviewed 74d39ef nor subsequent documentation commits have a passing comparison. Include all required tracked records before freezing the final SHA, require a clean worktree, then run the exact plan command once the context gate is resolved. Require exit 0 and the success marker before handoff. |

### Blocking Side Issues
<!-- Only issues that directly block current mainline progress belong here -->
| Issue | Discovered Round | Blocking AC | Resolution Path |
|-------|-----------------|-------------|-----------------|
| [blocking] Frozen import context cannot resolve any of its 15 attribute targets | 0; full extent verified in review | AC2 | The two grouped attribute commands report only their first missing name. Independent CheckFrozenAttributes.lean reports 15 unknown identifiers/constants. Controller must resolve the protected context under the frozen-contract constraints before this child can pass. Candidate-only edits cannot repair the separately copied challenge. Evidence: validation/reviewer/CheckFrozenAttributes.lean and independent-check-results.json. |
| [blocking] Exact-node comparator fails compiling the frozen challenge | 0 | AC2 | Request 651de54b4e4b4e739e83e4cd79b900b3 finished with exit 1, observed at 2026-10-07T15:15:30Z, before candidate comparison. Evidence: validation/current-comparator-status.json and current-comparator-output.log:98–104. Preserve this terminal result; do not retry unchanged inputs. Resume T7 after T6 and controller repair. |

### Queued Side Issues
<!-- Non-blocking issues stay queued and must NOT replace the round objective -->
| Issue | Discovered Round | Why Not Blocking | Revisit Trigger |
|-------|-----------------|------------------|-----------------|
| [queued] Shell sandbox launcher lacks bubblewrap | 0 | Required reads and Lean checks succeeded using tool escalation; this is a mitigated tooling issue, not the remaining proof blocker | Escalated access becomes unavailable or infrastructure maintenance is authorized |
| [queued] TaskCreate/TaskUpdate/TaskList are not exposed in this session | 0 | Task lifecycle is recorded in this tracker | If task tools become available |
| [queued] Historical comparator request a9f52b31844848fcaab8de98729357eb cannot be queried under current ownership (HTTP 409) | 0 | The current-owner request has a retained terminal result; the historical process was not taken over or canceled | Controller reconciliation of historical request; evidence: validation/prior-comparator-status.json |

### Completed and Verified
<!-- These rows verify only the stated work; they do not constitute theorem acceptance -->
| AC | Task | Completed Round | Verified Round | Evidence |
|----|------|-----------------|----------------|----------|
| AC1 | [mainline] T1 Read accepted proof and research pinned infrastructure | 0 | 0 review | Reviewer read the frozen problem and parent-supplied proof, repeated local-project searches, and inspected NormTrace.lean, Basic.lean, CongruenceSubgroups.lean, and FunctionsBoundedAtInfty.lean. BitLesson: NONE. |
| AC1 (implementation only) | [mainline] T2 Implement exact selected declaration | 0 (inherited implementation) | 0 review, source/body only | Submission.f036cc6b1f_fd_norm_bound matches the authoritative type ignoring whitespace, follows the accepted C = 1 argument, and is the only added named theorem. Frozen source prefix unchanged; no new axiom, placeholder, unsafe mechanism, or option override. Full-context/comparator acceptance remains blocked. |
| AC2 (partial only) | [mainline] T3 Audit source, dependencies, proof body, and axioms | 0 | 0 review | Reviewer reproduced body-only exit 0 and context-preserving exit 1; all four axiom reports contain only the permitted three axioms. Independently checked nine clean pinned dependencies, four snapshot mathlib files, and 20 cached project sources. Evidence: validation/reviewer/independent-source-audit.json and independent-check-results.json. Simplifier recommendation is builder-reported; this reviewer independently found no proof simplification defect. |
| AC2 (execution only), AC3 | [mainline] T4 Execute exact comparator and record scoped controller handoff | 0 | 0 review, evidence only | Retained broker response is finished, returncode 1, revision 11b450d; challenge failure is in current-comparator-output.log:98–104. Summary records one local-project reference_use entry and BitLesson Delta NONE. Successful comparison remains T7. |
| AC3 | [mainline] T5 Commit Round 0 records | 0 | 0 review | 74d39ef6c8daaf5d245d691243f9abb41f8940f6 contains only tracker, contract, and summary and postdates comparator failure. Worktree was clean before reviewer tracker edits. The next candidate must include these review corrections before comparison. |
| AC2 (prerequisite audit only), AC3 | [mainline] T8 Validate the blocker bundle and check for an authorized controller resolution | 1 | pending verification | All 15 diagnostic names match the frozen commands; evidence hashes recorded in validation/round-1-blocker-audit.json. Current DAG still names proof base 218176a; no authorized resolution supplied in the review or identified in selected-node handoffs. T6/T7 remain blocked. |
| AC3 | [mainline] T9 Commit reviewer corrections and Round 1 controller handoff | 1 | pending verification | Documentation commit `docs(proof): retain active gates and hand off all frozen import failures` contains the corrected tracker, Round 1 contract, and full 15-target summary handoff. No proof change or comparator acceptance claimed. |

### Explicitly Deferred
<!-- External prerequisites remain active and blocked above; none is waived or counted complete -->
| Task | Original AC | Deferred Since | Justification | When to Reconsider |
|------|-------------|----------------|---------------|-------------------|
| None | — | — | Mandatory AC2 work is tracked as blocked T6/T7, not as optional follow-up. Outer-controller reviewer comparison, wiki/PR integration, and DAG transition remain outside this implementation plan. | — |
