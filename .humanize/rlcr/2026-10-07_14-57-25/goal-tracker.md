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

### Plan Version: 1 (Updated: Round 0)

#### Plan Evolution Log
<!-- Document any changes to the plan with justification -->
| Round | Change | Reason | Impact on AC |
|-------|--------|--------|--------------|
| 0 | Initialize selected-node implementation plan | User-supplied authoritative child contract | AC1–AC3 |
| 0 | Audit the already-implemented candidate instead of adding a duplicate proof | The initial clean HEAD is 11b450d and already contains the exact selected declaration; prior evidence does not establish acceptance | Same AC1–AC3; no decomposition or contract change |

#### Active Tasks
<!-- Mainline tasks only: each task must directly advance the current round objective and carry routing metadata -->
| Task | Target AC | Status | Tag | Owner | Notes |
|------|-----------|--------|-----|-------|-------|

### Blocking Side Issues
<!-- Only issues that directly block current mainline progress belong here -->
| Issue | Discovered Round | Blocking AC | Resolution Path |
|-------|-----------------|-------------|-----------------|
| [blocking] Shell sandbox launcher lacks bubblewrap | 0 | AC1, AC2 | Use tool escalation for required commands; initial escalated read succeeded. |
| [blocking] Full-context warning-fatal check fails on two absent frozen attribute names | 0 | AC2 | Current CheckNode.lean exits 1 on FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions and FreyPackage.ModMCarrier.coe_rescaleLin_apply. Controller repair of immutable context required; verifier copies proof base 218176a before importing Submission. |
| [blocking] Exact-node comparator fails compiling the frozen challenge | 0 | AC2 | Request 651de54b4e4b4e739e83e4cd79b900b3 finished with exit 1 at 2026-10-07T15:15:30Z on the same two unknown constants, before candidate comparison. Evidence: validation/current-comparator-output.log. Repair requires controller authority. |

### Queued Side Issues
<!-- Non-blocking issues stay queued and must NOT replace the round objective -->
| Issue | Discovered Round | Why Not Blocking | Revisit Trigger |
|-------|-----------------|------------------|-----------------|
| [queued] TaskCreate/TaskUpdate/TaskList are not exposed in this session | 0 | Task lifecycle can be recorded in this tracker; no substitute external service is needed | If task tools become available |
| [queued] Historical comparator request a9f52b31844848fcaab8de98729357eb cannot be queried under current ownership (HTTP 409) | 0 | The exact prescribed command accepted a request under current ownership; no historical process was taken over or canceled | Controller reconciliation of historical request; evidence: validation/prior-comparator-status.json |

### Completed and Verified
<!-- Only move tasks here after the reviewer has verified them -->
| AC | Task | Completed Round | Verified Round | Evidence |
|----|------|-----------------|----------------|----------|
| AC1 | [mainline] T1 Read accepted proof and research pinned infrastructure | 0 | pending verification | Frozen proof read; rg searches and direct inspection of snapshot NormTrace.lean, Basic.lean, CongruenceSubgroups.lean and FunctionsBoundedAtInfty.lean. BitLesson: NONE. |
| AC1 | [mainline] T2 Implement exact selected declaration | 0 (inherited implementation) | pending verification | Existing Submission.lean implements C = 1 with only local proof steps; frozen source prefix unchanged. Not accepted merely because it exists. BitLesson: NONE. |
| AC2 (partial only) | [mainline] T3 Audit source, dependencies, proof body, axioms, and simplification | 0 | pending verification | Body-only warning-fatal check exits 0; full-context check exits 1. All nine dependencies clean and pinned. Source and exact-type audit logs retained in validation/. No acceptance claimed. |
| AC2 (execution only), AC3 | [mainline] T4 Execute exact comparator and record scoped controller handoff | 0 | pending verification | Terminal exit 1; no success marker. round-0-summary.md records the frozen-challenge failure, one local-project reference_use entry, and BitLesson Delta NONE. |
| AC3 | [mainline] T5 Commit final Round 0 records | 0 | pending verification | Documentation commit titled `docs(proof): record frozen-context blocker for coset norm bound` contains only the three requested round records. No Lean changes or acceptance claim. |

### Explicitly Deferred
<!-- Items here require strong justification -->
| Task | Original AC | Deferred Since | Justification | When to Reconsider |
|------|-------------|----------------|---------------|-------------------|
| [mainline] T3 Complete full-context validation and obtain comparator acceptance | AC2 | 0 | Full-context errors are in immutable proof base 218176a, not repairable by this child-only implementation. The comparator independently confirms the same frozen-challenge failure on committed clean SHA 11b450d. The blocker persisted across three consecutive goal turns. | Controller supplies a repaired authorized frozen import context without changing the theorem; AC2 remains unmet. |
