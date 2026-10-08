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
Implement only `Submission.p06_9e0f5043ff_sdp_clear_first_column` at its frozen child type, following the accepted parent-supplied proof. Produce a warning-clean, committed candidate with a clean worktree and a successful exact-node comparator run, then return control to the recursive controller.

Source plan: /mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-local-norm-order-a1-dvr-determinant-length-a1-dvr-matrix-diagona-61e38f4de9/rlcr-plan-v4.md

### Acceptance Criteria
<!-- Each criterion must be independently verifiable -->
<!-- The builder must extract or define these in Round 0 -->

1. **AC1 — Exact proof and provenance:** `Submission.lean` contains only the selected new named theorem, with its frozen hypotheses and conclusion, implementing the accepted proof. Consult the frozen problem, accepted child handoff, and pinned local-project snapshot; record exactly one `reference_use` entry with concrete findings.
2. **AC2 — Verified candidate:** Warning-fatal Lean verification and complete source/protected-file review pass; pinned dependencies and transitive axioms are checked; the candidate is committed with a clean worktree at the tested SHA; the configured exact-node comparator exits zero and prints `Your solution is okay!`.
3. **AC3 — Reviewable handoff:** Finalize tracker, contract, and round summary with evidence and BitLesson Delta, accurately distinguishing author verification from pending independent review; return without running root/sibling comparators or outer-controller publication/state transitions.

---

## MUTABLE SECTION
<!-- Update each round with justification for changes -->

### Plan Version: 1 (Updated: Round 0)

#### Plan Evolution Log
<!-- Document any changes to the plan with justification -->
| Round | Change | Reason | Impact on AC |
|-------|--------|--------|--------------|
| 0 | Initialize selected-node implementation contract | User's authoritative atomic-node plan | Establish AC1–AC3 without changing proof boundary |
| 0 | Audit and retain existing candidate; recover recorded verification blockers | HEAD already implements the exact theorem; prior round records show uncertain verifier requests and inherited import errors | AC1 needs fresh audit; AC2 still requires trusted comparator success, with no mathematical plan change |
| 0 | Commit only requested Round 0 records and validation evidence | User requests a commit; fresh audits and simplifier find no necessary Lean edit | Proof content unchanged; documentation commit is not comparator acceptance |

#### Active Tasks
<!-- Mainline tasks only: each task must directly advance the current round objective and carry routing metadata -->
| Task | Target AC | Status | Tag | Owner | Notes |
|------|-----------|--------|-----|-------|-------|
| [mainline] T3 Build, audit, simplify, and commit the candidate | AC2 | blocked | coding | claude | BitLesson NONE; selected-node check exits 0, axioms permitted, full-source check exits 1 in unchanged frozen prefix; source audit passes; simplifier recommends no edit |
| [mainline] T4 Run exact-node comparator and finalize handoff | AC2, AC3 | blocked | coding | claude | BitLesson NONE; blocked-round evidence finalized; successful handoff requires B2/B3 resolution and exact-node comparator exit 0 plus sentinel |

### Blocking Side Issues
<!-- Only issues that directly block current mainline progress belong here -->
| Issue | Discovered Round | Blocking AC | Resolution Path |
|-------|-----------------|-------------|-----------------|
| [blocking] B1 Sandbox launcher cannot find bubblewrap (workaround established) | 0 | AC1, AC2 | Explicitly requested execution escalation succeeded for local commands; no sandbox or service configuration changed |
| [blocking] B2 Prior comparator requests uncertain; configured service restoration unconfirmed | 0 | AC2 | Obtain existing controller's reconciliation under current claim before resubmission; requested from user |
| [blocking] B3 Inherited frozen Submission import errors reproduced this round | 0 | AC2 | Full-source warning-fatal Lean exits 1 at lines 9–11; unchanged root placeholder also becomes an error at line 14. Preserve frozen context and require trusted environment resolution; see warning-fatal-full-source.log |

### Queued Side Issues
<!-- Non-blocking issues stay queued and must NOT replace the round objective -->
| Issue | Discovered Round | Why Not Blocking | Revisit Trigger |
|-------|-----------------|------------------|-----------------|
| [queued] TaskCreate/TaskUpdate/TaskList tools absent from available tool catalog | 0 | Task metadata and progress are maintained in this tracker | Revisit only if task tools become available |

### Completed and Verified
<!-- Only move tasks here after the reviewer has verified them -->
| AC | Task | Completed Round | Verified Round | Evidence |
|----|------|-----------------|----------------|----------|
| AC1 | [mainline] T1 Read frozen proof and research pinned local-project APIs | 0 | pending verification | Read frozen problem and accepted proof; local-project manifest pins match clean snapshot checkouts; Matrix.mul_apply and transvection APIs inspected; targeted clearing search had no matches |
| AC1 | [mainline] T2 Implement the exact selected declaration | 0 | pending verification | Existing theorem audited against accepted proof and exact frozen type; full diff adds only this theorem with local have steps; dispatch handoff matches byte-for-byte; no source repair indicated |

### Explicitly Deferred
<!-- Items here require strong justification -->
| Task | Original AC | Deferred Since | Justification | When to Reconsider |
|------|-------------|----------------|---------------|-------------------|
