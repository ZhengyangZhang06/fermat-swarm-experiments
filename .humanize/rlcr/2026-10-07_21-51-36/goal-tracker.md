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
Implement only `Submission.p06_9e0f5043ff_ifl_residue_length_inertia` with its exact frozen type and accepted natural proof, and return a warning-clean, source-audited, committed candidate whose exact selected-node comparator exits zero with `Your solution is okay!`. Independent reviewer acceptance, wiki publication, and DAG transitions belong to the outer controller.

Source plan: /mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-local-norm-order-a1-integral-fiber-length-a1-residue-length-inertia-a1/rlcr-plan-v4.md

### Acceptance Criteria
<!-- Each criterion must be independently verifiable -->
<!-- The builder must extract or define these in Round 0 -->

1. **AC1 — Exact implementation:** `Submission.lean` contains the selected declaration with the complete frozen type, no new named helpers, and a kernel-checked proof following the accepted handoff. Research records exactly one `local-project` reference entry with concrete paths, searches, and compatibility findings.
2. **AC2 — Author verification and handoff:** Warning-fatal Lean verification, complete source-diff and transitive-axiom audits pass; the candidate is committed and the worktree clean at that SHA; the exact selected-node comparator exits zero and prints `Your solution is okay!`.
3. **AC3 — Round records:** The tracker, focused round contract, and final summary accurately record work, evidence, routing, reference use, BitLesson selection, and the boundary between author verification and outer-controller acceptance.

---

## MUTABLE SECTION
<!-- Update each round with justification for changes -->

### Plan Version: 1 (Updated: Round 0)

#### Plan Evolution Log
<!-- Document any changes to the plan with justification -->
| Round | Change | Reason | Impact on AC |
|-------|--------|--------|--------------|
| 0 | Initialize from the authoritative selected-node implementation plan | Preserve the atomic node and frozen proof boundary | AC1–AC3 |
| 0 | Audit the existing implementation before considering edits | HEAD already contains the selected theorem; preserve its active comparator candidate and verify it rather than inventing new proof work | AC1–AC2 unchanged |

#### Active Tasks
<!-- Mainline tasks only: each task must directly advance the current round objective and carry routing metadata -->
| Task | Target AC | Status | Tag | Owner | Notes |
|------|-----------|--------|-----|-------|-------|
| [mainline] T3 Audit, build, commit, and run selected-node comparator | AC2 | in_progress (B1 blocks success) | coding | claude | Exact-type warning-fatal diagnostic and allowed-axiom audit pass; full-source build and existing official comparator fail. Run the required exact command after the round-record commit; retain its actual result separately. BitLesson: NONE. |
| [mainline] T4 Finalize round evidence and return to controller | AC3 | in_progress | coding | claude | Final summary records the failed gate without claiming acceptance. BitLesson: NONE. |

### Blocking Side Issues
<!-- Only issues that directly block current mainline progress belong here -->
| Issue | Discovered Round | Blocking AC | Resolution Path |
|-------|-----------------|-------------|-----------------|
| B1: Frozen Submission prefix contains unavailable attribute targets | 0 | AC2 | Reproduce with pinned Lean and require a controller-owned challenge-context repair; candidate edits cannot repair the separate frozen challenge. |

### Queued Side Issues
<!-- Non-blocking issues stay queued and must NOT replace the round objective -->
| Issue | Discovered Round | Why Not Blocking | Revisit Trigger |
|-------|-----------------|------------------|-----------------|
| TaskCreate/TaskUpdate/TaskList are absent from available tools | 0 | Work is tracked with stable task IDs and statuses in this file | Use native Task tools if they become available. |

### Completed and Verified
<!-- Only move tasks here after the reviewer has verified them -->
| AC | Task | Completed Round | Verified Round | Evidence |
|----|------|-----------------|----------------|----------|
| AC1 | [mainline] T1 Read frozen proof and pinned references (coding; claude) | 0 | pending verification | Read accepted six-step proof, frozen problem and manifest; rg found fiber-center, finite-normalization, residue-scalar, and module-length APIs in the pinned snapshot; localization sum/length query had no matches. |
| AC1 | [mainline] T2 Implement the exact selected theorem (coding; claude) | 0 | pending verification | Existing implementation retained unchanged. Read-only simplifier review found no defect or meaningful simplification; all six accepted proof steps accounted for. Byte-identical selected-proof diagnostic with the explicit frozen type passed warning-fatal Lean, with only propext, Classical.choice and Quot.sound. This is not comparator acceptance. |
| AC1–AC2 | [blocking] Use the prescribed escalation path for the missing sandbox launcher (coding; claude) | 0 | pending verification | Required commands executed successfully through require_escalated; the installed pinned Lean toolchain was located outside PATH. |
| AC2 | [blocking] B2 Reconcile the prior comparator request (coding; claude) | 0 | pending verification | One owner-bound observation at 2026-10-07T21:55:49Z found request 704ac49bcc694eb2989d4e4c6f0a5be4 finished, returncode 1, no acceptance marker. Failure is in the separate frozen challenge. Evidence: existing-comparator-observation.json and existing-comparator-output.log. |

### Explicitly Deferred
<!-- Items here require strong justification -->
| Task | Original AC | Deferred Since | Justification | When to Reconsider |
|------|-------------|----------------|---------------|-------------------|
