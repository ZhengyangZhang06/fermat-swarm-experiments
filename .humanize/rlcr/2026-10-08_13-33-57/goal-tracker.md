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
Implement only `Submission.p04_tz91_invariant_restriction_norm_range` with the exact frozen child type and accepted parent-supplied proof, then return a warning-clean, committed candidate whose configured exact-node comparator succeeds. Independent reviewer acceptance, wiki publication, and the DAG transition remain outer-controller work.

Source plan: /mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/nodes/root-tate-index-annihilation-a1-tate-zero-transfer-a1-invariant-restr-4fa1637a00/rlcr-plan-v4.md

### Acceptance Criteria
<!-- Each criterion must be independently verifiable -->
<!-- The builder must extract or define these in Round 0 -->

1. **AC1 — Exact implementation and provenance:** `Submission.lean` contains the exact selected declaration, without additional named helpers or new dependencies; the accepted proof and frozen problem remain unchanged. Research uses the pinned local-project snapshot with paths and findings recorded.
2. **AC2 — Verified candidate:** Warning-fatal Lean checks, full source-diff and transitive-axiom audits, and clean pinned dependency checks pass. The candidate is committed with a clean worktree; the configured comparator for this node exits zero and prints `Your solution is okay!` at that exact SHA.
3. **AC3 — Reviewable handoff:** Round contract, task status, and summary accurately record scope, evidence, reference_use (exactly one local-project entry), BitLesson selection, and remaining outer-controller responsibilities. Return without running a root/sibling comparator or changing proof acceptance state.

---

## MUTABLE SECTION
<!-- Update each round with justification for changes -->

### Plan Version: 1 (Updated: Round 1)

#### Plan Evolution Log
<!-- Document any changes to the plan with justification -->
| Round | Change | Reason | Impact on AC |
|-------|--------|--------|--------------|
| 0 | Initialize the implementation-only round from the authoritative selected-node plan | Existing proof and DAG gates are complete | AC1–AC3 |
| 0 | Audit the inherited same-node candidate before making changes | The branch already contains a candidate (62765ae, bdf8435); no comparator acceptance is recorded | AC1 unchanged; AC2 still requires a fresh exact-node check |
| 1 | Focus on the reviewer's missing controller-authenticated failed-request inputs | The reviewer confirmed local integrity but cannot certify remote inputs from a terminal excerpt; exact comparator still failed | AC2 stays blocked pending evidence and authorized reconciliation; AC1 unchanged |

#### Active Tasks
<!-- Mainline tasks only: each task must directly advance the current round objective and carry routing metadata -->
| Task | Target AC | Status | Tag | Owner | Notes |
|------|-----------|--------|-----|-------|-------|
| [mainline] T3 Run warning-fatal build and source/dependency/axiom audits | AC2 | blocked | coding | claude | BitLesson: NONE; isolated exact type and axiom audit pass; full-file build fails on unchanged frozen attribute and root sorry |
| [mainline] T4 Commit clean candidate and run exact-node comparator | AC2 | blocked | coding | claude | BitLesson: NONE; clean checkpoint b92f7f6a88b239299fb61797260421ce450a2272; request 20cace6a340046d5ad4d0884dd3a16f9 exited 1 building frozen challenge, no success marker |
| [mainline] T6 Locate and audit controller-authenticated inputs for the existing failed request | AC2 | blocked | coding | claude | BitLesson: NONE; 266 mounted metadata artifacts including 133 prepared packets contain no request/candidate match; both available export implementations admit only successful verified requests |

### Blocking Side Issues
<!-- Only issues that directly block current mainline progress belong here -->
| Issue | Discovered Round | Blocking AC | Resolution Path |
|-------|-----------------|-------------|-----------------|
| Sandbox launcher lacks bubblewrap | 0 | AC1, AC2 | Resolved operationally by approved escalated command execution; no project change required |
| Frozen Submission.lean line 10 references missing `Representation.TateResCor.cosetDecomp_apply`; inherited root declaration at line 15 uses sorry | 0 | AC2 | Current warning-fatal build reproduced both failures (exit 1). Exact child diagnostic passes, but does not replace the full-file/comparator gate. Requested authorized controller handoff; preserve frozen inputs. |
| Exact-node comparator cannot build its independent frozen challenge | 0 | AC2 | Request 20cace6a340046d5ad4d0884dd3a16f9 exited 1 at challenge/Submission.lean:10. Controller must reconcile its frozen challenge inputs while preserving the selected contract; editing only the candidate theorem cannot repair that independent build. |
| Actual remote comparator inputs for request 20cace6a340046d5ad4d0884dd3a16f9 are unavailable | 1 | AC2 | Search confirmed no matching mounted artifact. Both inspected exporters filter returncode=0 and require a verified receipt. A controller must expose the original failed operation, prepared inputs, and copied checker sources without changing its failed status; see round-1-controller-handoff.md. |

### Queued Side Issues
<!-- Non-blocking issues stay queued and must NOT replace the round objective -->
| Issue | Discovered Round | Why Not Blocking | Revisit Trigger |
|-------|-----------------|------------------|-----------------|
| TaskCreate/TaskUpdate/TaskList tools are unavailable in this session | 0 | Task lifecycle can be maintained explicitly in this tracker | Revisit only if the tools become available; no replacement task-system implementation |

### Completed and Verified
<!-- Only move tasks here after the reviewer has verified them -->
| AC | Task | Completed Round | Verified Round | Evidence |
|----|------|-----------------|----------------|----------|
| AC1 | [mainline] T1 Read frozen proof/context and research pinned local-project infrastructure | 0 | pending verification | Read accepted four-step proof and frozen problem; inspected normBar, Coinvariants.mk_surjective, Rep.res, and RightTransversal/IsComplement.equiv in the pinned snapshot. BitLesson: NONE. |
| AC1 | [mainline] T2 Implement the exact atomic declaration in Submission.lean | 0 | pending verification | Same-node implementation already present in inherited commits 62765ae/bdf8435. Complete diff from authoritative base adds only the exact selected declaration. Read-only simplifier found no useful change, no additional named helpers, and no new unsafe mechanism. Isolated exact-type diagnostic passes with only propext, Classical.choice, Quot.sound; no proof acceptance claimed. BitLesson: NONE. |
| AC3 | [mainline] T5 Finalize tracker and implementation handoff summary | 0 | pending verification | Round contract and summary finalized with one local-project reference_use entry, BitLesson NONE, dependency/source audit, and explicit failed full-file/comparator evidence. Acceptance/publication remain outer-controller tasks. |
| AC3 | [mainline] T7 Finalize Round 1 evidence handoff and tracker | 1 | pending verification | Round 1 contract, summary, evidence-location JSON, and controller artifact request are complete; only these round documents and this tracker are committed. BitLesson NONE. AC2 remains blocked; no acceptance or loop-state change. |

### Explicitly Deferred
<!-- Items here require strong justification -->
| Task | Original AC | Deferred Since | Justification | When to Reconsider |
|------|-------------|----------------|---------------|-------------------|
