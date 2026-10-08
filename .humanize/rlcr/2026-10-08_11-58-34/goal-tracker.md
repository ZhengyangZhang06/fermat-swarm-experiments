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
Implement only `Submission.p07_flp_point_equiv_857cd4d38c` at the exact frozen atomic-node type in `Submission.lean`, following the accepted parent-supplied proof and pinned local-project references; deliver a warning-clean, committed candidate with a successful exact-node comparator run, then return to the recursive controller.

Source plan: /mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/nodes/root-full-level-quotient-a1-full-level-pullback-a1-pullback-point-equivalence-a1/rlcr-plan-v4.md

### Acceptance Criteria
<!-- Each criterion must be independently verifiable -->
<!-- The builder must extract or define these in Round 0 -->

1. **AC1 — Exact implementation:** The sole new named theorem has the complete frozen type, preserves every hypothesis and conclusion, follows the accepted proof, and uses only pinned proof-base declarations and local proof steps. No new helpers, axioms, placeholders, or protected-file changes.
2. **AC2 — Verified candidate:** Warning-fatal Lean verification and transitive axiom/dependency checks pass; the complete source diff is reviewed; the exact-node comparator exits zero and prints `Your solution is okay!` at a committed SHA with a clean worktree.
3. **AC3 — Auditable handoff:** Round contract, task status, reference provenance (exactly one `local-project` reference_use entry), BitLesson selection/delta, and summary accurately record evidence and distinguish author verification from pending independent controller review.

---

## MUTABLE SECTION
<!-- Update each round with justification for changes -->

### Plan Version: 1 (Updated: Round 0)

#### Plan Evolution Log
<!-- Document any changes to the plan with justification -->
| Round | Change | Reason | Impact on AC |
|-------|--------|--------|--------------|
| 0 | Initialize the supplied atomic-node implementation plan | Current frozen node contract controls; no decomposition changes | AC1–AC3 |
| 0 | Review and verify the existing selected-node candidate instead of duplicating it | Initial HEAD eccb244 already contains this node's implementation from 8ac90b1; it is not treated as an accepted dependency or as proof acceptance | AC1, AC2 remain required |

#### Active Tasks
<!-- Mainline tasks only: each task must directly advance the current round objective and carry routing metadata -->
| Task | Target AC | Status | Tag | Owner | Notes |
|------|-----------|--------|-----|-------|-------|
| [mainline] T3 Run warning-fatal checks, review source, and commit clean candidate | AC2 | blocked | coding | claude | BitLesson: NONE; full-source check failed on unchanged frozen attributes and root sorry; isolated child warning-fatal diagnostic and axiom reports passed; source review complete and candidate committed |
| [mainline] T4 Run exact-node comparator and finalize handoff | AC2, AC3 | in_progress | coding | claude | BitLesson: NONE; candidate and round audit committed; preserve exact HEAD while comparator runs; independent reviewer/wiki/DAG transitions remain controller tasks |

### Blocking Side Issues
<!-- Only issues that directly block current mainline progress belong here -->
| Issue | Discovered Round | Blocking AC | Resolution Path |
|-------|-----------------|-------------|-----------------|
| Sandbox launcher cannot find bubblewrap | 0 | AC1, AC2 | Local commands run through approved escalation; initial reads succeeded |
| `lake` absent from PATH | 0 | AC2 | Pinned binaries located at /mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin; use explicit toolchain PATH |
| Frozen Submission prefix does not pass warning-fatal Lean | 0 | AC2 | Lines 13–15 name unavailable constants opensMapFinal, baseChangePointToBase_ofBase, dualNumberFst_apply; line 22 is the inherited unsolved root. Preserve frozen context and obtain exact comparator evidence; isolated child diagnostics do not constitute acceptance |

### Queued Side Issues
<!-- Non-blocking issues stay queued and must NOT replace the round objective -->
| Issue | Discovered Round | Why Not Blocking | Revisit Trigger |
|-------|-----------------|------------------|-----------------|
| TaskCreate/TaskUpdate/TaskList unavailable in exposed tools | 0 | Goal tracker records the same task IDs, lane, routing, status, and evidence | If task tools become available |

### Completed and Verified
<!-- Only move tasks here after the reviewer has verified them -->
| AC | Task | Completed Round | Verified Round | Evidence |
|----|------|-----------------|----------------|----------|
| AC1 | [mainline] T1 Read accepted proof, frozen context, and pinned references | 0 | pending verification | Accepted seven-step proof and complete frozen problem read; exact snapshot revisions and all nine installed dependency revisions match and are clean; library APIs and no-match searches recorded for summary |
| AC1 | [mainline] T2 Implement the sole exact declaration in Submission.lean | 0 | pending verification | Existing candidate reviewed against the frozen DAG type and all seven proof steps; only p07_flp_point_equiv_857cd4d38c added over proof base 8cb34c6; unchanged base prefix; read-only simplifier recommends keeping the proof |

### Explicitly Deferred
<!-- Items here require strong justification -->
| Task | Original AC | Deferred Since | Justification | When to Reconsider |
|------|-------------|----------------|---------------|-------------------|
