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
Implement only `Submission.f036cc6b1f_hecke_commute` with its exact frozen child type, using the accepted parent proof and pinned local project infrastructure; produce a warning-clean, committed, clean candidate passing the configured selected-node comparator, then return to the recursive controller.

Source plan: /mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/nodes/root-good-hecke-commute-a1/rlcr-plan-v6.md

### Acceptance Criteria
<!-- Each criterion must be independently verifiable -->
<!-- The builder must extract or define these in Round 0 -->

1. **AC1 — Exact implementation:** `Submission.lean` contains exactly the tracked new theorem with the frozen binders and conclusion, no new named helpers, placeholders, axioms, unsafe mechanisms, or protected-source changes. Research uses exactly the pinned local-project snapshot and records provenance.
2. **AC2 — Verified candidate:** Warning-fatal Lean validation and transitive axiom checks pass; the complete source diff is audited; the candidate is committed and clean at the exact SHA for which the selected-node comparator exits zero and prints `Your solution is okay!`.
3. **AC3 — Controller handoff:** Round contract, task evidence, reference_use (exactly one local-project entry), and BitLesson Delta are recorded accurately. Independent reviewer acceptance, wiki publication, DAG transition, and PR integration remain outer-controller work.

---

## MUTABLE SECTION
<!-- Update each round with justification for changes -->

### Plan Version: 1 (Updated: Round 0)

#### Plan Evolution Log
<!-- Document any changes to the plan with justification -->
| Round | Change | Reason | Impact on AC |
|-------|--------|--------|--------------|
| 0 | Initialize exact selected-node implementation plan | Authoritative current contract supersedes historical scaffold architecture | AC1–AC3 |
| 0 | Use persistent task tables as Task-system fallback | No TaskCreate, TaskUpdate, or TaskList tool is exposed in this session | No proof-scope change; preserve lane and routing metadata |
| 0 | Audit and retain existing exact-node candidate | HEAD already includes the complete selected proof; do not invent unnecessary theorem changes | AC1 unchanged; acceptance still requires fresh AC2 evidence |
| 0 | Commit only the three required round records; retain diagnostics as local ignored evidence | User explicitly requests committed changes, while the theorem needs no source change | Final comparator must identify the documentation commit exactly; no mathematical scope change |

#### Active Tasks
<!-- Mainline tasks only: each task must directly advance the current round objective and carry routing metadata -->
| Task | Target AC | Status | Tag | Owner | Notes |
|------|-----------|--------|-----|-------|-------|
| [mainline] T3 Run warning-fatal validation, axiom/source audits, and simplifier review | AC2 | blocked | coding | claude | Selected diagnostic passes with standard axioms; full-file warning-fatal check fails in frozen context; see B1 |
| [mainline] T4 Finalize records, commit clean candidate, and run exact selected-node comparator | AC2, AC3 | blocked | coding | claude | Author request 656443635b8447f5862baf3833826634 exited 1 on frozen-context B1; final documentation-commit evidence belongs in comparator-final.log and verification-outcome.json; no acceptance claimed |

### Blocking Side Issues
Sandbox execution lacks bubblewrap (Round 0, AC1/AC2); approved escalated execution succeeds and resolves the execution blocker.
**[blocking] B1 (coding / claude):** Fresh full-file warning-fatal Lean check exits 1: `Submission.lean:9:22` cannot resolve `FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions`; `Submission.lean:10:18` cannot resolve `FreyPackage.ModMCarrier.coe_rescaleLin_apply`; the frozen root stub also emits a fatal `sorry` warning at line 12. AC2 requires a controller-authorized correction to the frozen context/verification environment; this worker cannot delete protected context or prove the out-of-scope parent. Evidence: `full-warning-fatal.log`. The selected-node diagnostic passes, but cannot establish comparator acceptance.

The exact-node comparator independently reproduced the two unknown-name errors while building its frozen challenge, exited 1, and did not print `Your solution is okay!`; see `comparator.log` (request 656443635b8447f5862baf3833826634, source candidate 705d8644472c68eeb90845dbc9222a5e37f5db81). No worker-side authorized repair was found. The final documentation-commit rerun is recorded separately without altering these acceptance criteria.
<!-- Only issues that directly block current mainline progress belong here -->
| Issue | Discovered Round | Blocking AC | Resolution Path |
|-------|-----------------|-------------|-----------------|

### Queued Side Issues
TaskCreate/TaskUpdate/TaskList are unavailable (Round 0); persistent tables retain all task metadata. Revisit only if those tools become available.
<!-- Non-blocking issues stay queued and must NOT replace the round objective -->
| Issue | Discovered Round | Why Not Blocking | Revisit Trigger |
|-------|-----------------|------------------|-----------------|

### Completed and Verified
<!-- Only move tasks here after the reviewer has verified them -->
| AC | Task | Completed Round | Verified Round | Evidence |
|----|------|-----------------|----------------|----------|
| AC1 | [mainline] T1 Inspect accepted proof and pinned references | 0 | pending verification | Accepted seven-step proof and frozen problem read; pinned P2M coefficient/uniqueness declarations found at lines 340/172; exact normalization confirmed in Definitions |
| AC1 | [mainline] T2 Implement exact commutativity declaration | 0 | pending verification | Existing implementation retained; full base-to-HEAD source diff adds only the tracked theorem, local proof steps, and namespace opens; no new proof dependency on root stub |
| AC2 | [mainline] T3 source/provenance and simplifier subtasks | 0 | pending verification | `source-audit.json`: frozen type/prefix exact, three reused sources byte-equal to snapshot and base, all nine packages clean/pinned. Author-side simplifier found no defect or necessary simplification; this is not independent acceptance |
| AC3 | [mainline] T4 round-record subtask | 0 | pending verification | Round contract, full summary, one local-project reference_use entry, and BitLesson Delta recorded; no loop state changed |

### Explicitly Deferred
<!-- Items here require strong justification -->
| Task | Original AC | Deferred Since | Justification | When to Reconsider |
|------|-------------|----------------|---------------|-------------------|
