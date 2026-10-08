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
Implement only `Submission.p03_tate_uniformization_68cf3476` at its exact frozen child type, preserving all protected inputs and approved dependencies, then return a warning-clean, committed candidate accepted by the configured comparator for `root.tate_uniformization-a1` to the recursive controller.

Source plan: /mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p03/.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/nodes/root-tate-uniformization-a1/rlcr-plan-v1.md

### Acceptance Criteria
<!-- Each criterion must be independently verifiable -->
<!-- The builder must extract or define these in Round 0 -->

- AC1: `Submission.lean` implements the exact selected declaration without placeholders, new axioms, unsafe mechanisms, untracked named helpers, or changes to protected inputs; warning-fatal Lean checking succeeds.
- AC2: The clean candidate commit passes the exact selected-node comparator with exit zero and `Your solution is okay!`, including the required exact-type, dependency, axiom, Git, and compiler-header evidence.
- AC3: The accepted proof, frozen problem, policy entry, and pinned local-project references are inspected; the summary contains exactly one `reference_use` entry with actual paths and findings.
- AC4: Goal tracker, round contract, and round summary accurately record scope, routing, task status, evidence, and BitLesson selection; control returns without performing outer-controller acceptance/publication work.

---

## MUTABLE SECTION
<!-- Update each round with justification for changes -->

### Plan Version: 1 (Updated: Round 0)

#### Plan Evolution Log
<!-- Document any changes to the plan with justification -->
| Round | Change | Reason | Impact on AC |
|-------|--------|--------|--------------|
| 0 | Initialize the supplied implementation plan without changing the selected DAG or proof | Required Round 0 setup | AC1–AC4 |

#### Active Tasks
<!-- Mainline tasks only: each task must directly advance the current round objective and carry routing metadata -->
| Task | Target AC | Status | Tag | Owner | Notes |
|------|-----------|--------|-----|-------|-------|
| [mainline] T2 Implement the exact selected theorem using accepted dependencies and local proof steps | AC1 | blocked | coding | claude | BitLesson: NONE; local assembly checked, but discriminant identity and uniformization construction remain unproved in Lean; no candidate source added |
| [mainline] T3 Run warning-fatal checks and audit the complete source diff | AC1 | blocked | coding | claude | BitLesson: NONE; source integrity checked; exact-goal attempt exits 1; conditional assembly exits 0 and does not prove the target |
| [mainline] T4 Commit the candidate, confirm clean SHA, and run the exact node comparator | AC2 | blocked | coding | claude | BitLesson: NONE; comparator on clean evidence commit a1f5a77 exited 1: selected declaration not found; no proof candidate or acceptance exists |

### Blocking Side Issues
<!-- Only issues that directly block current mainline progress belong here -->
| Issue | Discovered Round | Blocking AC | Resolution Path |
|-------|-----------------|-------------|-----------------|
| [blocking] Sandbox command launcher lacks bubblewrap | 0 | AC1, AC2 | Required commands can run only through explicit tool escalation; initial escalated read succeeded |
| [blocking] The selected Lean proof is unfinished | 0 | AC1, AC2 | Final exact-goal diagnostic at `/tmp/p03-tu-round0-ve8vshzl/AssemblyAttempt.lean.log` leaves the discriminant product identity and the surjective homomorphism with specified kernel and coordinates. Nonvanishing and equivariance assemble conditionally. This is unfinished formalization, not a rejection of the accepted proof or DAG |
| [blocking] Exact selected-node comparator failed | 0 | AC2 | Request 876d96e55a0b44d889b7712cd11d5ae7 exited 1 on clean a1f5a77: `Submission.p03_tate_uniformization_68cf3476` is absent; implementing the complete frozen theorem remains necessary |

### Queued Side Issues
<!-- Non-blocking issues stay queued and must NOT replace the round objective -->
| Issue | Discovered Round | Why Not Blocking | Revisit Trigger |
|-------|-----------------|------------------|-----------------|
| [queued] TaskCreate/TaskUpdate/TaskList are not exposed by the available tool registry | 0 | Task state can be recorded faithfully in this tracker | Use native task tools if made available; do not fabricate tool calls |
| [queued] Pinned `Def_FLTPrelim_Modularity.lean` emits an inherited deprecated-import warning | 0 | It compiled with exit zero under the requested warning option; candidate diagnostics are separate and protected imports remain fixed | Only an authorized dependency/toolchain maintenance task |

### Completed and Verified
<!-- Only move tasks here after the reviewer has verified them -->
| AC | Task | Completed Round | Verified Round | Evidence |
|----|------|-----------------|----------------|----------|
| AC1, AC3 | [mainline] T1 Inspect frozen inputs, accepted proof, policy, and local references (coding / claude) | 0 | pending verification | Read accepted 18-step proof and frozen problem; matching policy digest and lines 10–11; pinned source searches and inspection found invariant definitions, preparation and point group formulas, but no Tate uniformization declaration |
| AC3, AC4 | [mainline] T5 Finalize round evidence and return control (coding / claude) | 0 | pending verification | Round contract, summary, explicit remaining formal goals, local diagnostic record, and failed comparator identity recorded; return is unsuccessful and does not assert proof acceptance |

### Explicitly Deferred
<!-- Items here require strong justification -->
| Task | Original AC | Deferred Since | Justification | When to Reconsider |
|------|-------------|----------------|---------------|-------------------|
