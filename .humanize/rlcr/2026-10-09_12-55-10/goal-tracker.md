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
Implement only `Submission.p09_af497904fe_ff_cyclotomic_supply` at the frozen child type, using the accepted handoff, pinned library infrastructure and comparator-approved dependencies. Produce a warning-clean, source-safe, committed candidate accepted by the exact selected-node comparator, then return to the recursive controller.

Source plan: /mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/nodes/root-frobenius-approximation-a1-finite-frobenius-a1-cyclotomic-froben-fcc401e280/rlcr-plan-v4.md

### Acceptance Criteria
<!-- Each criterion must be independently verifiable -->
<!-- The builder must extract or define these in Round 0 -->

1. **AC1 — Exact implementation:** `Submission.lean` contains the tracked declaration at the frozen type, without placeholders, new axioms, unsafe mechanisms, untracked named helpers or changes to frozen inputs, header, proof, or decomposition.
2. **AC2 — Verified candidate:** Warning-fatal Lean checks and full source-diff review pass; the candidate is committed with a clean worktree; the exact selected-node comparator exits zero and prints `Your solution is okay!`. Inspect exact-type, kernel, transitive-axiom, dependency and compiler-header evidence.
3. **AC3 — Auditable handoff:** Round contract, task status and summary accurately record work, evidence, any blockers, BitLesson selection, and exactly one `reference_use` entry for `local-project`. Publication, fresh reviewer rerun and DAG transition remain outer-controller work.

---

## MUTABLE SECTION
<!-- Update each round with justification for changes -->

### Plan Version: 1 (Updated: Round 0)

#### Plan Evolution Log
<!-- Document any changes to the plan with justification -->
| Round | Change | Reason | Impact on AC |
|-------|--------|--------|--------------|
| 0 | Initialize from authoritative selected-node plan | Required Round 0 setup; no scope change | AC1–AC3 |

#### Active Tasks
<!-- Mainline tasks only: each task must directly advance the current round objective and carry routing metadata -->
| Task | Target AC | Status | Tag | Owner | Notes |
|------|-----------|--------|-----|-------|-------|
| [mainline] T2 Implement the exact selected declaration | AC1 | blocked | coding | claude | BitLesson: NONE. Existing selected-node draft ends at explicit failure for nontrivial character continuation/nonvanishing. No Lean source changes made; the arithmetic argument remains unimplemented. |
| [mainline] T4 Commit clean candidate and run exact node comparator | AC2 | in_progress | coding | claude | BitLesson: NONE. Commit audit artifacts, then run only the exact node comparator. Local build already failed, so no acceptance claim. |
| [mainline] T5 Finalize tracker and round summary | AC3 | in_progress | coding | claude | Record failed gates and remaining exact goal; outer publication/review is out of scope. |

### Blocking Side Issues
<!-- Only issues that directly block current mainline progress belong here -->
| Issue | Discovered Round | Blocking AC | Resolution Path |
|-------|-----------------|-------------|-----------------|
| [blocking] Sandbox command launcher lacks bubblewrap | 0 | AC1, AC2 | Required commands use requested escalation; initial escalated reads succeeded |
| [blocking] Existing proof has an explicit unfinished continuation/nonvanishing obligation | 0 | AC1, AC2 | Formalize accepted arithmetic steps 15–25 locally, without new hypotheses or untracked helpers; reproduce exact selected-node diagnostics first. |

### Queued Side Issues
<!-- Non-blocking issues stay queued and must NOT replace the round objective -->
| Issue | Discovered Round | Why Not Blocking | Revisit Trigger |
|-------|-----------------|------------------|-----------------|
| [queued] TaskCreate/TaskUpdate/TaskList tools are unavailable | 0 | Persistent tracker records the same task metadata; tool discovery found no Task system | Tool availability changes |

### Completed and Verified
<!-- Only move tasks here after the reviewer has verified them -->
| AC | Task | Completed Round | Verified Round | Evidence |
|----|------|-----------------|----------------|----------|
| AC1, AC3 | [mainline] T1 Inspect frozen handoff, policy, source and pinned references | 0 | pending verification | Read complete accepted proof and frozen root record; inspected matching policy entry and manifest; searched pinned project and mathlib; source ends at `Submission.lean:3106`. Routing: coding / claude; BitLesson NONE. |
| AC1, AC2 | [mainline] T3 Run warning-fatal checks and audit the complete source diff | 0 | pending verification; acceptance gate failed | `HeaderAbsence-result.json`: exit 0. `SelectedNode-result.json`: exit 1 at the explicit arithmetic obligation. `source-audit.json`: exact type text preserved, no source diff. `dependency-audit.json`: all nine packages clean/pinned. Routing: coding / claude; BitLesson NONE. |

### Explicitly Deferred
<!-- Items here require strong justification -->
| Task | Original AC | Deferred Since | Justification | When to Reconsider |
|------|-------------|----------------|---------------|-------------------|
