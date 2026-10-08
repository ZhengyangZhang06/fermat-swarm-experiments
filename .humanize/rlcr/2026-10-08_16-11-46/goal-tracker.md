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
Implement only `Submission.p04_tz91_invariant_restriction_norm_range` at the frozen child type, following the accepted parent-supplied proof; deliver a warning-clean, source-audited, committed candidate that passes the exact selected-node comparator, then return to the recursive controller.

Source plan: /mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/nodes/root-tate-index-annihilation-a1-tate-zero-transfer-a1-invariant-restr-4fa1637a00/rlcr-plan-v6.md

### Acceptance Criteria
<!-- Each criterion must be independently verifiable -->
<!-- The builder must extract or define these in Round 0 -->

1. **AC1 — Exact implementation:** `Submission.lean` contains only the selected new theorem, with its exact frozen type and no new named helpers; the accepted proof and operational DAG remain unchanged.
2. **AC2 — Verified candidate:** Warning-fatal Lean builds and full diff/input audits pass; the exact node comparator exits zero and prints `Your solution is okay!` on a clean committed candidate with pinned dependencies and allowed transitive axioms.
3. **AC3 — Research provenance:** Search the pinned snapshot with `rg`, inspect relevant sources, and record exactly one `reference_use` entry, `local-project`, including actual paths, findings, compatibility and axiom evidence.
4. **AC4 — Handoff:** Finalize the tracker, round contract, and summary with evidence and BitLesson Delta; return control without running a parent/root comparator or performing the controller's review/publication/DAG transition.

---

## MUTABLE SECTION
<!-- Update each round with justification for changes -->

### Plan Version: 1 (Updated: Round 1)

#### Plan Evolution Log
<!-- Document any changes to the plan with justification -->
| Round | Change | Reason | Impact on AC |
|-------|--------|--------|--------------|
| 0 | Initialize the selected-node implementation plan | Authoritative child contract and accepted proof govern this round | AC1–AC4 |
| 0 | Use this tracker for task state because TaskCreate/TaskUpdate/TaskList are not exposed | Tool discovery found no Task system; preserve all requested lane/routing metadata here | AC4; no proof-scope change |
| 0 | Audit and retain the inherited exact-node implementation from 62765ae/bdf8435 | The current tree already contains the selected proof; no gratuitous rewrite is warranted and acceptance is still required | AC1 unchanged; AC2 remains mandatory |
| 1 | Focus on authentic failed-request inputs and authorized frozen-challenge reconciliation | The reviewer passed local integrity but cannot establish remote input identity from terminal logs; exact author comparison failed | AC2 stays mandatory; AC1 and the immutable selected-node contract remain unchanged |
| 1 | Inspect newly mounted operator header policy as a possible reconciliation | Its p04 entry matches the frozen contract; archive checks pass, but production deployment is not established and no project guidance is configured | Advances AC2 diagnosis without enabling a policy or editing frozen input |

#### Active Tasks
<!-- Mainline tasks only: each task must directly advance the current round objective and carry routing metadata -->
| Task | Target AC | Status | Tag | Owner | Notes |
|------|-----------|--------|-----|-------|-------|
| [mainline] T3 Build with fatal warnings and audit complete diff and inputs | AC2 | blocked | coding | claude | BitLesson NONE; full-file build and preserved-context diagnostic exit 1 on frozen missing attribute and root sorry. Child type check has no error; transitive axioms are propext, Classical.choice, Quot.sound. All nine dependencies clean and pinned |
| [mainline] T4 Commit clean candidate and run exact node comparator | AC2 | blocked | coding | claude | BitLesson NONE; clean checkpoint b0ad04bde368623b3856a4a8c4bc5a22cbb80ac0; request 3c23c64cf708425894ed055e65e97df9 exited 1 building the independent frozen challenge; no success marker and no root comparator |
| [mainline] T6 Locate and audit authentic inputs and available reconciliation for the failed request | AC2 | blocked | coding | claude | BitLesson NONE; 588 mounted metadata files have no exact request/candidate/digest match; exporter requires success. Matching operator policy found, but no active deployment or project guidance established |

### Blocking Side Issues
<!-- Only issues that directly block current mainline progress belong here -->
| Issue | Discovered Round | Blocking AC | Resolution Path |
|-------|-----------------|-------------|-----------------|
| Sandbox launcher lacks bubblewrap | 0 | AC1–AC2 execution | Resolved operationally using approved escalated commands |
| Default PATH lacks lake | 0 | AC2 execution | Resolved operationally with controller-pinned Lean 4.33.1 under fermat-example/.humanize/toolchains |
| Frozen header names absent `Representation.TateResCor.cosetDecomp_apply`; frozen root has `sorry` | 0 | AC2 | Full warning-fatal build reproduced both errors (exit 1; warning-fatal-build.log). Requires controller-authorized reconciliation preserving the frozen contract; none supplied during this round |
| Exact-node comparator cannot build its independent frozen challenge | 0 | AC2 | Request 3c23c64cf708425894ed055e65e97df9 exited 1 at challenge/Submission.lean:10. Reported packet digest 5d6f827a86b081735a0577d66517d8ce7565f3af15d87a0e4dd8248d785e69dc. Controller must reconcile challenge inputs; editing only the candidate theorem cannot fix this failure |
| Actual failed-request comparator inputs and executed checker identities are unavailable to the reviewer | 1 | AC2 | No match in 588 mounted metadata files. Existing exporter admits only returncode=0 and verified receipts, so a controller must provide a diagnostic export preserving this request's actual exit-1 state |
| Newly staged header policy is not established as active in this node's verification path | 1 | AC2 | Read-only policy digest 96fc18eb6b8cbdad1beec37ca318ab2cf08ac1dda8ebf7cbfe1d6d51abf32f96 matches p04. Documentation requires controller rollout; worker/project guidance fields are absent. Obtain deployment receipt before relying on derived inputs |

### Queued Side Issues
<!-- Non-blocking issues stay queued and must NOT replace the round objective -->
| Issue | Discovered Round | Why Not Blocking | Revisit Trigger |
|-------|-----------------|------------------|-----------------|
| Task system tools unavailable | 0 | Task metadata and progress can be maintained in this tracker | Tool availability changes |

### Completed and Verified
<!-- Only move tasks here after the reviewer has verified them -->
| AC | Task | Completed Round | Verified Round | Evidence |
|----|------|-----------------|----------------|----------|
| AC1, AC3 | [mainline] T1 Read frozen inputs and research local-project sources | 0 | pending verification | Accepted proof and frozen problem read. Snapshot normBar, coinvariant surjection, restriction, right-transversal equivalence inspected; no selected-name or TateResCor matches in searched definitions. See dependency-source-audit.json. BitLesson NONE. |
| AC1 | [mainline] T2 Implement the exact atomic declaration | 0 | pending verification | Inherited candidate retained: only selected theorem added to Submission.lean relative to frozen base. Read-only simplifier found no necessary change, new helper, or unsafe mechanism. No comparator acceptance claimed. BitLesson NONE. |
| AC3, AC4 | [mainline] T5 Finalize evidence and return to controller | 0 | pending verification | Tracker, contract, summary, source/dependency audits, diagnostic log, and failed-comparator evidence finalized. One local-project reference_use entry; BitLesson NONE. No acceptance, publication, PR lifecycle, or DAG/loop-state modification. |
| AC4 | [mainline] T7 Finalize Round 1 evidence and controller handoff | 1 | pending verification | Round 1 contract, summary, precise artifact/rollout handoff, and three nonsecret evidence audits completed. Only explicit round documents/reports are committed; no Lean or automatic loop-state change. BitLesson NONE. AC2 remains blocked. |

### Explicitly Deferred
<!-- Items here require strong justification -->
| Task | Original AC | Deferred Since | Justification | When to Reconsider |
|------|-------------|----------------|---------------|-------------------|
