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
Implement and verify exactly `Submission.p04_tz91_invariant_restriction_norm_range` against its frozen child type and accepted parent-supplied proof, preserving the frozen problem and pinned dependencies, then return the clean committed candidate to the recursive controller.

Source plan: /mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p04/.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/nodes/root-tate-index-annihilation-a1-tate-zero-transfer-a1-invariant-restr-4fa1637a00/rlcr-plan-v3.md

### Acceptance Criteria
<!-- Each criterion must be independently verifiable -->
<!-- The builder must extract or define these in Round 0 -->

1. **AC1 — Exact implementation:** `Submission.lean` contains only the selected new theorem, with the exact frozen type, no new named helpers, and a proof following the accepted handoff using permitted pinned infrastructure. Record local-project provenance and inspect all source changes for placeholders, new axioms, unsafe mechanisms, or protected-file changes.
2. **AC2 — Candidate verification:** warning-fatal Lean checks pass; pinned dependencies and transitive axioms pass the configured exact-node comparator; the candidate is committed and clean at the tested SHA; the comparator exits zero with `Your solution is okay!`.
3. **AC3 — Reviewable handoff:** initialize and maintain the tracker and round contract, record reference_use with exactly one local-project entry and a BitLesson Delta, and return control with a round summary. Fresh independent review, wiki publication, and DAG transition remain outer-controller tasks.

---

## MUTABLE SECTION
<!-- Update each round with justification for changes -->

### Plan Version: 1 (Updated: Round 1)

#### Plan Evolution Log
<!-- Document any changes to the plan with justification -->
| Round | Change | Reason | Impact on AC |
|-------|--------|--------|--------------|
| 0 | Initialize the selected-node implementation plan; preserve its authoritative type and atomic DAG boundary. | Required Round 0 setup. | AC1–AC3 |
| 0 | Record a frozen-challenge build blocker without changing the implementation boundary. | The exact comparator fails while compiling challenge/Submission.lean, before candidate comparison, on an unknown constant in the immutable attribute command. | AC2 remains unsatisfied; controller reconciliation is required. No replacement contract or decomposition is introduced. |
| 1 | Follow reviewer request to locate the existing verification request's actual inputs and controller reconciliation evidence. | A packet digest does not expose the prepared inputs or deployed checker; repeated unchanged verification is not requested. | Advances AC2/AC3 within the original frozen boundary. |

#### Active Tasks
<!-- Mainline tasks only: each task must directly advance the current round objective and carry routing metadata -->
| Task | Target AC | Status | Tag | Owner | Notes |
|------|-----------|--------|-----|-------|-------|
| [mainline] T3 Audit, build warning-fatal, commit, and run the exact-node comparator | AC2 | blocked | coding | claude | BitLesson NONE. Candidate 3489ec1665d22e9d9eea739e5be2f02ed6c9d489 is committed and clean. Build, explicit warning-fatal check, and exact comparator all exited 1; immutable challenge references an unavailable constant. No acceptance claimed. |

### Blocking Side Issues
<!-- Only issues that directly block current mainline progress belong here -->
| Issue | Discovered Round | Blocking AC | Resolution Path |
|-------|-----------------|-------------|-----------------|
| [blocking] Frozen challenge Submission.lean:10 references unknown constant Representation.TateResCor.cosetDecomp_apply. | 0 | AC2 | Controller must reconcile the frozen source/import context and verification inputs. Selected-theorem-only edits cannot repair the independently compiled challenge. Do not mutate the contract or verifier. |
| [blocking] Explicit warning-fatal check rejects the unchanged frozen root sorry at Submission.lean:15. | 0 | AC2 | Controller must supply a compatible node-only warning-fatal verification boundary while preserving the frozen problem. Do not prove or alter the unrelated root in this node. |
| [blocking] Existing request's prepared packet, source snapshots, and deployed checker/toolchain identities are unavailable to the reviewer. | 1 | AC2, AC3 | The 114 prepared manifests in /runtime/review-evidence contain no selected-node/request match. Both operator export scripts filter for successful requests, excluding this exit-1 request. Controller must expose the existing failed-request evidence without changing its verdict; detailed artifact list is in round-1-summary.md. |

### Queued Side Issues
<!-- Non-blocking issues stay queued and must NOT replace the round objective -->
| Issue | Discovered Round | Why Not Blocking | Revisit Trigger |
|-------|-----------------|------------------|-----------------|
| [queued] TaskCreate/TaskUpdate/TaskList are not exposed by this runtime. | 0 | Required task metadata and state are maintained in this tracker; no callable Task API was found. | If Task tools become available. |

### Completed and Verified
<!-- Only move tasks here after the reviewer has verified them -->
| AC | Task | Completed Round | Verified Round | Evidence |
|----|------|-----------------|----------------|----------|
| AC1 | [mainline] T1 Inspect accepted proof, current candidate, and pinned local references | 0 | pending verification | Read accepted handoff and frozen problem; searched snapshot with rg; inspected normBar, coinvariant projection, restriction, and right-transversal definitions. |
| AC1 | [mainline] T2 Complete the exact single-theorem implementation | 0 | pending verification | Existing candidate at bdf84353b3f38a42e108b54861b6fb18b5085996 already implements only the selected theorem. Retained it unchanged; dispatch-to-HEAD diff adds 36 lines to Submission.lean, and frozen source bytes remain unchanged. |
| AC3 | [mainline] T4 Finalize tracker, contract, and implementation summary | 0 | pending verification | Initialized immutable tracker and round contract before implementation; summary records exact candidate, failed build/comparator, one local-project reference entry, and BitLesson NONE. |
| AC2, AC3 | [mainline] T5 Locate existing request inputs and authorized verification reconciliation | 1 | pending verification | Located the review-evidence mount and audited only packet identity metadata for a match; inspected the two success-only operator exporters and documented why no failed-request copy appears. No authorized frozen-context reconciliation found. This investigation is complete; the evidence and build blockers remain unresolved. |
| AC3 | [mainline] T6 Finalize Round 1 evidence and handoff | 1 | pending verification | Round 1 summary provides exact request/candidate/digest bindings, exporter source locations, local hashes, and the required failed-request artifact handoff. Round contract and tracker reflect AC2's unresolved status. |

### Environment resolution

The missing-bubblewrap launcher failure was worked around through the provided escalation mechanism. Pinned Lean/Lake binaries were located outside PATH. Neither issue remains the verification blocker.

### Explicitly Deferred
<!-- Items here require strong justification -->
| Task | Original AC | Deferred Since | Justification | When to Reconsider |
|------|-------------|----------------|---------------|-------------------|
