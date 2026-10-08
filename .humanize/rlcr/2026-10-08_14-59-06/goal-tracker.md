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
Implement only `Submission.p07_cre_group_law_857cd4d38c` with the exact frozen child type and accepted natural proof, then return a warning-clean, committed candidate that passes the configured selected-node comparator to the recursive controller.

Source plan: /mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/nodes/root-curve-ring-equiv-a1-group-law-rebase-a1/rlcr-plan-v12.md

### Acceptance Criteria
<!-- Each criterion must be independently verifiable -->
<!-- The builder must extract or define these in Round 0 -->

1. **AC1 — Exact implementation:** `Submission.lean` contains the single tracked declaration with its frozen type, all required group-law and equivalence properties, no new named helpers, and no approved child dependencies.
2. **AC2 — Candidate verification:** warning-fatal Lean compilation and the exact selected-node comparator pass at a clean committed SHA; the comparator exits zero and prints `Your solution is okay!`. Audit source safety, pinned dependencies, and transitive axioms.
3. **AC3 — Evidence and scope:** record accepted-proof and local-project reference findings, complete-diff inspection, lesson selections, and round outcome; preserve protected files and leave independent acceptance, publication, and DAG transitions to the outer controller.

---

## MUTABLE SECTION
<!-- Update each round with justification for changes -->

### Plan Version: 1 (Updated: Round 0)

#### Plan Evolution Log
<!-- Document any changes to the plan with justification -->
| Round | Change | Reason | Impact on AC |
|-------|--------|--------|--------------|
| 0 | Initialized from authoritative selected-node plan | Keep implementation inside this atomic node | AC1–AC3 |
| 0 | Existing selected theorem found at initial HEAD 296be36; review its body directly before fresh verification | Avoid needless proof edits; no acceptance inferred from earlier implementation | AC1–AC2 |
| 0 | Defer passing validation gates after fresh full-file and exact comparator failures in inherited scaffold | Selected proof changes cannot repair frozen challenge generation; preserve authorized atomic boundary | AC2 remains unmet; AC1/AC3 evidence retained |

#### Active Tasks
<!-- Mainline tasks only: each task must directly advance the current round objective and carry routing metadata -->
| Task | Target AC | Status | Tag | Owner | Notes |
|------|-----------|--------|-----|-------|-------|

### Blocking Side Issues
<!-- Only issues that directly block current mainline progress belong here -->
| Issue | Discovered Round | Blocking AC | Resolution Path |
|-------|-----------------|-------------|-----------------|
| [blocking] Fresh full-file build and configured comparator fail in inherited scaffold | 0 | AC2 | Local build: three unknown attribute targets and unsolved root. Comparator request 6ce3add7f60b402b963ac65ad9ce6c3d exits 1 before child comparison, with no success marker. Trusted controller must resolve faithful challenge loading; do not alter frozen context in this worker |

### Queued Side Issues
<!-- Non-blocking issues stay queued and must NOT replace the round objective -->
| Issue | Discovered Round | Why Not Blocking | Revisit Trigger |
|-------|-----------------|------------------|-----------------|
| [queued] TaskCreate/TaskUpdate/TaskList are not exposed tools | 0 | Track task states and required routing in this goal tracker | Tool availability changes |
| [queued] Restore missing bwrap sandbox launcher | 0 | Required commands succeeded through explicit escalation; no environment repair needed for this round | Operator maintenance |
| [queued] Raw comparator log contains eight upstream trailing spaces | 0 | Preserved byte-for-byte for the recorded SHA-256; only this raw log is excluded from staged whitespace checking | Never normalize immutable raw evidence; any display cleanup belongs in a separate derived report |

### Completed and Verified
<!-- Only move tasks here after the reviewer has verified them -->
| AC | Task | Completed Round | Verified Round | Evidence |
|----|------|-----------------|----------------|----------|
| AC1, AC3 | [mainline] Read accepted proof, frozen problem, and pinned references | 0 | pending verification | Read accepted seven-step proof and manifest; rg/inspection confirms group-law fields, precomposition, subtype representation; no existing selected name in pinned project; BitLesson NONE |
| AC1 | [mainline] Implement exact relative group-law rebasing declaration | 0 | pending verification | Existing 117-line single declaration audited against accepted proof; independent simplifier found no warranted changes; no proof edits made |
| AC2, AC3 | [mainline] Audit exact type, pins, and source safety | 0 | pending verification | `round-0-audit.json`: complete frozen child type equal modulo whitespace; all nine package checkouts and both references clean at exact pins; frozen prefix unchanged; only selected theorem in suffix, no forbidden proof tokens |
| AC2, AC3 | [mainline] Inspect selected theorem's transitive axioms | 0 | pending verification | `round-0-axioms.log`: only propext, Classical.choice, Quot.sound. Scratch copy preserves full original source and appends only #print axioms; process still exits 1 on inherited scaffold, so no successful build is claimed |
| AC2 | [blocking] Shared-index changes resolved externally | 0 | pending verification | Observed another round commit 9740a14, then external reset to 296be36; latest status is clean; no index/reset operations performed by this round |
| AC2, AC3 | [mainline] Compile, simplify-review, and audit complete source diff (attempt completed; success gate deferred) | 0 | pending verification | Literal warning-fatal exit 1; source/type/pin checks recorded; simplifier found no warranted changes; no source edits; routing coding → claude, BitLesson NONE |
| AC2 | [mainline] Run exact comparator at committed clean candidate (attempt completed; success gate deferred) | 0 | pending verification | 296be36 before/after, clean; request 6ce3add7f60b402b963ac65ad9ce6c3d exits 1, no success marker; raw log digest in round-0-comparator-result.json; routing coding → claude, BitLesson NONE |
| AC3 | [mainline] Finalize round evidence and return to controller | 0 | pending verification | round-0-summary.md, contract, source audit, reference-use record, build/axiom/comparator logs and results; documentation-only commit; routing coding → claude, BitLesson NONE |

### Explicitly Deferred
<!-- Items here require strong justification -->
| Task | Original AC | Deferred Since | Justification | When to Reconsider |
|------|-------------|----------------|---------------|-------------------|
| [mainline] Achieve warning-clean full-file build and passing exact comparator | AC2 | Round 0 | Both gates fail in preserved inherited context before a successful exact comparison. Repairing frozen commands or the served verifier is outside this selected-node implementation scope; no child proof defect was identified. AC2 remains unmet | Trusted controller resolves the challenge-loading prerequisite, then the configured gates are rerun at an exact clean commit |
| [queued] Independent acceptance, wiki publication, DAG transition, and PR integration | Completion boundary | Round 0 | Explicit outer-controller ownership; this failed author gate grants no acceptance | Successful author gate and return to recursive controller |
