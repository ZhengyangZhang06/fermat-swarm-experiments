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
Implement only `Submission.p06_9e0f5043ff_dlen_scalar_quotient` with the frozen selected-node type and accepted natural proof, and return a warning-clean, cleanly committed candidate that passes the exact selected-node comparator to the recursive controller.

Source plan: /mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-local-norm-order-a1-dvr-determinant-length-a1-scalar-quotient-le-9dc69f4859/rlcr-plan-v2.md

### Acceptance Criteria
<!-- Each criterion must be independently verifiable -->
<!-- The builder must extract or define these in Round 0 -->

1. AC1: The sole new named theorem has the exact frozen type, uses no new axioms or placeholders, and builds with warnings fatal against pinned dependencies.
2. AC2: The complete source diff is audited, the candidate is committed with a clean worktree, and the exact selected-node comparator exits zero with `Your solution is okay!`.
3. AC3: The accepted proof and frozen problem are read, local snapshot searches and provenance are recorded with exactly one `reference_use` entry (`local-project`), and the round artifacts accurately hand control back to the outer controller.

---

## MUTABLE SECTION
<!-- Update each round with justification for changes -->

### Plan Version: 1 (Updated: Round 2 recovery)

#### Plan Evolution Log
<!-- Document any changes to the plan with justification -->
| Round | Change | Reason | Impact on AC |
|-------|--------|--------|--------------|
| 0 | Initialize from the supplied selected-node implementation plan | Preserve the exact atomic boundary and outer-controller completion boundary | AC1–AC3 |
| 0 | Retain and verify the existing candidate at `ee0110eeb25dd35b82b7086bee294c6589a4f29c` | Worktree inspection found the selected theorem already implemented; this is candidate evidence only, not proof acceptance | Same AC1–AC3; no decomposition or contract change |
| 0 | Return an explicit input blocker after exact comparator exit 1 | Immutable challenge compilation fails on three unavailable attribute constants before solution comparison; repairing that input exceeds selected-node scope | AC1 and AC2 unmet; no acceptance claimed; AC3 artifacts complete pending review |
| 1 | Investigate the existing verification request's input and checker provenance | Review confirms source integrity but requires inspectable packet, checker identity, and endpoint authorization; no audit-only comparator rerun requested | Advance AC2 and AC3 without changing the immutable goal or frozen theorem |
| 1 | Record precise controller questions instead of fabricating unavailable remote evidence | Failed requests are ineligible for the mounted evidence exporter; local runtime copies cannot establish the actual remote checker | B1 and B2 remain open; passing acceptance still deferred, with a concrete read-only evidence-export request |
| 2 | Recover the original acceptance objective; stop substituting audit artifacts for mainline movement | Two reviews found unchanged B1/B2. The independent frozen challenge needs a controller-owned repair, not another proof rewrite or audit-only commit | Target AC1 and AC2 directly. Perform one bounded check for an authoritative unblock; if absent, report no credible authorized worker-side implementation path |
| 2 | Recovery prerequisite check found no worker-executable path | New exporter `f116f3cae2f8` also rejects failed requests; exact request export remains absent and relevant runtime/input files are unchanged | AC1/AC2 remain unmet. Required workflow records only; no extra audit bundle, proof rewrite, or unchanged comparator rerun |

#### Active Tasks
<!-- Mainline tasks only: each task must directly advance the current round objective and carry routing metadata -->
| Task | Target AC | Status | Tag | Owner | Notes |
|------|-----------|--------|-----|-------|-------|

### Blocking Side Issues
<!-- Only issues that directly block current mainline progress belong here -->
| Issue | Discovered Round | Blocking AC | Resolution Path |
|-------|-----------------|-------------|-----------------|
| Sandbox launcher cannot find bubblewrap | 0 | AC1, AC2 | Execute required shell commands through the escalation mechanism; initial read succeeded |
| [blocking] B1 Frozen attributes name unavailable constants | 0 | AC1, AC2 | Both warning-fatal check and configured comparator exit 1 at `AlgebraicCurve.IsCurveOver.instNontrivialKaehler`, `AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply`, and `AlgebraicCurve.SemilinearAut.coe_torsion_smul`. Comparator fails in the immutable challenge before solution comparison. Controller must reconcile the frozen context. Tag: coding; Owner: claude; BitLesson: NONE. |
| [blocking] B2 Existing request packet, remote checker identity, and endpoint authorization are not locally established | 1 | AC2, AC3 | Local inspection completed. Exporter accepts only verified exit-zero operations, so this failed request is absent. The inspected broker source has no artifact GET route; the actual request's broker implementation remains unverified. Controller must export retained failed-request inputs/checker identities and bind endpoint authorization. Local read-only mounts and deployment notes are supporting observations only. Remaining question tag: analyze; Owner: codex. BitLesson: NONE. |

### Queued Side Issues
<!-- Non-blocking issues stay queued and must NOT replace the round objective -->
| Issue | Discovered Round | Why Not Blocking | Revisit Trigger |
|-------|-----------------|------------------|-----------------|
| TaskCreate/TaskUpdate/TaskList are not exposed by this session | 0 | The required task metadata and lifecycle can be maintained in this tracker | If the Task tools become available, mirror T1–T4 there |
| Inherited style/deprecation warnings in DivisorPushPull and PlacesOverDVR | 0 | They are outside the selected declaration, and the exact comparator stops on frozen attribute errors | Controller-owned upstream maintenance after the frozen input blocker is addressed |

### Completed and Verified
<!-- Only move tasks here after the reviewer has verified them -->
| AC | Task | Completed Round | Verified Round | Evidence |
|----|------|-----------------|----------------|----------|
| AC1, AC2 | [mainline] R2-T1 Check for a newly available authoritative verification path (coding; claude) | 2 | pending verification | Bounded prerequisite check completed; no authorized repair or failed-request export found. New exporter `f116f3cae2f8` still excludes failures. This is a negative feasibility result, not mainline acceptance progress. |
| AC2, AC3 | [mainline] R1-T1 Inspect existing request and runtime evidence (coding; claude) | 1 | pending verification | Wrapper override and all runtime evidence are mounted read-only. Deployment notes document the port 8849 rollout. Exact failed request absent from `/runtime/review-evidence`; exporter explicitly accepts only verified exit-zero requests. Inspected broker source has only `/issues` and `/health` GET routes; it is not authenticated as the actual remote implementation. No network request or new verification started. |
| AC2 | [mainline] R1-T2 Establish exact controller-owned decisions (coding; claude) | 1 | pending verification | B1 cannot be fixed by candidate-only edits: failure is in the separate frozen challenge. B2 needs a controller export of this failed request's packet, operation receipt, source hashes, and remote checker identities; the available exporter forbids failed requests. Existing deployment notes support port 8849's intended role but do not bind this request to an authorized checker. Questions remain analyze/codex in the summary. |
| AC2, AC3 | [mainline] R1-T3 Save reviewable provenance and finalize handoff (coding; claude) | 1 | pending verification | Commit `bd0e1c6e8ea910f9a98e0933d7ab146e5390fcd2` archives the original failed output, hashes observed evidence, and documents unresolved controller questions. Source unchanged; clean worktree. Simplifier review incorporated one provenance wording correction. Exact checked candidate remains `dbe4787`; no new comparator run or acceptance claimed. |
| AC1, AC3 | [mainline] T1 Read frozen inputs and research pinned local references | 0 | pending verification | Read frozen problem and accepted handoff. Searched local-project snapshot; inspected DVR factorization/length and place order definitions. Four reused interface files match byte-for-byte; all nine dependency revisions match and have clean tracked sources. |
| AC1 | [mainline] T2 Implement the exact scalar quotient theorem | 0 | pending verification | Existing implementation retained with one theorem docstring added. Exact type preserved; only pinned upstream declarations reused. Read-only simplifier review recommends retaining it and confirms sole tracked theorem and unchanged frozen prefix. |
| AC3 | [mainline] T4 Finalize artifacts and return to controller | 0 | pending verification | Goal tracker, round contract, and summary finalized with exactly one local-project reference entry and BitLesson NONE. Candidate `dbe478749afa15b2ac4a65d23df7e64ff2899735` is clean and committed. Comparator request `af0506aaa3f0407db2b2eedd0fe9b38f` exited 1; no proof acceptance claimed. Tag: coding; Owner: claude. |

### Explicitly Deferred
<!-- Items here require strong justification -->
| Task | Original AC | Deferred Since | Justification | When to Reconsider |
|------|-------------|----------------|---------------|-------------------|
| [mainline] T3 Obtain warning-clean and exact-comparator acceptance (coding; claude; BitLesson NONE) | AC1, AC2 | Round 0 | Audit and clean candidate commit completed; both required verification invocations were run and failed on B1. The immutable challenge fails independently of candidate proof changes. Preserve frozen inputs and return the evidence to the controller; successful verification cannot honestly be reported. | Controller reconciles the frozen import/attribute context and provides an authorized runnable contract. |
| [blocking] Supply actual failed-request packet/checker/authorization evidence (analyze; codex; BitLesson NONE) | AC2, AC3 | Round 1 | Repository inspection found only successful-request exports and unauthenticated copies of possible runtime sources. Local observations are committed, but cannot reconstruct trusted remote provenance. The worker must not modify controller exporters, receipts, or verdicts to manufacture availability. | Controller exposes the retained failed request through a read-only export with request-specific identity and authorization. |
| [mainline] R2-T2 Apply authorized reconciliation and pass selected-node gates (coding; claude; BitLesson NONE) | AC1, AC2 | Round 2 | Recovery check found no controller-authorized repair for the independent frozen challenge and no actual failed-request provenance export. Repeating unchanged checks or modifying the frozen contract would not satisfy the original plan. | Controller supplies the concrete B1/B2 prerequisites listed in the Round 2 summary. |
