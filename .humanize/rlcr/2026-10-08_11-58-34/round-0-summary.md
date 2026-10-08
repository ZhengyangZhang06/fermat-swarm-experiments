# Round 0 Summary

**Outcome: blocked; no proof acceptance.** The exact selected-node comparator exits 1 while compiling the controller's frozen challenge, before candidate comparison. The isolated child proof passes its warning-fatal type and axiom checks. No Lean source was changed in this round.

## Implementation and scope

The starting branch already contains the sole selected theorem, `Submission.p07_flp_point_equiv_857cd4d38c`, introduced in `8ac90b184237be5f866deac1545609af0e0bfb36` and documented in `eccb2440c4b9010b4c819733095470fb5a4a17ab`. This round reviews and verifies that candidate; it does not treat the existing implementation as an accepted dependency. The frozen proof base is `8cb34c690b020247caaf2f18f9cb6fbab8d526f6`, and the selected node has no children or approved dependencies.

The proof follows all seven accepted steps: forward composition, inverse pullback lift, inverse identities by the two projections, multiplication via subtype extensionality, identity by cancelling an idempotent, repeated sums by induction, and the order action by associativity. Every intermediate fact is local. The complete source diff from the proof base adds exactly this theorem; the original source prefix is byte-for-byte unchanged. The pre-existing root `sorry` remains in the frozen specification and is not used as a solution to this child.

The requested read-only code simplifier reviewed lines 80–144 and found no defect or worthwhile simplification. No source change is justified by that review. This is not the outer independent acceptance review.

## Files and task tracking

- Initialized `goal-tracker.md` with three acceptance criteria and four `[mainline]` tasks, all routed `coding -> claude` as requested.
- Created `round-0-contract.md`, targeting AC1 and AC2.
- Updated this summary with review and reference evidence.
- TaskCreate/TaskUpdate/TaskList are not exposed in this session; task lifecycle is recorded in the goal tracker. No loop state, frozen proof, scaffold, DAG, or protected source file was changed.

## Validation

- Initial worktree: clean at `eccb2440c4b9010b4c819733095470fb5a4a17ab`.
- Snapshot project HEAD: `73257f1e32d99b75813b037f28a5cf45a2db886d`, clean.
- Snapshot mathlib HEAD: `db584cd6d46c92f209a44c0f1c829460d327499d`, clean.
- All nine installed dependency checkouts match `lake-manifest.json` and are clean, including untracked files.
- `lake` was absent from PATH; the pinned Lean 4.33.1 compiler was located at `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin`.
- Warning-fatal command: `PATH=/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin:$PATH lake env lean -DwarningAsError=true Submission.lean`. Exit 1: unknown constants `AlgebraicGeometry.Scheme.Hom.opensMapFinal` (line 13), `GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase` (line 14), and `RegularLocalRingQuotientAscent.dualNumberFst_apply` (line 15); inherited root declaration uses `sorry` (line 22). All four diagnostics concern the byte-for-byte unchanged frozen source prefix. No child-theorem error was reported. This is a failed check, not a warning-clean candidate.
- Exact-node comparator: exit 1 at clean commit `81698cca3ff5c5387d604ab60ee86d2e988ba762`, request `7b0142dd56a241709f70716c7f2a3f3c`. The request packet identified precisely this node and candidate; packet digest `f59369ba62f21902c4bb5bd1ee32c1bcfde19cd1166ce9a0092691c08ab37041`. The verifier failed building `/output/result/challenge/Submission.lean` on the same three unknown constants at lines 13–15. The root `sorry` appeared as a warning in that build. No candidate export or comparison completed, and `Your solution is okay!` was not printed. The exact command from the plan was run with `env -u HF_TOKEN` and only the selected node ID. Neither root nor sibling comparator was run.
- Isolated diagnostic `/tmp/p07-point-equiv-round0-o4lku_rc/CheckNode.lean`: exit 0 with `-DwarningAsError=true` and the pinned project options. This imports the same five Definitions modules, copies the selected theorem verbatim, and checks it against the exact frozen DAG type with `example`. It excludes the broken frozen prefix and root specification, so it is diagnostic evidence only, not acceptance of `Submission.lean`.
- Diagnostic transitive axiom reports for the selected theorem and `CategoryTheory.IsPullback.lift`, `lift_fst`, `lift_snd`, and `hom_ext` each list only `propext`, `Classical.choice`, and `Quot.sound`.
- `git diff 8cb34c6..HEAD --check` passed. Manual review and an added-source scan found no `sorry`, `admit`, new `axiom`, `unsafe`, `native_decide`, `implemented_by`, `run_tac`, or `run_elab` in the theorem addition. No extra named helpers were added. `Submission.lean` SHA-256 is `81d0a9d64dee7d82cd27ac069c5dde7a4617d51a74ca4899b6fe5ef3dfe4002b`.
- The comparator candidate remained committed and clean for the entire request and was confirmed unchanged after exit. A final documentation-only commit records this outcome; it does not represent a successful comparator run at a new SHA. The Lean source is unchanged from the checked candidate.

## Reference use

`reference_use` contains exactly one entry:

```yaml
reference_use:
  - source: local-project
    snapshot: /mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89
    project_commit: 73257f1e32d99b75813b037f28a5cf45a2db886d
    mathlib_commit: db584cd6d46c92f209a44c0f1c829460d327499d
    findings: The pinned APIs support the accepted proof; no existing matching point-equivalence or nsmulPt naturality theorem was found in the searched project Definitions and Submission.lean.
```

All paths below are relative to that absolute snapshot directory:

| Query | Inspected path and finding |
|---|---|
| `IsPullbackVia\|nsmulPt\|def pushPt` | `project/Definitions/Def_CerednikDrinfeld_QMFormalModuleOf.lean:31–43`: pullback square, multiplication and action equations, and level compatibility. `project/Definitions/Def_CerednikDrinfeld_QMModuli.lean:27–48`: `mapPt`, `pushPt` (an abbrev, inspected directly), and recursive `nsmulPt`. |
| `abbrev SchemeHomOver\|def SchemeHomOver` | `project/Definitions/Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier.lean:23–24`: subtype of morphisms with the required base equation. The earlier query using only `def SchemeHomOver` had no match. |
| `def SchemeHomOver\|mul_assoc\|inv_mul_cancel\|one_mul\|structure RelativeGroupLaw` | `project/Definitions/Def_AlgebraicGeometry_RelativeGroupLaw.lean:78–104`: the explicit multiplication, identity, inverse, associativity, identity and cancellation fields used by the local argument. |
| `noncomputable def lift\|theorem lift_fst\|theorem lift_snd\|hom_ext` | `mathlib/Mathlib/CategoryTheory/Limits/Shapes/Pullback/IsPullback/Defs.lean:106–127`: lift and uniqueness matched; direct inspection also found `lift_fst` and `lift_snd`, which are declared as lemmas. |
| `nsmulPt.*natural\|theorem.*nsmulPt\|lemma.*nsmulPt\|p07_flp_point_equiv\|pullback_point_equiv` | Searched `project/Definitions` and `project/Submission.lean`: no matches (rg exit 1). |

Compatibility was checked against the actual manifest, the installed clean dependency revisions, and the selected node's frozen DAG type. Diagnostic elaboration and transitive axiom checks passed; acceptance still requires the configured comparator. No network search was used, and no reference source was modified.

## Remaining items

AC2 is unmet. The controller must resolve the frozen challenge build context before exact-node acceptance can succeed. No candidate-local proof change can repair the separately copied frozen challenge, and changing that controller-owned contract is outside this selected-node implementation. T3 and T4 remain explicitly blocked; T1 and T2 are recorded as completed pending independent verification. The reference audit, contract and final handoff evidence satisfy the documentation work for AC3, without implying theorem acceptance.

The independent reviewer comparator rerun, theorem-wiki publication, issue/PR integration and DAG `proved` transition remain outer-controller tasks. No decomposition or proof rewrite was attempted. No retry of the identical failed comparator is justified until its frozen-source blocker changes.

The theorem catalogue for this node consists solely of `Submission.p07_flp_point_equiv_857cd4d38c`. The only acceptance issue found is the frozen-source build failure above; the read-only simplifier found no selected-proof defect.

## BitLesson Delta

Action: none
Lesson ID(s): NONE
Notes: The BitLesson file has no lesson entries; NONE applies to every task. No lesson was added or updated.
