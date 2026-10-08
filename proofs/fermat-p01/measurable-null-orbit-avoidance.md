# Measurable null-orbit avoidance

Tracked declaration: `Submission.f036cc6b1f_pc_ed_aoi_null_orbit` in
`Submission.lean`. Its frozen type is:

```lean
∀ s : Set UpperHalfPlane, MeasurableSet s →
  (MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane) s = 0 →
  ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane),
    ∀ a : Matrix.SpecialLinearGroup (Fin 2) ℤ, a • z ∉ s
```

This atomic node has no approved child dependencies. The existing proof is retained;
the Round 0 advisory code-simplifier review found no changes warranted.

## Correspondence with the accepted proof

The accepted handoff is
`/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/nodes/root-petersson-core-good-hecke-a1-effective-domain-a1-ae-orbit-interi-9760a4d8a3/parent-supplied-natural-proof.md`.

1. The local `Countable` instance unfolds `Matrix.SpecialLinearGroup` and `Matrix`
   to the determinant-one subtype of four integer entries (accepted step 3).
2. `MeasureTheory.ae_all_iff.mpr` combines the countably many full-measure
   complements of bad preimages (accepted steps 4–5).
3. For each modular matrix, `change` identifies its action with the real GL action
   through `Matrix.SpecialLinearGroup.mapGL ℝ` (accepted steps 1–2).
4. `SMulInvariantMeasure.measure_preimage_smul` and the prescribed nullness give
   nullness of the preimage. `measure_eq_zero_iff_ae_notMem.mp` gives its
   almost-everywhere complement (accepted steps 2 and 5).

All named lemmas used are existing pinned library declarations. The proof adds no
named helpers, assumptions, axioms, or unsafe mechanisms. The inherited root
specification, imports, and disabled attributes are unchanged.

## Reference use

`reference_use` has one source: **local-project**. The snapshot root is
`/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb`.
Its `manifest.json` pins project `61b5f85556ac71631ccad822e0694511234f7132`
and mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`.
The following are actual paths relative to that root, searched with `rg` and inspected:

| Path | Query | Finding |
| --- | --- | --- |
| `mathlib/Mathlib/LinearAlgebra/Matrix/SpecialLinearGroup.lean:70` | `def SpecialLinearGroup\|countable\|Countable` | Determinant-one matrix subtype; countability is inferred after unfolding. |
| `mathlib/Mathlib/Analysis/Complex/UpperHalfPlane/MoebiusAction.lean:285` | `SLAction\|mapGL` | The modular action is defined by composition with `mapGL ℝ`. |
| `mathlib/Mathlib/Analysis/Complex/UpperHalfPlane/Topology.lean:84` | `instContinuousGLSMul` | The real GL action is continuous. |
| `mathlib/Mathlib/Analysis/Complex/UpperHalfPlane/Measure.lean:89` | `SMulInvariantMeasure\|measure_preimage_smul\|volume_eq` | Hyperbolic volume is invariant under the real GL action. |
| `mathlib/Mathlib/MeasureTheory/Group/Defs.lean:59` | `class SMulInvariantMeasure\|measure_preimage_smul` | Invariance gives the exact measurable-preimage identity used. |
| `mathlib/Mathlib/MeasureTheory/Group/Action.lean` | `measure_preimage_smul\|measurePreserving_smul` | General invariant-action infrastructure; no new helper is needed. |
| `mathlib/Mathlib/MeasureTheory/OuterMeasure/AE.lean:91` | `ae_all_iff\|measure_eq_zero_iff_ae_notMem` | Nullness/complement equivalence and countable almost-everywhere quantification. |
| `project/Definitions`, `project/P2M` | `f036cc6b1f_pc_ed_aoi_null_orbit\|ae_all_iff\|measure_preimage_smul` | No matches. |

## Validation scope

The warning-fatal harness copies the unchanged imports and disabled attributes,
then the selected theorem verbatim. It omits the unrelated inherited root
placeholder, checks the literal frozen type using an anonymous `example`, and
prints the selected declaration's transitive axioms. The harness and logs are
local round evidence, not additional submitted declarations.

Round 0 local results:

- All nine installed dependencies are clean at the exact manifest revisions.
  Seven referenced mathlib files, 90 project files, the toolchain, and the manifest
  match the pinned snapshot byte for byte.
- The complete diff from the dispatch base adds only this theorem to the Lean
  sources. The frozen prefix remains byte-identical; source-safety and whitespace
  checks found no candidate defect.
- Building the imports with `lake --no-cache --wfail build
  Definitions.Def_ModularForm_HeckeOperatorForms` exits 1 because of existing
  deprecation/style warnings in pinned files. The imports themselves elaborate.
- Running the selected-node harness with `-DwarningAsError=true` reports unknown
  constants in the inherited `attribute [-instance]` and `attribute [-simp]`
  commands: `FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions`
  and `FreyPackage.ModMCarrier.coe_rescaleLin_apply`. These names have no matches
  in the pinned project `Definitions` and `P2M` trees. No frozen directive was edited.
- Despite those header errors, the axiom report for the selected proof is
  `[propext, Classical.choice, Quot.sound]`. This does **not** make the failed
  full-header check a passing build or comparator acceptance.

Detailed local evidence is in
`.humanize/rlcr/2026-10-08_12-49-35/{compatibility-audit.json,source-audit.json,dependency-build.log,selected-node-build.log}`.

Only the configured selected-node comparator can establish machine acceptance of
the committed candidate. The independent reviewer comparator, issue/PR lifecycle,
wiki publication, and DAG transition remain outer-controller responsibilities.

## Revalidation started 2026-10-08 14:00:06 UTC

The selected implementation is unchanged. A fresh advisory simplifier review
found no warranted simplification: the explicit countability witness, restricted
real GL action, measurable-preimage identity, and countable AE quantifier match
the accepted proof directly. This source review does not establish acceptance.

Fresh compatibility checks found all nine dependencies clean at their manifest
revisions. All 98 sources in `Definitions`, `P2M`, and `Theorems`, the seven
referenced mathlib files, `lean-toolchain`, and `lake-manifest.json` match the
pinned snapshot byte for byte. The selected proposition also matches the literal
frozen type after whitespace normalization. The full Lean diff from dispatch
`eae1c3e` adds only the selected theorem; the frozen prefix is byte-identical,
and the added proof contains no prohibited constructs.

Fresh `rg` searches in the snapshot's `project/Definitions` and `project/P2M`
found no matches for either
`instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions`
or `coe_rescaleLin_apply`. These names occur in the inherited frozen attribute
directives, so changing this theorem's proof cannot supply them. The directives
and pinned sources remain unchanged. Likewise, the selected identifier is absent
from both `project` and `mathlib/Mathlib`; this implementation uses library
infrastructure, not an upstream proof of the selected node.

The fresh warning-fatal dependency build exited 1 on inherited deprecation/style
warnings. The selected-node harness also exited 1, reporting exactly the two
unknown frozen attribute constants above. It nevertheless printed transitive
axioms `[propext, Classical.choice, Quot.sound]` for the selected theorem and all
six audited library declarations. These axiom reports do not turn either failed
command into acceptance. The harness retains every frozen import and attribute
directive while omitting only the unrelated root theorem, and checks the literal
child proposition with an anonymous example.

Fresh command outputs, source and compatibility audits, and the eventual exact
committed-candidate comparator result are recorded under
`.humanize/rlcr/2026-10-08_14-00-06/`. Consult `round-0-summary.md` there for the
author's final outcome. An unresolved frozen-context build error or nonzero
comparator result must remain a blocker, regardless of the proof's axiom report.

## Round initialized 2026-10-08 15:15:08 UTC

Fresh review retains the selected theorem without source changes. The requested
advisory simplifier again found no warranted change; this is not acceptance.
The accepted Markdown/JSON proof and child handoff match the immutable dispatch
copies byte for byte. The literal proposition and frozen header are unchanged,
and the complete Lean diff from `eae1c3e7aa1a3c40f973844f73289a6f5bc76fc4`
still adds only this selected declaration, without prohibited mechanisms.

All nine dependencies are clean and match their manifest revisions. Fresh byte
comparisons match all 98 project Lean sources, nine relevant mathlib files,
`lean-toolchain`, and `lake-manifest.json` to the pinned local-project snapshot.
The additional countability references are `Mathlib/Data/Countable/Defs.lean:89`
(subtypes) and `Mathlib/Data/Countable/Basic.lean:146` (finite function spaces).
Targeted searches again find neither the selected declaration in the snapshot
nor the two missing frozen attribute constants in `project/Definitions` and
`project/P2M`.

The fresh warning-fatal dependency build exits 1 on inherited deprecation/style
warnings. Current exact-type harness results, axiom reports, and the committed
candidate's exact-node comparator outcome are recorded in
`.humanize/rlcr/2026-10-08_15-15-08/round-0-summary.md` and its adjacent evidence
files. No frozen source or dependency was altered to avoid a validation failure.
