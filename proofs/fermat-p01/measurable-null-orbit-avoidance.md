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
