<!-- theorem-id: fermat-p01/root.petersson_core_good_hecke-a1.effective_domain-a1.ae_orbit_interior-a1.standard_boundary_null-a1 -->

## Theorem `Submission.f036cc6b1f_pc_ed_aoi_boundary_null`

Let ℍ = {x + iy ∈ ℂ : y > 0} carry its Borel measurable structure and hyperbolic measure μ = dx dy/y². Define F₀ = {z ∈ ℍ : 1 ≤ |z|² and |Re z| ≤ 1/2} and F₀° = {z ∈ ℍ : 1 < |z|² and |Re z| < 1/2}. Then E = F₀ \ F₀° is measurable and μ(E) = 0.

Node: `root.petersson_core_good_hecke-a1.effective_domain-a1.ae_orbit_interior-a1.standard_boundary_null-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/1

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/102

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.f036cc6b1f_pc_ed_aoi_boundary_null`

```lean
MeasurableSet (ModularGroup.fd \ ModularGroup.fdo) ∧ (MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane) (ModularGroup.fd \ ModularGroup.fdo) = 0
```

### Frozen project context

`Fermat/Thm_CuspForm_span_heckeTLin_eigen_eq_top.lean` at `61b5f85556ac71631ccad822e0694511234f7132` supplies the original imports, definitions and root contract. Child hypotheses are stated above; prerequisite declarations are linked in their issues.

```lean
/-
Copyright 2026 Anthropic, PBC. Licensed under Apache-2.0; see LICENSE.
Source: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_CuspForm_span_heckeTLin_eigen_eq_top.lean
Modified: replaced the proof with sorry and removed P2M proof imports.
Requires the upstream Definitions modules and their dependencies.
-/

import Definitions.Def_ModularForm_HeckeOperatorForms
attribute [-instance] FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2
attribute [-simp] FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero

theorem CuspForm.span_heckeTLin_eigen_eq_top (M : ℕ) [NeZero M] :
    Submodule.span ℂ {v : CuspForm (CongruenceSubgroup.Gamma0 M) 2 |
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M), ∃ c : ℂ,
        CuspForm.heckeTLin 2 hℓ hℓM v = c • v} = ⊤ := by
  sorry
```

## Natural-language proof

Reviewed mathematical argument; formal verification state: `proved`.

# Parent-supplied natural-language proof

- Parent DAG node: `root.petersson_core_good_hecke-a1.effective_domain-a1.ae_orbit_interior-a1`
- Child DAG node: `root.petersson_core_good_hecke-a1.effective_domain-a1.ae_orbit_interior-a1.standard_boundary_null-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Put E = F₀ \ F₀°. The functions z ↦ |z|² and z ↦ |Re z| are continuous on ℍ. Their non-strict inequalities define a closed set F₀, and their strict inequalities define an open set F₀°. Thus E is Borel measurable. These facts are ModularGroup.isClosed_fd and ModularGroup.isOpen_fdo in the pinned Modular.lean.
2. Let z = x + iy belong to E. Then 1 ≤ x² + y² and |x| ≤ 1/2. If both inequalities were strict, z would belong to F₀°, contradicting z ∈ E. Hence x² + y² = 1 or |x| = 1/2. In the latter case x = 1/2 when x ≥ 0, and x = -1/2 when x < 0. Consequently the image of E in ℂ is contained in the union of C = {x + iy : x² + y² = 1}, L₊ = {x + iy : x = 1/2}, and L₋ = {x + iy : x = -1/2}.
3. Identify ℂ with ℝ × ℝ by z ↦ (Re z, Im z). This identification preserves Lebesgue measure, as established by Complex.volume_preserving_equiv_real_prod. For any real c, the vertical line x = c corresponds to {c} × ℝ. The product-measure formula gives its measure as λ({c})λ(ℝ) = 0, since real Lebesgue measure λ assigns zero to singletons and 0 times infinity is zero in the nonnegative extended reals. Thus both L₊ and L₋ have planar measure zero.
4. The real-coordinate image C′ = {(x,y) : x² + y² = 1} of C is closed, hence measurable. Fix x. Its vertical section is Sₓ = {y : x² + y² = 1}. If Sₓ is empty, its measure is zero. Otherwise choose y₀ ∈ Sₓ. For every y ∈ Sₓ, subtraction of the two defining equations yields y² - y₀² = 0, so (y - y₀)(y + y₀) = 0. Therefore y = y₀ or y = -y₀. Thus Sₓ is contained in a two-element set and has real Lebesgue measure zero. Tonelli's null-section consequence, MeasureTheory.Measure.measure_prod_null_of_ae_null, now gives product measure zero for C′. The measure-preserving identification gives planar measure zero for C.
5. By finite subadditivity, C ∪ L₊ ∪ L₋ has planar measure zero. The containment in step 2 and monotonicity therefore show that the image of E in ℂ has planar measure zero.
6. UpperHalfPlane.volume_eq_lintegral expresses μ(E) as the nonnegative integral over that image of the density (1/|Im z|)². The restriction of planar measure to a null set is the zero measure, so this integral is zero. Hence μ(E) = 0. Together with step 1 this proves both asserted conclusions.

## Key steps

1. Use continuity to prove measurability of F₀ \ F₀°.
2. Contain its complex image in the unit circle and two vertical lines.
3. Prove vertical-line nullness by the product-measure formula.
4. Prove circle nullness from finite vertical sections and Tonelli.
5. Transfer planar nullness to hyperbolic nullness using the density formula.

## Reference use

### local-project

Queries:
- `isClosed_fd|isOpen_fdo|def fd|def fdo|volume|measure|ae_|boundary`
- `SLAction|mapGL|instContinuousGLSMul|continuous.*smul|smul_eq`
- `fd.*fdo|fdo.*fd|boundary.*(null|zero)|volume.*fd|fd.*volume`
- `measure_prod_null_of_ae_null|volume_preserving_equiv_real_prod|measure_preimage_fst|measure_sphere|sphere.*zero`
- `measure_preimage_smul|measurePreserving_smul|ae_smul|quasiMeasurePreserving_smul`
- `ae_all_iff|ae_iff|theorem ae_notMem`
- `structure SpecialLinearGroup|def SpecialLinearGroup|val_injective|coe_injective|theorem ext|lemma ext|Countable`
- `f036cc6b1f_pc_ed_aoi_boundary_null|f036cc6b1f_pc_ed_aoi_null_orbit`
- `git -C .lake/packages/mathlib rev-parse HEAD`
- `git -C .lake/packages/mathlib status --porcelain`
- `#synth MeasureTheory.MeasureSpace UpperHalfPlane`
- `#synth SMul (Matrix.SpecialLinearGroup (Fin 2) ℤ) UpperHalfPlane`
- `#check (inferInstanceAs (Countable { A : Fin 2 → Fin 2 → ℤ // Matrix.det A = 1 }) : Countable (Matrix.SpecialLinearGroup (Fin 2) ℤ))`
- `#print axioms UpperHalfPlane.volume_eq_lintegral`
- `#print axioms UpperHalfPlane.instSMulInvariantMeasureGeneralLinearGroupFinOfNatNatRealVolume`
- `#print axioms MeasureTheory.Measure.measure_prod_null_of_ae_null`
- `#print axioms Complex.volume_preserving_equiv_real_prod`
- `#print axioms MeasureTheory.ae_all_iff`

Files inspected:
- `.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/problem.md`
- `.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/dag.json`
- `.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/manifest.json`
- `.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/NumberTheory/Modular.lean`
- `.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/Analysis/Complex/UpperHalfPlane/Measure.lean`
- `.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/Analysis/Complex/UpperHalfPlane/Topology.lean`
- `.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/Analysis/Complex/UpperHalfPlane/MoebiusAction.lean`
- `.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/Complex.lean`
- `.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/MeasureTheory/Group/Action.lean`
- `.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/MeasureTheory/OuterMeasure/AE.lean`
- `.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/LinearAlgebra/Matrix/SpecialLinearGroup.lean`
- `.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/Data/Countable/Defs.lean`
- `.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/project/Definitions`
- `.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/project/P2M`
- `.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/nodes/root-petersson-core-good-hecke-a1-effective-domain-a1-ae-orbit-interior-a1/decomposition-checks-v1/FrozenTypesFinal.lean`
- `.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/nodes/root-petersson-core-good-hecke-a1-effective-domain-a1-ae-orbit-interior-a1/decomposition-checks-v1/FrozenTypesFinal.log`
- `.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/nodes/root-petersson-core-good-hecke-a1-effective-domain-a1-ae-orbit-interior-a1/decomposition-checks-v1/CompatibilityFinal.json`

The snapshot pins project 61b5f85556ac71631ccad822e0694511234f7132 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. Modular.lean supplies the exact domain definitions and their closed/open properties. Measure.lean supplies the hyperbolic density formula and GL₂(ℝ) invariance; MoebiusAction.lean and Topology.lean identify the restricted SL₂(ℤ) action and its continuity. Prod.lean and Lebesgue/Complex.lean justify planar nullness through null sections and the measure-preserving real-coordinate identification. Group/Action.lean and OuterMeasure/AE.lean supply invariant preimages and countable almost-everywhere quantification. The targeted search in project/Definitions and project/P2M found no boundary-null helper. Neither proposed identifier occurs in the active DAG or searched declarations. Both frozen child expressions elaborate through literal import Submission; the final check exits 0. Instance inspection confirms the hyperbolic MeasureSpace and UpperHalfPlane.SLAction. Countability requires explicitly unfolding both SpecialLinearGroup and Matrix; its witness also checks. All nine installed dependencies are clean and pinned; twenty project sources and eight mathlib sources were checked against the recorded snapshot. The thirteen audited infrastructure declarations use only propext, Classical.choice, Quot.sound, or no axioms. These are compatibility checks, not comparator acceptance of either proposed theorem.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/498

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
