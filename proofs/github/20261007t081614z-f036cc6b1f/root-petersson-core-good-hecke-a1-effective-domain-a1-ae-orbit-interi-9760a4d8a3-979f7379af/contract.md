<!-- theorem-id: fermat-p01/root.petersson_core_good_hecke-a1.effective_domain-a1.ae_orbit_interior-a1.measurable_null_orbit_avoidance-a1 -->

## Theorem `Submission.f036cc6b1f_pc_ed_aoi_null_orbit`

Let G = SL₂(ℤ) act on ℍ by Möbius transformations, and equip ℍ with its Borel measurable structure and hyperbolic measure μ = dx dy/y². For every measurable set S ⊆ ℍ satisfying μ(S) = 0, for μ-almost every z ∈ ℍ and every a ∈ G, one has a • z ∉ S.

Node: `root.petersson_core_good_hecke-a1.effective_domain-a1.ae_orbit_interior-a1.measurable_null_orbit_avoidance-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/1

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/102

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.f036cc6b1f_pc_ed_aoi_null_orbit`

```lean
∀ s : Set UpperHalfPlane, MeasurableSet s → (MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane) s = 0 → ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane), ∀ a : Matrix.SpecialLinearGroup (Fin 2) ℤ, a • z ∉ s
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
- Child DAG node: `root.petersson_core_good_hecke-a1.effective_domain-a1.ae_orbit_interior-a1.measurable_null_orbit_avoidance-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix a measurable set S ⊆ ℍ with μ(S) = 0. For each a ∈ G, define Tₐ(z) = a • z and Bₐ = Tₐ⁻¹(S).
2. Let g be the image of a under Matrix.SpecialLinearGroup.mapGL ℝ. By the definition UpperHalfPlane.SLAction in the pinned MoebiusAction.lean, Tₐ(z) = g • z. The GL₂(ℝ) action maps are continuous by UpperHalfPlane.instContinuousGLSMul, so Tₐ is measurable and Bₐ is measurable. The invariant-measure instance in UpperHalfPlane/Measure.lean states that the GL₂(ℝ) action preserves hyperbolic measure. Applying its measurable-preimage identity to g and S gives μ(Bₐ) = μ(S) = 0.
3. The map sending a ∈ SL₂(ℤ) to its four integer matrix entries is injective, since equality of all entries implies equality of matrices and hence equality in the determinant-one subtype. A finite product of countable sets is countable, so ℤ⁴ is countable and therefore G is countable. In the pinned definitions, this is precisely the determinant-one subtype of the function space Fin 2 → Fin 2 → ℤ.
4. Define N = ⋃ₐ∈G Bₐ. This is a countable union of measurable sets, so it is measurable. Countable subadditivity and step 2 give μ(N) ≤ Σₐ∈G μ(Bₐ) = 0. Nonnegativity then yields μ(N) = 0.
5. If z ∉ N, then z ∉ Bₐ for every a ∈ G. By the definition of Bₐ, this means a • z ∉ S for every a. Since N has measure zero, its complement has full μ-measure, proving the required simultaneous almost-everywhere assertion.

## Key steps

1. Form the preimage of the prescribed null set under each modular action map.
2. Restrict GL₂(ℝ) continuity and measure invariance to show every preimage is measurable and null.
3. Prove SL₂(ℤ) countable through its four integer entries.
4. Remove the countable union of all preimages.
5. Read nonmembership in that union as avoidance by every modular translate.

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

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/274

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
