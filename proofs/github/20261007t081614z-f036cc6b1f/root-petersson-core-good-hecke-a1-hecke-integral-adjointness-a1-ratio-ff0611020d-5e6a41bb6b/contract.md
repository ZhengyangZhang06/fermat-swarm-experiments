<!-- theorem-id: fermat-p01/root.petersson_core_good_hecke-a1.hecke_integral_adjointness-a1.rational_slash_transfer-a1 -->

## Theorem `Submission.f036cc6b1f_pc_hi_rational_slash`

Let Γ and Δ be finite-index subgroups of SL₂(ℤ), interpreted in GL₂(ℝ) by the canonical embedding ι. Let A ∈ GL₂(ℝ) have positive determinant and rational entries. Assume Aι(δ)A⁻¹ ∈ ι(Γ) for every δ ∈ Δ. For every f ∈ CuspForm Γ 2, there exists g ∈ CuspForm Δ 2 whose underlying function is the weight-two slash f|₂A.

Node: `root.petersson_core_good_hecke-a1.hecke_integral_adjointness-a1.rational_slash_transfer-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/1

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/33

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.f036cc6b1f_pc_hi_rational_slash`

```lean
∀ (Γ Δ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex] [Δ.FiniteIndex] (A : Matrix.GeneralLinearGroup (Fin 2) ℝ), 0 < (A.det : ℝ) → (∀ i j : Fin 2, ∃ q : ℚ, A i j = (q : ℝ)) → (∀ δ : Matrix.SpecialLinearGroup (Fin 2) ℤ, δ ∈ Δ → A * Matrix.SpecialLinearGroup.mapGL ℝ δ * A⁻¹ ∈ (Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ))) → ∀ f : CuspForm Γ 2, ∃ g : CuspForm Δ 2, (g : UpperHalfPlane → ℂ) = SlashAction.map (2 : ℤ) A (f : UpperHalfPlane → ℂ)
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

- Parent DAG node: `root.petersson_core_good_hecke-a1.hecke_integral_adjointness-a1`
- Child DAG node: `root.petersson_core_good_hecke-a1.hecke_integral_adjointness-a1.rational_slash_transfer-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Write ι for the canonical embedding into GL₂(ℝ). Every finite-index subgroup Λ of SL₂(ℤ) has exactly the rational cusps. Indeed, for any σ ∈ SL₂(ℤ), finiteness of the coset space implies that some positive power of σTσ⁻¹ belongs to Λ, where T = ((1,1),(0,1)). This power is noncentral parabolic and fixes σ∞. Conversely, a noncentral parabolic integer matrix ((a,b),(c,d)) fixes infinity if c = 0, and if c ≠ 0 its unique fixed point is (a-d)/(2c), which is rational. Finally, every rational projective point is σ∞ for some σ ∈ SL₂(ℤ): choose a primitive integer column representing the point and complete it to determinant one using Bézout. Apply these facts to both Γ and Δ. They are also expressed by the pinned arithmetic-subgroup cusp lemmas in Mathlib/NumberTheory/ModularForms/Cusps.lean.
2. Define u = f|₂A. For δ ∈ Δ, put h = Aι(δ)A⁻¹ ∈ ι(Γ). Slash composition and the Γ-invariance of f give u|₂ι(δ) = f|₂(Aι(δ)) = (f|₂h)|₂A = f|₂A = u. This proves the required Δ-invariance.
3. The slash formula is u(z) = det(A)(cz+d)⁻² f(Az), with c,d the bottom row of A. The denominator never vanishes on the upper half-plane, and the positive-determinant Möbius transformation A maps that half-plane holomorphically to itself. Thus u is holomorphic. This is precisely the positive-determinant case of the pinned MDifferentiable.slash lemma.
4. Let x be any cusp of Δ. By step 1, choose σ ∈ SL₂(ℤ) with σ∞ = x. Since A has rational entries and is invertible, Aσ∞ is a rational projective point. Choose ρ ∈ SL₂(ℤ) carrying infinity to Aσ∞. Then B = ι(ρ)⁻¹Aι(σ) fixes infinity, so B = ((a,b),(0,d)). Invertibility gives a,d ≠ 0, and det(B) = det(A) > 0 gives a/d > 0.
5. The point ρ∞ is a cusp of Γ by step 1. Hence the cusp condition on f gives f|₂ι(ρ) tending to zero as the imaginary part tends to infinity. Slash composition and the upper-triangular formula give (u|₂ι(σ))(z) = (a/d)(f|₂ι(ρ))((a/d)z+b/d). The argument on the right has imaginary part (a/d) Im z, which tends to infinity because a/d > 0. Multiplication by the fixed constant a/d preserves convergence to zero. Therefore u|₂ι(σ) vanishes at infinity.
6. The pinned OnePoint.isZeroAt_iff, applied to ι(σ)∞ = x, upgrades this one-coordinate vanishing to OnePoint.IsZeroAt x u 2. Since x was any cusp of Δ, u vanishes at every cusp of Δ. Bundle u with the invariance from step 2, holomorphy from step 3, and this cusp condition. The resulting g ∈ CuspForm Δ 2 has underlying function u by construction.

## Key steps

1. Identify the cusps of both finite-index groups with rational projective points.
2. Use the conjugation hypothesis and slash composition to prove Δ-invariance.
3. Apply the positive-determinant slash formula to preserve holomorphy.
4. Move a rational cusp and its A-image to infinity using integer determinant-one matrices.
5. Reduce to an upper-triangular positive-determinant matrix and transport vanishing at infinity.
6. Apply the single-coordinate cusp criterion and bundle the resulting cusp form.

## Reference use

### local-project

Queries:
- `petersson_slash|petersson_integral_core|coe_heckeTLin_apply|hyperbolic|Hyperbolic`
- `measurePreserving|smulInvariant|volume_preserving|isZeroAt_iff|isCusp.*iff|cusps_eq|cusp.*rational`
- `petersson_integral_core|doubleCoset|double_coset|hecke.*adjoint|adjoint.*hecke|slash.*rational`
- `mdifferentiable.*slash|slash.*mdifferentiable|holomorphic.*slash|HasDetPos|IsGLPos`
- `integral.*iUnion|integral.*biUnion|setIntegral.*sum|integral_comp.*smul|measurePreserving_smul`
- `def Gamma0|mem_Gamma0|Gamma0_mem`
- `f036cc6b1f_pc_hi_(rational_slash|good_prime_transversal|effective_domain_lift|finite_trace_unfolding)`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lean /tmp/f036cc6b1f_hecke_decomposition_checks/Types.lean`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lean /tmp/f036cc6b1f_hecke_decomposition_checks/Probe.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/project/Definitions/Def_ModularForm_HeckeOperator.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/project/Definitions/Def_ModularForm_HeckeOperatorForms.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/NumberTheory/ModularForms/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/NumberTheory/ModularForms/SlashActions.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/NumberTheory/ModularForms/Petersson.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/NumberTheory/ModularForms/Cusps.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/NumberTheory/ModularForms/BoundedAtCusp.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/NumberTheory/ModularForms/CongruenceSubgroups.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/Analysis/Complex/UpperHalfPlane/Measure.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/MeasureTheory/Group/Action.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/tmp/f036cc6b1f_hecke_decomposition_checks/Types.lean`
- `/tmp/f036cc6b1f_hecke_decomposition_checks/Types.log`
- `/tmp/f036cc6b1f_hecke_decomposition_checks/Probe.log`
- `/tmp/f036cc6b1f_hecke_decomposition_checks/Compatibility.json`

The manifest pins project 61b5f85556ac71631ccad822e0694511234f7132 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. The snapshot supplies the exact Hecke matrices, coe_heckeTLin_apply, Petersson covariance, slash holomorphy, rational-cusp classification, the single-coordinate vanishing criterion, hyperbolic-volume invariance, and integration over almost-everywhere disjoint unions. The search for petersson_integral_core, double-coset, Hecke-adjointness, and rational-slash names returned no matches in project/Definitions and mathlib/Mathlib/NumberTheory/ModularForms. All 98 compared project dependency sources match the snapshot; the installed mathlib has the pinned clean revision. All four proposed propositions elaborate as Prop after import Submission. The inferred volume instance is UpperHalfPlane.instSMulInvariantMeasureGeneralLinearGroupFinOfNatNatRealVolume; the inferred slash instances are the native GL slash action and ModularForm.SLAction. Audited library declarations, including that volume instance, depend only on propext, Classical.choice, and Quot.sound, or on no axioms. The proposed names have no matches in the current DAG or node JSON files. These are interface and library checks, not comparator acceptance of child proofs.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/250

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
