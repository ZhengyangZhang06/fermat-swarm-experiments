<!-- theorem-id: fermat-p01/root.petersson_core_good_hecke-a1.hecke_integral_adjointness-a1.effective_domain_lift-a1 -->

## Theorem `Submission.f036cc6b1f_pc_hi_effective_domain_lift`

Let G = SL₂(ℤ), let Γ,Δ be subgroups with Δ ≤ Γ and -I ∈ Δ, and let R be a finite subset of G. Assume R ⊆ Γ, every γ ∈ Γ has some r ∈ R with γr⁻¹ ∈ Δ, and for r,s ∈ R the condition sr⁻¹ ∈ Δ implies s = r. Let F be a measurable subset of the upper half-plane. For hyperbolic-volume-almost every z, assume there exists γ ∈ Γ with γz ∈ F and every δ ∈ Γ with δz ∈ F satisfies δ = γ or δ = -γ. Define E = ⋃_{r∈R} rF. Then E is measurable and satisfies the same almost-everywhere effective-domain condition for Δ. Moreover, for almost every z, membership in both rF and sF with r,s ∈ R implies r = s.

Node: `root.petersson_core_good_hecke-a1.hecke_integral_adjointness-a1.effective_domain_lift-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/1

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/33

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.f036cc6b1f_pc_hi_effective_domain_lift`

```lean
∀ (Γ Δ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) (R : Finset (Matrix.SpecialLinearGroup (Fin 2) ℤ)) (F : Set UpperHalfPlane), Δ ≤ Γ → (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) ∈ Δ → (∀ r ∈ R, r ∈ Γ) → (∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, γ ∈ Γ → ∃ r ∈ R, γ * r⁻¹ ∈ Δ) → (∀ r ∈ R, ∀ s ∈ R, s * r⁻¹ ∈ Δ → s = r) → MeasurableSet F → (∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane), ∃ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, γ ∈ Γ ∧ γ • z ∈ F ∧ ∀ δ : Matrix.SpecialLinearGroup (Fin 2) ℤ, δ ∈ Γ → δ • z ∈ F → δ = γ ∨ δ = -γ) → let E : Set UpperHalfPlane := ⋃ r ∈ R, (fun z : UpperHalfPlane => r • z) '' F; MeasurableSet E ∧ (∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane), ∃ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, γ ∈ Δ ∧ γ • z ∈ E ∧ ∀ δ : Matrix.SpecialLinearGroup (Fin 2) ℤ, δ ∈ Δ → δ • z ∈ E → δ = γ ∨ δ = -γ) ∧ (∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane), ∀ r ∈ R, ∀ s ∈ R, z ∈ (fun w : UpperHalfPlane => r • w) '' F → z ∈ (fun w : UpperHalfPlane => s • w) '' F → r = s)
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
- Child DAG node: `root.petersson_core_good_hecke-a1.hecke_integral_adjointness-a1.effective_domain_lift-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Each integer determinant-one matrix acts on the upper half-plane by a homeomorphism, with inverse given by its inverse matrix. Consequently each image rF is measurable, and the finite union E is measurable.
2. Fix any z satisfying the assumed effective-domain property for F. At this z, any two elements a,b ∈ Γ taking z into F satisfy b = a or b = -a: compare each with the representative supplied by the hypothesis and combine the two signs. All arguments below are at such z, so the resulting assertions hold almost everywhere.
3. Choose η ∈ Γ with ηz ∈ F. Apply transversal coverage to η⁻¹ to choose r ∈ R with h = η⁻¹r⁻¹ ∈ Δ. Then η⁻¹ = hr, so h⁻¹z = r(ηz) ∈ rF ⊆ E. The element h⁻¹ ∈ Δ supplies coverage for E.
4. Suppose h₁,h₂ ∈ Δ take z into E. Choose r,s ∈ R with h₁z ∈ rF and h₂z ∈ sF. Then a = r⁻¹h₁ and b = s⁻¹h₂ belong to Γ and take z into F. By step 2, b = a or b = -a. Rearrangement gives h₂h₁⁻¹ = sr⁻¹ or h₂h₁⁻¹ = -sr⁻¹. Since h₂h₁⁻¹ ∈ Δ and -I ∈ Δ, either case implies sr⁻¹ ∈ Δ. Transversal uniqueness yields s = r; substituting this back gives h₂ = h₁ or h₂ = -h₁.
5. Apply step 4 with h₁ equal to the covering element from step 3. This proves the full quantified effective-domain condition for Δ at z, including uniqueness relative to that covering element.
6. Finally, if z ∈ rF ∩ sF for r,s ∈ R, the two elements r⁻¹,s⁻¹ ∈ Γ take z into F. Step 2 gives s⁻¹ = r⁻¹ or s⁻¹ = -r⁻¹. Hence sr⁻¹ is I or -I and belongs to Δ. Transversal uniqueness again gives s = r. This proves the asserted simultaneous almost-everywhere disjointness. All uses of the exceptional-set hypothesis were at the same point z, so no additional saturation assumption is needed.

## Key steps

1. Use homeomorphic matrix actions to obtain measurability of the finite union.
2. Turn the effective-domain hypothesis into pairwise uniqueness up to sign at a good point.
3. Decompose the inverse of a covering element to prove Δ-coverage.
4. Use transversal uniqueness and -I ∈ Δ to prove effective uniqueness for E.
5. Apply the same uniqueness argument to intersections of distinct pieces.

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

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/241

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
