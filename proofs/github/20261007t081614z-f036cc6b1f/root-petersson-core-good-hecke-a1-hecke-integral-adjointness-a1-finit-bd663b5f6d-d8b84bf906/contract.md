<!-- theorem-id: fermat-p01/root.petersson_core_good_hecke-a1.hecke_integral_adjointness-a1.finite_trace_unfolding-a1 -->

## Theorem `Submission.f036cc6b1f_pc_hi_finite_trace_unfolding`

Let G = SL₂(ℤ), let Δ ≤ Γ ≤ G with -I ∈ Δ, and let R ⊂ G be finite. Assume R ⊆ Γ; for every γ ∈ Γ there is r ∈ R with γr⁻¹ ∈ Δ; and for r,s ∈ R, sr⁻¹ ∈ Δ implies s = r. Let F ⊂ ℍ be measurable and satisfy the effective Γ-domain condition: for hyperbolic-volume-almost every z there is γ ∈ Γ with γz ∈ F and every δ ∈ Γ taking z into F equals γ or -γ. Let u,v : ℍ → ℂ be arbitrary functions with v|₂γ = v for every γ ∈ Γ. Put E = ⋃_{r∈R} rF and P(u,v)(z) = conjugate(u(z))v(z)(Im z)². If P(u,v) is integrable on E, then every P(u|₂r,v), r ∈ R, is integrable on F, and ∫_F P(Σ_{r∈R} u|₂r,v)dμ = ∫_E P(u,v)dμ.

Node: `root.petersson_core_good_hecke-a1.hecke_integral_adjointness-a1.finite_trace_unfolding-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/1

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/33

Prerequisites: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/206

Decomposition children: None

## Lean problem

Declaration: `Submission.f036cc6b1f_pc_hi_finite_trace_unfolding`

```lean
∀ (Γ Δ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) (R : Finset (Matrix.SpecialLinearGroup (Fin 2) ℤ)) (F : Set UpperHalfPlane), Δ ≤ Γ → (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) ∈ Δ → (∀ r ∈ R, r ∈ Γ) → (∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, γ ∈ Γ → ∃ r ∈ R, γ * r⁻¹ ∈ Δ) → (∀ r ∈ R, ∀ s ∈ R, s * r⁻¹ ∈ Δ → s = r) → MeasurableSet F → (∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane), ∃ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, γ ∈ Γ ∧ γ • z ∈ F ∧ ∀ δ : Matrix.SpecialLinearGroup (Fin 2) ℤ, δ ∈ Γ → δ • z ∈ F → δ = γ ∨ δ = -γ) → ∀ u v : UpperHalfPlane → ℂ, (∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, γ ∈ Γ → SlashAction.map (2 : ℤ) γ v = v) → let E : Set UpperHalfPlane := ⋃ r ∈ R, (fun z : UpperHalfPlane => r • z) '' F; MeasureTheory.IntegrableOn (UpperHalfPlane.petersson 2 u v) E (MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane) → (∀ r ∈ R, MeasureTheory.IntegrableOn (UpperHalfPlane.petersson 2 (SlashAction.map (2 : ℤ) r u) v) F (MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane)) ∧ MeasureTheory.integral ((MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane).restrict F) (UpperHalfPlane.petersson 2 (R.sum (fun r => SlashAction.map (2 : ℤ) r u)) v) = MeasureTheory.integral ((MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane).restrict E) (UpperHalfPlane.petersson 2 u v)
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
- Child DAG node: `root.petersson_core_good_hecke-a1.hecke_integral_adjointness-a1.finite_trace_unfolding-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Apply effective_domain_lift to the stated Γ,Δ,R,F. It gives a measurable E and simultaneous almost-everywhere disjointness of its pieces. Each piece rF is measurable because the action of r is a homeomorphism. In particular, each pair of distinct pieces has null intersection.
2. Write Q = P(u,v). Since Q is integrable on E and rF ⊆ E, Q is integrable on each rF. The map z ↦ rz is a measurable bijection with measurable inverse and preserves hyperbolic volume. The latter is the SL₂(ℤ) specialization of the pinned GL₂(ℝ)-invariant measure instance in Mathlib/Analysis/Complex/UpperHalfPlane/Measure.lean, using the canonical embedding of the integer matrix.
3. For r ∈ R, the hypothesis R ⊆ Γ gives v|₂r = v. The pinned UpperHalfPlane.petersson_slash_SL therefore gives P(u|₂r,v)(z) = P(u|₂r,v|₂r)(z) = Q(rz) for every z. Change of variables for the measure-preserving bijection in step 2 shows that this function is integrable on F and that ∫_F P(u|₂r,v)dμ = ∫_{rF} Q dμ. This proves every individual integrability assertion in the conclusion.
4. Complex conjugation distributes over finite sums, so pointwise P(Σ_{r∈R}u|₂r,v) = Σ_{r∈R}P(u|₂r,v). Step 3 supplies integrability of each term on F; finite-sum linearity of the Bochner integral consequently gives ∫_F P(Σ_{r∈R}u|₂r,v)dμ = Σ_{r∈R}∫_F P(u|₂r,v)dμ.
5. Substitute the integral identities from step 3 into the sum from step 4. Because the measurable pieces rF are pairwise disjoint almost everywhere and Q is integrable on their union, finite additivity of the integral gives Σ_{r∈R}∫_{rF}Q dμ = ∫_E Q dμ. For example, this is the finite-index specialization of the pinned MeasureTheory.integral_iUnion_ae. The two equalities prove the claimed unfolding identity, without introducing any multiplicity or index factor.

## Key steps

1. Use effective_domain_lift to obtain measurable, almost-everywhere disjoint pieces.
2. Restrict integrability to each translated piece and use invariance of hyperbolic volume.
3. Apply Petersson covariance and Γ-invariance of v to transport each integral to F.
4. Expand the finite slash trace and use integrability to exchange the finite sum and integral.
5. Recombine the translated integrals over the almost-everywhere disjoint union.

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

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/394

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
