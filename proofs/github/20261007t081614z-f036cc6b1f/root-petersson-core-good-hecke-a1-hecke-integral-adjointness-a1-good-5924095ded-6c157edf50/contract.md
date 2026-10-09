<!-- theorem-id: fermat-p01/root.petersson_core_good_hecke-a1.hecke_integral_adjointness-a1.good_prime_transversal-a1 -->

## Theorem `Submission.f036cc6b1f_pc_hi_good_prime_transversal`

Let M be a nonzero natural number and p a natural prime with p not dividing M. Write Γ = Γ₀(M), ι : SL₂(ℤ) → GL₂(ℝ) for the canonical embedding, α = ModularForm.heckeMatrix p 0 = diag(1,p), A_j = ModularForm.heckeMatrix p j, and C = ModularForm.heckeDiagMatrix p = diag(p,1). There exists r : Fin(p+1) → SL₂(ℤ) such that every r_i belongs to Γ; for every γ ∈ Γ there is a unique i ∈ Fin(p+1) for which p divides the upper-right entry of γr_i⁻¹; α ι(r_j) = A_j for every j ∈ Fin p, embedded by Fin.castSucc; and there exists β ∈ Γ with α ι(r_p) = ι(β) C, where the last index is Fin.last p.

Node: `root.petersson_core_good_hecke-a1.hecke_integral_adjointness-a1.good_prime_transversal-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/1

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/33

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/214, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/215

## Lean problem

Declaration: `Submission.f036cc6b1f_pc_hi_good_prime_transversal`

```lean
∀ (M : ℕ) [NeZero M] (p : ℕ), p.Prime → ¬ p ∣ M → ∃ r : Fin (p + 1) → Matrix.SpecialLinearGroup (Fin 2) ℤ, (∀ i, r i ∈ CongruenceSubgroup.Gamma0 M) ∧ (∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, γ ∈ CongruenceSubgroup.Gamma0 M → ∃! i : Fin (p + 1), (p : ℤ) ∣ (γ * (r i)⁻¹) 0 1) ∧ (∀ i : Fin p, ModularForm.heckeMatrix p 0 * Matrix.SpecialLinearGroup.mapGL ℝ (r i.castSucc) = ModularForm.heckeMatrix p i.val) ∧ (∃ β : Matrix.SpecialLinearGroup (Fin 2) ℤ, β ∈ CongruenceSubgroup.Gamma0 M ∧ ModularForm.heckeMatrix p 0 * Matrix.SpecialLinearGroup.mapGL ℝ (r (Fin.last p)) = Matrix.SpecialLinearGroup.mapGL ℝ β * ModularForm.heckeDiagMatrix p)
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
- Child DAG node: `root.petersson_core_good_hecke-a1.hecke_integral_adjointness-a1.good_prime_transversal-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Primality and p not dividing M imply gcd(p,M) = 1. Choose integers u,v with pu+Mv = 1. For 0 ≤ j < p set t_j = ((1,j),(0,1)); set γ* = ((p,-v),(M,u)) and β = ((1,-v),(M,pu)). The determinants of γ* and β are pu+Mv = 1, and t_j also has determinant one. Their lower-left entries are respectively M, M, and 0, so all these matrices lie in Γ₀(M).
2. Define r on Fin(p+1) by r_j = t_j for the embedded indices j ∈ Fin p and r_p = γ* at the last index. These cases exhaust Fin(p+1). Step 1 proves the asserted membership of every r_i.
3. Fix γ = ((a,b),(c,d)) ∈ Γ. Since ad-bc = 1, the reductions of a and b modulo p are not both zero. Work in the field ℤ/pℤ. The relation pu+Mv = 1 implies Mv = 1 in this field, so the residue of v is nonzero.
4. Direct inversion and multiplication give (γt_j⁻¹)₀₁ = b-aj and (γ(γ*)⁻¹)₀₁ = av+bp. If the residue of a is nonzero, exactly one residue j satisfies b-aj = 0, namely j = b/a. It has a unique integer representative 0 ≤ j < p. In this case av+bp has nonzero residue av, so the last index does not satisfy the divisibility condition. If the residue of a is zero, the residue of b is nonzero, so no b-aj is zero modulo p; but av+bp is zero modulo p. Thus exactly the last index satisfies the condition. These cases prove the required existence and uniqueness for every γ.
5. Since p is positive, the pinned Hecke matrix definitions have their nonzero-p values. Multiplication gives α ι(t_j) = ((1,j),(0,p)) = A_j. Likewise α ι(γ*) = ((p,-v),(pM,pu)) = ι(β) diag(p,1) = ι(β) C. Together with β ∈ Γ from step 1, these are exactly the two requested Hecke matrix identities.

## Key steps

1. Choose Bézout coefficients for p and M and construct determinant-one matrices in Γ₀(M).
2. Index the p translations and one exceptional representative by Fin(p+1).
3. Reduce the first row of an arbitrary γ modulo p.
4. Use b-aj and av+bp to prove the unique divisibility condition.
5. Multiply by diag(1,p) to obtain the exact pinned Hecke matrices.

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

The exact contract must pass the machine comparator and an independent reviewer's comparator rerun, without changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/369

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
