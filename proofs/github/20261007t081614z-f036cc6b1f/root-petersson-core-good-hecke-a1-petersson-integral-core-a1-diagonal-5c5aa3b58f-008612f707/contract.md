<!-- theorem-id: fermat-p01/root.petersson_core_good_hecke-a1.petersson_integral_core-a1.diagonal_integral_definite-a1.ae_vanishing_from_orbit_cover-a1 -->

## Theorem `Submission.f036cc6b1f_pic_dd_ae_orbit_zero`

Let Δ be any subgroup of SL₂(ℤ), acting canonically on the upper half-plane ℍ, and let μ=dx dy/y². Let E⊂ℍ be measurable and A:ℍ→ℝ be measurable. Assume that for μ-almost every z there exists γ∈Δ with γz∈E, that A(γz)=A(z) for every γ∈Δ and z∈ℍ, and that A(z)=0 for μ restricted to E-almost every z. Then A(z)=0 for μ-almost every z∈ℍ.

Node: `root.petersson_core_good_hecke-a1.petersson_integral_core-a1.diagonal_integral_definite-a1.ae_vanishing_from_orbit_cover-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/1

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/201

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.f036cc6b1f_pic_dd_ae_orbit_zero`

```lean
∀ (Δ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) (E : Set UpperHalfPlane) (A : UpperHalfPlane → ℝ), MeasurableSet E → Measurable A → (∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane), ∃ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, γ ∈ Δ ∧ γ • z ∈ E) → (∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), γ ∈ Δ → ∀ z : UpperHalfPlane, A (γ • z) = A z) → (∀ᵐ z ∂((MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane).restrict E), A z = 0) → ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane), A z = 0
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

- Parent DAG node: `root.petersson_core_good_hecke-a1.petersson_integral_core-a1.diagonal_integral_definite-a1`
- Child DAG node: `root.petersson_core_good_hecke-a1.petersson_integral_core-a1.diagonal_integral_definite-a1.ae_vanishing_from_orbit_cover-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Write G=SL₂(ℤ) and μ=dx dy/y² on ℍ. The map sending an integer matrix to its four entries embeds G in ℤ⁴. Thus G and its subgroup Δ are countable.
2. Let N=E∩{z : A(z)≠0}. Since E and A are measurable, N is measurable. The assumed almost-everywhere equality for μ restricted to E says precisely that μ(N)=0.
3. For each γ∈Δ, the map Tγ(z)=γz is a homeomorphism with inverse Tγ⁻¹ and preserves μ. Indeed, writing γ with real entries a,b,c,d and ad−bc=1, the denominator cz+d never vanishes in ℍ, Im(Tγ(z))=Im(z)/|cz+d|², and the real Jacobian determinant is |cz+d|⁻⁴. Multiplication by the transformed density therefore gives (Im(Tγ(z)))⁻²|cz+d|⁻⁴=(Im z)⁻². The change-of-variables formula gives preservation of μ. This is also the specialization of the pinned UpperHalfPlane GL₂(ℝ)-invariance theorem to the canonical image of γ. Consequently Tγ⁻¹(N) is measurable and null.
4. Define N*=⋃γ∈Δ Tγ⁻¹(N) and C=⋃γ∈Δ Tγ⁻¹(E), where the inverse notation denotes preimage. Countability makes both sets measurable and makes N* null. The orbit-coverage hypothesis states that μ(ℍ∖C)=0.
5. Fix z∈C∖N*. By the definition of C, choose γ∈Δ such that γz∈E. Since z∉N*, one has γz∉N. Membership in E and nonmembership in N imply A(γz)=0. The assumed invariance yields A(z)=A(γz)=0.
6. It follows that {z : A(z)≠0} is contained in (ℍ∖C)∪N*, a null set. Therefore A(z)=0 for μ-almost every z in ℍ, as required.

## Key steps

1. Establish countability of Δ using its embedding in ℤ⁴.
2. Identify the measurable null exceptional set N inside E.
3. Use hyperbolic measure preservation to show that every translated preimage of N is null.
4. Form the countable null saturation N* and the conull orbit cover C.
5. Use invariance to prove vanishing on C∖N*, hence almost everywhere.

## Reference use

### local-project

Queries:
- `petersson_self|petersson.*nonneg|petersson.*zero|petersson.*invariant|theorem.*petersson|lemma.*petersson`
- `continuous.*ae_eq|eq_of_ae_eq|integral_eq_zero_iff_of_nonneg`
- `isOpenPosMeasure|IsOpenPosMeasure|ae_eq|ae.*withDensity|withDensity.*ae`
- `IsOpenPosMeasure.*UpperHalfPlane|UpperHalfPlane.*IsOpenPosMeasure|ae.*orbit|orbit.*ae|ae_orbit_zero|dd_open_pos`
- `ae_.*smul|measurePreserving_smul|preimage_smul|ae_all_iff`
- `f036cc6b1f_pic_dd_ae_orbit_zero|f036cc6b1f_pic_dd_open_pos`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/NumberTheory/ModularForms/Petersson.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/Analysis/Complex/UpperHalfPlane/Measure.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/Analysis/Complex/UpperHalfPlane/MoebiusAction.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/MeasureTheory/Group/Action.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/MeasureTheory/Measure/OpenPos.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/nodes/root-petersson-core-good-hecke-a1-petersson-integral-core-a1-diagonal-bfb02b2f40/decomposition-typechecks-dd/FrozenTypes.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/nodes/root-petersson-core-good-hecke-a1-petersson-integral-core-a1-diagonal-bfb02b2f40/decomposition-typechecks-dd/FrozenTypes.log`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/nodes/root-petersson-core-good-hecke-a1-petersson-integral-core-a1-diagonal-bfb02b2f40/decomposition-typechecks-dd/Compatibility.json`

The manifest pins project 61b5f85556ac71631ccad822e0694511234f7132 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. Petersson.lean supplies continuity and determinant-one invariance; Bochner/Basic.lean supplies the nonnegative zero-integral criterion; OpenPos.lean supplies equality of continuous functions from almost-everywhere equality once full support is established. UpperHalfPlane/Measure.lean supplies the hyperbolic density and GL₂(ℝ)-invariance. Searches found no existing theorem with the proposed orbit-cover propagation statement and no hyperbolic full-support declaration in the snapshot; the latter name occurs only in cleanup commands. Both proposed names are unreserved in the current DAG. All nine installed packages are clean and pinned, and the relevant mathlib sources and twenty local import sources match the snapshot. Both exact child types elaborate after import Submission under Lean 4.33.1. Instance inspection confirms hyperbolic volume and the canonical SL₂ action through mapGL. Thirteen inspected infrastructure declarations have only propext, Classical.choice, and Quot.sound as transitive axioms. These checks validate the proposed interfaces, not acceptance of future child proofs.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/229

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
