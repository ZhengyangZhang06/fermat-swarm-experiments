<!-- theorem-id: fermat-p01/root.petersson_core_good_hecke-a1.petersson_integral_core-a1.effective_domain_transfer-a1 -->

## Theorem `Submission.f036cc6b1f_pic_domain_transfer`

Let Δ≤SL₂(ℤ) contain −I and let μ=dx dy/y² on ℍ. Let E,F⊂ℍ be measurable. For each S∈{E,F}, assume that for μ-almost every z there is γ∈Δ with γz∈S and every δ∈Δ with δz∈S satisfies δ=γ or δ=−γ. Let φ:ℍ→ℂ be continuous and Δ-invariant, meaning φ(γz)=φ(z) for every γ∈Δ and z∈ℍ. If φ is μ-integrable on E, then it is μ-integrable on F and ∫_E φ dμ=∫_F φ dμ.

Node: `root.petersson_core_good_hecke-a1.petersson_integral_core-a1.effective_domain_transfer-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/1

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/32

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/211, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/212

## Lean problem

Declaration: `Submission.f036cc6b1f_pic_domain_transfer`

```lean
∀ (Δ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) (E F : Set UpperHalfPlane), (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) ∈ Δ → MeasurableSet E → MeasurableSet F → (∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane), ∃ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, γ ∈ Δ ∧ γ • z ∈ E ∧ ∀ δ : Matrix.SpecialLinearGroup (Fin 2) ℤ, δ ∈ Δ → δ • z ∈ E → δ = γ ∨ δ = -γ) → (∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane), ∃ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, γ ∈ Δ ∧ γ • z ∈ F ∧ ∀ δ : Matrix.SpecialLinearGroup (Fin 2) ℤ, δ ∈ Δ → δ • z ∈ F → δ = γ ∨ δ = -γ) → ∀ φ : UpperHalfPlane → ℂ, Continuous φ → (∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, γ ∈ Δ → ∀ z : UpperHalfPlane, φ (γ • z) = φ z) → MeasureTheory.IntegrableOn φ E (MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane) → MeasureTheory.IntegrableOn φ F (MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane) ∧ MeasureTheory.integral ((MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane).restrict E) φ = MeasureTheory.integral ((MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane).restrict F) φ
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

- Parent DAG node: `root.petersson_core_good_hecke-a1.petersson_integral_core-a1`
- Child DAG node: `root.petersson_core_good_hecke-a1.petersson_integral_core-a1.effective_domain_transfer-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix Δ,E,F,φ satisfying the hypotheses. The group SL₂(ℤ), and hence its subgroup Δ, is countable, since an integer 2×2 matrix is determined by four integers. Every element acts on ℍ by a measure-preserving homeomorphism: the action agrees with the canonical GL₂(ℝ) action whose invariance is proved in the pinned UpperHalfPlane/Measure.lean.
2. For S=E or F, let R_S(z) be its stated representative predicate. It is measurable as a predicate in z: for each fixed γ, the condition γz∈S is a measurable preimage, and the existential and universal quantifiers over Δ are countable unions and intersections; the matrix equalities impose only constant truth values. Consequently N={z : not R_E(z) or not R_F(z)} is measurable and null by the two almost-everywhere hypotheses.
3. Let N*=⋃_{δ∈Δ}δ⁻¹N and X=ℍ\N*. Countability and measure preservation show that N* is measurable and null, so X is measurable and conull. Multiplication in Δ reindexes the union, giving δX=X for every δ∈Δ. The identity lies in Δ, so N⊆N*, and both R_E and R_F hold at every point of X. Each representative predicate implies that any two subgroup elements sending that point into the given set differ by sign, by comparing both with its witnessing representative.
4. The central subgroup {I,−I} is contained in Δ and acts trivially on ℍ. Choose a countable set L⊂Δ containing exactly one representative of each class modulo this subgroup. For γ∈L define A_γ=E∩X∩γF and B_γ=F∩X∩γ⁻¹E. These sets are measurable because all the action maps are homeomorphisms.
5. The sets A_γ partition E∩X. Indeed, for z∈E∩X choose δ∈Δ with δz∈F. If γ∈L represents δ⁻¹ modulo sign, then γ⁻¹z=δz, because −I acts trivially, so z∈A_γ. If z∈A_γ∩A_η, then γ⁻¹z and η⁻¹z belong to F. The uniqueness consequence of R_F(z) gives η⁻¹=±γ⁻¹, hence η=±γ; the choice of L implies η=γ. Likewise the B_γ partition F∩X: use R_E(z) to find δz∈E and choose γ representing δ, and use its uniqueness to prove disjointness.
6. The map z↦γ⁻¹z sends A_γ bijectively onto B_γ. Invariance of X verifies the X condition in each direction; the other conditions follow directly from the definitions. This map preserves μ, and Δ-invariance gives φ(γ⁻¹z)=φ(z). Thus the nonnegative norm integrals over A_γ and B_γ are equal. Summing these equalities over the countable partitions and discarding the null complement of X gives ∫⁺_F|φ|dμ=∫⁺_E|φ|dμ<∞.
7. Continuity makes φ strongly measurable with values in the separable Banach space ℂ. Step 6 therefore proves its integrability on F. Its restrictions to all A_γ and B_γ are integrable, and the same change of variables gives ∫_{A_γ}φdμ=∫_{B_γ}φdμ for every γ. The series of these integrals are absolutely convergent, since each summand's norm is bounded by the corresponding integral of |φ| and their sum is finite by step 6. Countable additivity for integrable functions, followed by removal of the null complement of X, now gives ∫_E φdμ=∑_γ∫_{A_γ}φdμ=∑_γ∫_{B_γ}φdμ=∫_F φdμ.

## Key steps

1. Use countability and measure-preserving Möbius actions.
2. Show the failures of the representative predicates form a measurable null set.
3. Remove its countable subgroup saturation to obtain an invariant conull set.
4. Choose representatives of Δ/{±I} and construct paired measurable pieces.
5. Prove both families are disjoint partitions using uniqueness modulo sign.
6. Transfer nonnegative norm integrals piece by piece to obtain integrability on F.
7. Transfer the absolutely convergent complex integrals to obtain equality.

## Reference use

### local-project

Queries:
- `rg -n 'integrable.*petersson|petersson.*integrable|integral.*petersson|petersson.*integral|IsOpenPosMeasure' project/Definitions mathlib/Mathlib/NumberTheory/ModularForms mathlib/Mathlib/Analysis/Complex/UpperHalfPlane`
- `exp_decay|cuspFunction|hasSum|zero_at|IsCusp|FiniteIndex|translate`
- `def fd|def fdo|isClosed_fd|sqrt|im.*fd|mem_fd`
- `SL_neg_smul|coeSubgroup|coe.*Subgroup|instCoe`
- `f036cc6b1f_pic_translated_integrable|f036cc6b1f_pic_domain_transfer|f036cc6b1f_pic_diagonal_definite`
- `git -C .lake/packages/mathlib rev-parse HEAD`
- `git -C .lake/packages/mathlib status --porcelain`
- `python3 /tmp/f036cc6b1f_integral_core_split/verify.py`
- `tail -8 /tmp/f036cc6b1f_integral_core_split/CheckInfrastructure.log`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/project/Definitions/Def_ModularForm_HeckeOperatorForms.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/NumberTheory/Modular.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/NumberTheory/ModularForms/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/NumberTheory/ModularForms/Petersson.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/NumberTheory/ModularForms/QExpansion.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/Analysis/Complex/UpperHalfPlane/Measure.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/Analysis/Complex/UpperHalfPlane/MoebiusAction.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p01/.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/local-references/7c4c5c8bc05269bb/mathlib/Mathlib/Analysis/InnerProductSpace/Defs.lean`
- `/tmp/f036cc6b1f_integral_core_split/verify.py`
- `/tmp/f036cc6b1f_integral_core_split/CheckTypes.lean`
- `/tmp/f036cc6b1f_integral_core_split/CheckTypes.log`
- `/tmp/f036cc6b1f_integral_core_split/CheckInfrastructure.lean`
- `/tmp/f036cc6b1f_integral_core_split/CheckInfrastructure.log`

The snapshot pins project 61b5f85556ac71631ccad822e0694511234f7132 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. All nine installed package revisions match their pins and have clean working trees. The inspected mathlib sources and all twenty local dependency modules rebuilt for this check match the snapshot. QExpansion.lean supplies the removable-singularity and exponential-decay arguments; Petersson.lean supplies continuity and covariance; Measure.lean defines the unnormalized hyperbolic measure and proves GL₂(ℝ)-invariance; Modular.lean supplies the domain geometry. The targeted search found no matching Petersson-integrability/integral or IsOpenPosMeasure declarations in the searched directories. All three proposed types elaborate after literal import Submission. Instance inspection confirms UpperHalfPlane.instMeasureSpace, UpperHalfPlane.SLAction.toSMul, matrix multiplication in GL₂(ℝ), and the subgroup embedding Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ). Twelve audited infrastructure declarations have only propext, Classical.choice, and Quot.sound as transitive axioms. The proposed names have no active-DAG collisions. These checks establish interface compatibility, not comparator acceptance of the proposed child proofs.


## Acceptance

The exact contract must pass the machine comparator and an independent reviewer's comparator rerun, without changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/611

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
