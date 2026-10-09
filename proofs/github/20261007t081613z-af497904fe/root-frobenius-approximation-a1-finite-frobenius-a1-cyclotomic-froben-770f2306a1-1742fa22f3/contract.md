<!-- theorem-id: fermat-p09/root.frobenius_approximation-a1.finite_frobenius-a1.cyclotomic_frobenius_supply-a1.counting_mellin_continuation-a1.floor_remainder_bound-a1 -->

## Theorem `Submission.p09_af497904fe_cmc_40fde013_floor_remainder`

Let a : ℕ → ℝ and κ, α, C : ℝ satisfy 0 ≤ α and 0 ≤ C. Suppose that for every integer n ≥ 1, |Σ_{k=1}^n a(k) − κn| ≤ C n^α. Define R(t) = Σ_{k=1}^{Nat.floor(t)} a(k) − κt for every real t, where Nat.floor is the natural-number floor, equal to zero on negative inputs. Then R is measurable for the Borel structures on ℝ, and for every t ≥ 1, |R(t)| ≤ (C + |κ|)t^α. No sign condition on a and no upper bound on α are needed.

Node: `root.frobenius_approximation-a1.finite_frobenius-a1.cyclotomic_frobenius_supply-a1.counting_mellin_continuation-a1.floor_remainder_bound-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/9

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/697

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p09_af497904fe_cmc_40fde013_floor_remainder`

```lean
∀ (a : ℕ → ℝ) (κ α C : ℝ), 0 ≤ α → 0 ≤ C → (∀ n : ℕ, 1 ≤ n → |(∑ k ∈ Finset.Icc 1 n, a k) - κ * (n : ℝ)| ≤ C * (n : ℝ) ^ α) → Measurable (fun t : ℝ => (∑ k ∈ Finset.Icc 1 (Nat.floor t), a k) - κ * t) ∧ ∀ t : ℝ, 1 ≤ t → |(∑ k ∈ Finset.Icc 1 (Nat.floor t), a k) - κ * t| ≤ (C + |κ|) * t ^ α
```

### Frozen project context

`Fermat/Thm_GaloisRepAdic_exists_quadraticRelation_forall_of_frobenius.lean` at `20574e45daf714e745af8e649c7b61b21eed5644` supplies the original imports, definitions and root contract. Child hypotheses are stated above; prerequisite declarations are linked in their issues.

```lean
/-
Copyright 2026 Anthropic, PBC. Licensed under Apache-2.0; see LICENSE.
Source: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_GaloisRepAdic_exists_quadraticRelation_forall_of_frobenius.lean
Modified: replaced the proof with sorry and removed P2M proof imports.
Requires the upstream Definitions modules and their dependencies.
-/

import Mathlib
import Definitions.Def_GaloisRep_Adic
attribute [-instance] AlgebraicClosure.Rat.isGalois FrobeniusDensity.liesOver_ratBelow FrobeniusDensity.isMaximal_ratPrimeIdeal Deep.NTSupply.instNormalRayClassSubgroup NumberField.NormResidueChar.fintype_G NumberField.NormResidueChar.finite_G
attribute [-simp] TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec

set_option autoImplicit false

open IsLocalRing

theorem GaloisRepAdic.exists_quadraticRelation_forall_of_frobenius
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [CharZero 𝒪]
    (p : ℕ) [Fact p.Prime] (hp𝒪 : (p : 𝒪) ∈ maximalIdeal 𝒪)
    {R : Type} [CommRing R] [IsLocalRing R] [Algebra 𝒪 R] [Module.Finite 𝒪 R]
    (hl : IsLocalHom (algebraMap 𝒪 R))
    (ρ : GaloisRepAdic R)
    {Y : Type} [AddCommGroup Y] [Module R Y] [Module 𝒪 Y] [IsScalarTower 𝒪 R Y] [Module.Finite 𝒪 Y]
    (ρY : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Module.End R Y)
    (hcont : ∀ n : ℕ, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ F, σ x = x) →
        ∀ y : Y, ρY σ y - y ∈ (Ideal.span {(p : R)} ^ n • (⊤ : Submodule R Y)))
    (L : ℕ) [NeZero L] (D : (ZMod L)ˣ →* Module.End R Y)
    (hD : ∀ (u : (ZMod L)ˣ) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), D u * ρY σ = ρY σ * D u)
    (S₀ : Finset ℕ)
    (hES : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S₀ → ∀ (hℓL : ¬ ℓ ∣ L), ℓ ≠ p →
      ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ ℓ →
          ρY σ * ρY σ - (ρ.trace σ) • ρY σ
            + (ℓ : R) • D (ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓL)) = 0) :
    ∃ (c : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Rˣ)
      (χ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (ZMod L)ˣ),
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
        ρY σ * ρY σ - (ρ.trace σ) • ρY σ + ((c σ : Rˣ) : R) • D (χ σ) = 0 := by
  sorry
```

## Natural-language proof

Reviewed mathematical argument; formal verification state: `proved`.

# Parent-supplied natural-language proof

- Parent DAG node: `root.frobenius_approximation-a1.finite_frobenius-a1.cyclotomic_frobenius_supply-a1.counting_mellin_continuation-a1`
- Child DAG node: `root.frobenius_approximation-a1.finite_frobenius-a1.cyclotomic_frobenius_supply-a1.counting_mellin_continuation-a1.floor_remainder_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix a, κ, α, C and the stated hypotheses. For n ∈ ℕ put A_n = Σ_{k=1}^n a(k), with A_0 = 0, and for t ∈ ℝ put R(t) = A_{Nat.floor(t)} − κt.
2. The map Nat.floor : ℝ → ℕ is measurable: the inverse image of {0} is (−∞,1), and for n ≥ 1 the inverse image of {n} is [n,n+1); these are Borel sets. Every subset of ℕ is a countable union of singletons, so all its inverse images are Borel. The map n ↦ A_n from the discrete measurable space ℕ to ℝ is measurable. Therefore t ↦ A_{Nat.floor(t)} is measurable. Subtracting the continuous function t ↦ κt proves measurability of R on all of ℝ.
3. Fix t ≥ 1 and put n = Nat.floor(t). The floor inequalities give n ≥ 1 and 0 ≤ t − (n : ℝ) < 1. In particular 1 ≤ (n : ℝ) ≤ t. The identity R(t) = (A_n − κ(n : ℝ)) + κ((n : ℝ) − t), the triangle inequality, and the counting hypothesis imply |R(t)| ≤ C(n : ℝ)^α + |κ|(t − (n : ℝ)) ≤ C(n : ℝ)^α + |κ|.
4. Because α ≥ 0 and 1 ≤ (n : ℝ) ≤ t, monotonicity of real powers on positive bases gives (n : ℝ)^α ≤ t^α and 1 ≤ t^α. Multiplying these inequalities by C ≥ 0 and |κ| ≥ 0 respectively yields |R(t)| ≤ Ct^α + |κ|t^α = (C + |κ|)t^α. This proves the claimed bound for every t ≥ 1 and completes both conclusions.

## Key steps

1. Prove natural-floor measurability from its Borel level sets and compose with the sequence of finite sums.
2. Subtract κt to obtain a globally measurable remainder.
3. Use n = Nat.floor(t) ≥ 1 and 0 ≤ t − n < 1 to compare the real remainder with the integer error.
4. Use α ≥ 0 to bound n^α and 1 by t^α.

## Reference use

### local-project

Queries:
- `summable|integral|sumCoeff|cpow|nonneg`
- `differentiable.*[Mm]ellin|[Mm]ellin.*differentiable|hasDerivAt_integral|hasDerivAt.*[Mm]ellin`
- `measurable.*(floor|nat_floor)|measurable_to_countable`
- `integrableOn_Ioi_cpow_of_lt|integral_Ioi_cpow_of_lt|norm_ofReal_cpow`
- `def term|def LSeries|term_zero|term_def`
- `counting_mellin|mellin_tail|floor_remainder`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/NumberTheory/LSeries/SumCoeff.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/NumberTheory/LSeries/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/Analysis/MellinTransform.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/Analysis/Calculus/ParametricIntegral.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/Analysis/SpecialFunctions/ImproperIntegrals.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/MeasureTheory/Function/Floor.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/project/Definitions`

The manifest pins project 20574e45daf714e745af8e649c7b61b21eed5644 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. SumCoeff supplies LSeriesSummable_of_sum_norm_bigO_and_nonneg and LSeries_eq_mul_integral_of_nonneg; at exponent 1 these discharge the parent’s convergence and Abel-representation steps. Basic confirms that LSeries.term at n = 0 is zero. Floor supplies Nat.measurable_floor. ImproperIntegrals supplies integrableOn_Ioi_cpow_of_lt and integral_Ioi_cpow_of_lt for the main term. ParametricIntegral supplies differentiation under an integrable local derivative bound, also used in MellinTransform. The search for counting_mellin, mellin_tail, and floor_remainder found no matching declaration in project/Definitions, NumberTheory/LSeries, or Analysis/MellinTransform.lean. The local interfaces and cited library support passed the pinned compiler and transitive-axiom checks; only propext, Classical.choice, and Quot.sound occur.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: Pending

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
