<!-- theorem-id: fermat-p09/root.frobenius_approximation-a1.finite_frobenius-a1.cyclotomic_frobenius_supply-a1.cyclic_weighted_infinitude-a1.infinite_diff_of_log_lower_bound-a1 -->

## Theorem `Submission.p09_af497904fe_cwi_infinite_diff_of_log_lower_bound`

Let ι be a type, N : ι → ℕ satisfy N(i) ≥ 2, and E,D ⊆ ι. Put w_i(s) = Real.rpow(N(i),−s), and assume the weights are summable over ι for every real s > 1. Let c,K,ε,C be real numbers with c > 0 and 0 < ε ≤ 1. Suppose Σ_{i∈E} w_i(s) ≥ c log(1/(s−1))−K whenever 1 < s < 1+ε, and Σ_{i∈D} w_i(s) ≤ C whenever 1 < s < 2. Then E \ D is infinite. No sign condition on K or C is required.

Node: `root.frobenius_approximation-a1.finite_frobenius-a1.cyclotomic_frobenius_supply-a1.cyclic_weighted_infinitude-a1.infinite_diff_of_log_lower_bound-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/9

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/699

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p09_af497904fe_cwi_infinite_diff_of_log_lower_bound`

```lean
∀ (ι : Type) (N : ι → ℕ) (E D : Set ι) (c K ε C : ℝ), (∀ i : ι, 2 ≤ N i) → (∀ s : ℝ, 1 < s → Summable (fun i : ι => Real.rpow (N i : ℝ) (-s))) → 0 < c → 0 < ε → ε ≤ 1 → (∀ s : ℝ, 1 < s → s < 1 + ε → c * Real.log (1 / (s - 1)) - K ≤ ∑' i : {i : ι // i ∈ E}, Real.rpow (N i.1 : ℝ) (-s)) → (∀ s : ℝ, 1 < s → s < 2 → (∑' i : {i : ι // i ∈ D}, Real.rpow (N i.1 : ℝ) (-s)) ≤ C) → Set.Infinite (E \ D)
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

- Parent DAG node: `root.frobenius_approximation-a1.finite_frobenius-a1.cyclotomic_frobenius_supply-a1.cyclic_weighted_infinitude-a1`
- Child DAG node: `root.frobenius_approximation-a1.finite_frobenius-a1.cyclotomic_frobenius_supply-a1.cyclic_weighted_infinitude-a1.infinite_diff_of_log_lower_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix the stated data. For every s > 1 and every i, N(i) ≥ 2 implies 0 < w_i(s) ≤ 1: the base is positive and at least one, while the exponent −s is negative. The assumed summability implies summability of the weight series restricted to E, D, E∩D, and E\D.
2. Suppose for contradiction that A = E\D is finite, and let r be its cardinality, regarded as a real number when used in inequalities. Fix 1 < s < 1+ε. Since ε ≤ 1, we also have s < 2. The disjoint partition E = (E∩D) ∪ A and summability give Σ_{i∈E} w_i(s) = Σ_{i∈E∩D} w_i(s) + Σ_{i∈A} w_i(s). Nonnegativity and E∩D ⊆ D bound the first sum by Σ_{i∈D} w_i(s) ≤ C. The second sum is a finite sum of r terms, each at most one, and is therefore at most r. Thus Σ_{i∈E} w_i(s) ≤ C+r throughout this interval.
3. Define u = max((C+r+K)/c, −log ε)+1. Then u > (C+r+K)/c and u > −log ε. Set s = 1+exp(−u). Positivity of the exponential gives s > 1. The second strict inequality gives exp(−u) < exp(log ε) = ε, using ε > 0. Hence s < 1+ε, so both the upper bound of step 2 and the assumed lower bound apply.
4. Since s−1 = exp(−u), its reciprocal is exp(u), and log(1/(s−1)) = u. Because c > 0 and u > (C+r+K)/c, we have c·u−K > C+r. The lower bound now yields Σ_{i∈E} w_i(s) ≥ c·u−K > C+r, contradicting step 2. Thus E\D is not finite and is therefore infinite.

## Key steps

1. Bound every weight between zero and one and restrict the summable series.
2. Under finiteness of E \ D, split the E-series and bound it by C plus the finite cardinality.
3. Choose s = 1+exp(−u) inside the prescribed interval with u sufficiently large.
4. Evaluate the logarithm and contradict the uniform upper bound.

## Reference use

### local-project

Queries:
- `rg -n 'cyclic_weighted|orthogonality|summable.*rpow' project/Definitions/Def_GaloisRep_Adic.lean project/Submission.lean`
- `rg -n 'norm.*eq_one|theorem pow_inj' mathlib/Mathlib/RingTheory/RootsOfUnity/Complex.lean mathlib/Mathlib/RingTheory/RootsOfUnity/PrimitiveRoots.lean`
- `rg -n 'geom_sum_mul|mul_geom_sum' mathlib/Mathlib/Algebra/Ring/GeomSum.lean`
- `rg -n 'tprod_finsetProd|Multipliable.subtype|tprod_subtype|summable_norm_iff' mathlib/Mathlib/Topology/Algebra/InfiniteSum/Basic.lean mathlib/Mathlib/Topology/Algebra/InfiniteSum/Defs.lean mathlib/Mathlib/Analysis/Normed/Group/InfiniteSum.lean`
- `rg -n 'Summable.of_nonneg_of_le|tsum_comp_le_tsum_of_inj' mathlib/Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean`
- `rg -n 'rpow_le_one_of_one_le_of_nonpos|rpow_pos_of_pos|theorem log_exp' mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean mathlib/Mathlib/Analysis/SpecialFunctions/Log/Basic.lean`
- `rg -n 'orthog|sum.*eq|sum.*ite' mathlib/Mathlib/Analysis/Fourier/ZMod.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/project/Fermat/Thm_GaloisRepAdic_exists_quadraticRelation_forall_of_frobenius.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/project/Definitions/Def_GaloisRep_Adic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/project/Submission.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/RootsOfUnity/Complex.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/RootsOfUnity/PrimitiveRoots.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/Algebra/Ring/GeomSum.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/Topology/Algebra/InfiniteSum/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/Analysis/SpecialFunctions/Log/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/Analysis/Fourier/ZMod.lean`

Queries ran relative to the supplied snapshot root. The inspected project files contained no matching cyclic-weighted infinitude or orthogonality theorem. The pinned mathlib supplies IsPrimitiveRoot.norm'_eq_one, IsPrimitiveRoot.pow_inj, geometric-sum identities, Summable.tsum_finsetSum, tsum_subtype, nonnegative-series comparison, positive real powers, the bound for nonpositive exponents, and Real.log_exp. Fourier/ZMod.lean illustrates character orthogonality for the standard additive character; its private auxiliary declarations are not proposed dependencies. Project revision 20574e45daf714e745af8e649c7b61b21eed5644 and mathlib revision db584cd6d46c92f209a44c0f1c829460d327499d matched the manifest and were tracked-clean. Lean axiom checks for the listed proposed library dependencies reported only propext, Classical.choice, and Quot.sound.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: Pending

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
