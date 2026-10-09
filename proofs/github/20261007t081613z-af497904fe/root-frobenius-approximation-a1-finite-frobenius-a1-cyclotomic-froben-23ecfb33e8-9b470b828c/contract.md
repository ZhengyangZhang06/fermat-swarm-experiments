<!-- theorem-id: fermat-p09/root.frobenius_approximation-a1.finite_frobenius-a1.cyclotomic_frobenius_supply-a1.cyclic_weighted_infinitude-a1.fiber_log_estimate-a1 -->

## Theorem `Submission.p09_af497904fe_cwi_fiber_log_estimate`

Let ι be a type, m a positive natural number, ω ∈ ℂ a primitive mth root, N : ι → ℕ with N(i) ≥ 2, and g : ι → ZMod m. Put w_i(s) = Real.rpow(N(i),−s), and assume these real weights are summable over ι for every real s > 1. For k ∈ Fin m put F_k(s) = Σ_i ω^(k.val·val(g(i)))w_i(s), with weights embedded in ℂ. Assume that for each k there exist real C_k ≥ 0 and ε_k > 0 such that ‖F_k(s) − δ_{k.val,0} log(1/(s−1))‖ ≤ C_k whenever 1 < s < 1+ε_k. Then there exist real K ≥ 0 and ε with 0 < ε ≤ 1 such that, simultaneously for every a ∈ ZMod m and every 1 < s < 1+ε, |Σ_{i:g(i)=a} w_i(s) − log(1/(s−1))/m| ≤ K.

Node: `root.frobenius_approximation-a1.finite_frobenius-a1.cyclotomic_frobenius_supply-a1.cyclic_weighted_infinitude-a1.fiber_log_estimate-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/9

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/699

Prerequisites: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/718

Decomposition children: None

## Lean problem

Declaration: `Submission.p09_af497904fe_cwi_fiber_log_estimate`

```lean
∀ (ι : Type) (m : ℕ) (ω : ℂ) (N : ι → ℕ) (g : ι → ZMod m), 0 < m → IsPrimitiveRoot ω m → (∀ i : ι, 2 ≤ N i) → (∀ s : ℝ, 1 < s → Summable (fun i : ι => Real.rpow (N i : ℝ) (-s))) → (∀ k : Fin m, ∃ C : ℝ, 0 ≤ C ∧ ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, 1 < s → s < 1 + ε → ‖(∑' i : ι, ω ^ (k.val * (g i).val) * Complex.ofReal (Real.rpow (N i : ℝ) (-s))) - (if k.val = 0 then (Real.log (1 / (s - 1)) : ℂ) else 0)‖ ≤ C) → ∃ K : ℝ, 0 ≤ K ∧ ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∀ (a : ZMod m) (s : ℝ), 1 < s → s < 1 + ε → |(∑' i : {i : ι // g i = a}, Real.rpow (N i.1 : ℝ) (-s)) - Real.log (1 / (s - 1)) / (m : ℝ)| ≤ K
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
- Child DAG node: `root.frobenius_approximation-a1.finite_frobenius-a1.cyclotomic_frobenius_supply-a1.cyclic_weighted_infinitude-a1.fiber_log_estimate-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix the stated data. From ω^m = 1 and m > 0, taking norms gives ‖ω‖ = 1. Thus χ_k(b) = ω^(k.val·val(b)) and v_k(a) = conjugate(χ_k(a)) have norm one for every k,a,b. For s > 1 the weights w_i(s) are positive because N(i) ≥ 2. Consequently ‖χ_k(g(i))w_i(s)‖ = w_i(s). The assumed summability of the weights therefore proves absolute summability of every character-weighted series and of its product by the constant v_k(a). The restricted real weight series on every fiber is summable as well; denote its sum by P_a(s).
2. Fix a and s > 1. Multiplication by a fixed complex scalar commutes with these sums. Since there are finitely many k and each series is absolutely summable, finite summation also commutes with summation over ι. Therefore ∑_k v_k(a)F_k(s) = ∑_i (∑_k v_k(a)χ_k(g(i)))w_i(s). Apply the sibling theorem character_orthogonality with the present m,ω,a and b = g(i). Its hypotheses are exactly m > 0 and the given primitivity. The inner sum is m when g(i) = a and zero otherwise. The resulting indicator series equals the sum over the fiber, so ∑_k v_k(a)F_k(s) = m·P_a(s), with real quantities embedded in ℂ.
3. For every k choose constants C_k ≥ 0 and ε_k > 0 supplied by the hypothesis. Let ε be the minimum of the finite nonempty collection consisting of 1 and all ε_k. Then 0 < ε ≤ 1 and ε ≤ ε_k for every k. Put C_* = ∑_k C_k and K = C_*/(m : ℝ). Because every C_k is nonnegative and m > 0, K ≥ 0. These choices do not depend on a.
4. Fix any a and any 1 < s < 1+ε, and put L = log(1/(s−1)). There is exactly one element of Fin m with value zero, namely ⟨0, m > 0⟩. For this index v_k(a) = 1. Therefore the sum of v_k(a) times the prescribed main term δ_{k.val,0}L is L. Subtracting these main terms from the identity in step 2 gives m·P_a(s)−L = ∑_k v_k(a)(F_k(s)−δ_{k.val,0}L).
5. All character estimates apply because s < 1+ε ≤ 1+ε_k. The triangle inequality and ‖v_k(a)‖ = 1 give ‖m·P_a(s)−L‖ ≤ ∑_k C_k = C_*. The expression on the left is real embedded in ℂ, so its norm is |m·P_a(s)−L| = (m : ℝ)|P_a(s)−L/(m : ℝ)|. Divide by the positive real number m to obtain |P_a(s)−L/m| ≤ K. Since a and s were arbitrary and the constants were chosen independently of a, this proves the stated uniform estimate.

## Key steps

1. Establish absolute summability of the complex character series and summability on fibers.
2. Interchange the finite character sum with the series and apply character orthogonality.
3. Choose one positive interval and one nonnegative error constant for all characters.
4. Observe that the weighted main terms contribute exactly one logarithm.
5. Apply the triangle inequality and divide by m to obtain the uniform real estimate.

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
