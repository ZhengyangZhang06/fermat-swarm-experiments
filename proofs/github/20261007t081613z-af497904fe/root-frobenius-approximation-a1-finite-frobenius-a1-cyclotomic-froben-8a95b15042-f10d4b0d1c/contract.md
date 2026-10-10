<!-- theorem-id: fermat-p09/root.frobenius_approximation-a1.finite_frobenius-a1.cyclotomic_frobenius_supply-a1.cyclic_weighted_infinitude-a1 -->

## Theorem `Submission.p09_af497904fe_cfs_cyclic_weighted_infinitude`

Let ι be a type, m a positive natural number, ω ∈ ℂ a primitive mth root of unity, N : ι → ℕ with N(i) ≥ 2, g : ι → ZMod m, and D ⊆ ι. Write w_i(s) = N(i)^(−s) for real s, and let val denote the representative in {0,…,m−1}. Assume Σ_i w_i(s) is summable for every s > 1. For each k ∈ {0,…,m−1}, define F_k(s) = Σ_i ω^(k·val(g(i)))w_i(s), and assume there exist C_k ≥ 0 and ε_k > 0 such that ‖F_k(s) − δ_{k,0} log(1/(s−1))‖ ≤ C_k for 1 < s < 1+ε_k. Finally, assume there is C_D ≥ 0 such that Σ_{i∈D} w_i(s) ≤ C_D for every 1 < s < 2. Then, for every a ∈ ZMod m, the set {i ∈ ι : i ∉ D and g(i) = a} is infinite.

Node: `root.frobenius_approximation-a1.finite_frobenius-a1.cyclotomic_frobenius_supply-a1.cyclic_weighted_infinitude-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/9

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/678

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/718, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/719, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/720

## Lean problem

Declaration: `Submission.p09_af497904fe_cfs_cyclic_weighted_infinitude`

```lean
∀ (ι : Type) (m : ℕ) (ω : ℂ) (N : ι → ℕ) (g : ι → ZMod m) (D : Set ι), 0 < m → IsPrimitiveRoot ω m → (∀ i : ι, 2 ≤ N i) → (∀ s : ℝ, 1 < s → Summable (fun i : ι => Real.rpow (N i : ℝ) (-s))) → (∀ k : Fin m, ∃ C : ℝ, 0 ≤ C ∧ ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, 1 < s → s < 1 + ε → ‖(∑' i : ι, ω ^ (k.val * (g i).val) * Complex.ofReal (Real.rpow (N i : ℝ) (-s))) - (if k.val = 0 then (Real.log (1 / (s - 1)) : ℂ) else 0)‖ ≤ C) → (∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, 1 < s → s < 2 → (∑' i : {i : ι // i ∈ D}, Real.rpow (N i.1 : ℝ) (-s)) ≤ C) → ∀ a : ZMod m, Set.Infinite {i : ι | i ∉ D ∧ g i = a}
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

- Parent DAG node: `root.frobenius_approximation-a1.finite_frobenius-a1.cyclotomic_frobenius_supply-a1`
- Child DAG node: `root.frobenius_approximation-a1.finite_frobenius-a1.cyclotomic_frobenius_supply-a1.cyclic_weighted_infinitude-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix the stated data. Since ω is primitive and m > 0, ω^m = 1, ω ≠ 0, and ‖ω‖^m = 1. Nonnegativity of the norm therefore gives ‖ω‖ = 1. Primitivity also implies that the powers ω^j for 0 ≤ j < m are distinct. Write χ_k(b) = ω^(k·val(b)) and v_k(a) = conjugate(χ_k(a)); all these numbers have norm one.
2. For a,b ∈ ZMod m put u = ω^val(b)/ω^val(a). Then u^m = 1, and u = 1 exactly when a = b. Since conjugation of a complex number of norm one equals inversion, v_k(a)χ_k(b) = u^k. If a = b, summing over 0 ≤ k < m gives m. Otherwise, multiply the geometric sum by 1−u to obtain 1−u^m = 0; cancellation of the nonzero factor 1−u gives a zero sum. Thus Σ_k v_k(a)χ_k(b) equals m when a = b and zero otherwise.
3. For s > 1 put w_i(s) = Real.rpow(N(i),−s). These weights are positive and at most one because N(i) ≥ 2. Their summability is assumed. Since ‖χ_k(g(i))w_i(s)‖ = w_i(s), each complex character-weighted series is absolutely summable. The weight series restricted to any subset is also summable. In particular, define the real number P_a(s) = Σ_{g(i)=a} w_i(s).
4. Multiply each F_k(s) by v_k(a), sum over the finite set of k, and interchange this finite sum with the absolutely convergent series over i. The identity in step 2 yields m·P_a(s) = Σ_k v_k(a)F_k(s), with the real quantity on the left viewed in ℂ.
5. Choose the constants C_k and ε_k from the hypotheses. Because there are finitely many k and m > 0, choose ε₀ > 0 no larger than one or any ε_k, and put K = (Σ_k C_k)/m ≥ 0. The k = 0 coefficient v_0(a) is one, and all other main terms vanish. Divide the identity in step 4 by m and apply the triangle inequality to the error terms. For 1 < s < 1+ε₀ this gives |P_a(s) − m^(−1)log(1/(s−1))| ≤ K, hence P_a(s) ≥ m^(−1)log(1/(s−1))−K.
6. Choose C_D from the last hypothesis. Suppose that A = {i : i ∉ D and g(i) = a} were finite, with cardinality r. Split the summable series defining P_a(s) into its parts inside and outside D. The part inside D is at most Σ_{i∈D} w_i(s), because all weights are nonnegative. The part outside D is a sum over A and is at most r, since every weight is at most one. Consequently P_a(s) ≤ C_D+r whenever 1 < s < 1+ε₀.
7. Choose a real u larger than both m(C_D+r+K) and −log ε₀, and set s = 1+exp(−u). Then 1 < s < 1+ε₀ and log(1/(s−1)) = u. Step 5 gives P_a(s) ≥ u/m−K > C_D+r, contradicting step 6. Therefore A is infinite. The argument applies to every a and also to m = 1, when the character sum has its single trivial term.

## Key steps

1. Derive unit norms and distinct powers from primitivity.
2. Prove cyclic character orthogonality by the finite geometric-sum identity.
3. Establish absolute summability of all character-weighted and restricted series.
4. Express each fiber's weighted sum by finite Fourier inversion.
5. Combine the character estimates on a common interval to obtain logarithmic growth.
6. Bound a hypothetically finite remaining fiber together with the excluded contribution.
7. Choose s sufficiently close to one to contradict that bound.

## Reference use

### local-project

Queries:
- `IsFrobeniusAt|LiesOverPrime|rayClass|RayClass|Chebotarev|chebotarev|dedekindZeta|DedekindZeta`
- `ray.class|RayClass|rayClass|partial.zeta|partialZeta|[Cc]hebotarev`
- `sum.*rpow|differentiable.*LSeries|LSeries.*differentiable|abscissaOfAbsConv|sumCoeff|sum.*cpow`
- `exp_log|exp_eq_one_iff|continuousAt_log|hasDerivAt_log|sum.*eq_zero|norm.*eq_one|geom_sum`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/project/Definitions/Def_EllipticCurve_FrobeniusTrace.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/project/Definitions/Def_FLTPrelim_Ramification.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/NumberTheory/LSeries/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/NumberTheory/LSeries/SumCoeff.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/NumberTheory/NumberField/DedekindZeta.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/Analysis/SpecialFunctions/Complex/Log.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/RootsOfUnity/PrimitiveRoots.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/NumberTheory`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/project/Definitions`

The manifest pins project 20574e45daf714e745af8e649c7b61b21eed5644 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. The inspected Frobenius definition uses the actual decomposition-subgroup action on the residue field. SumCoeff supplies absolute summability from nonnegative coefficient sums and Abel's integral representation; DedekindZeta supplies positive residue limits. Complex.exp_log and Complex.exp_eq_one_iff supply logarithm normalization and its discrete ambiguity, and PrimitiveRoots supplies geometric-sum facts. No ray-class, partial-zeta, or Chebotarev implementation matched in the searched NumberTheory and Definitions roots. The proposed interfaces and inspected library declarations were checked with the pinned toolchain; their transitive axiom reports contain only propext, Classical.choice, and Quot.sound.


## Acceptance

The exact contract must pass the machine comparator and an independent reviewer's comparator rerun, without changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/795

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
