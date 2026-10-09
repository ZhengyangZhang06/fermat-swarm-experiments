<!-- theorem-id: fermat-p09/root.frobenius_approximation-a1.finite_frobenius-a1.cyclotomic_frobenius_supply-a1.cyclic_weighted_infinitude-a1.character_orthogonality-a1 -->

## Theorem `Submission.p09_af497904fe_cwi_character_orthogonality`

Let m be a positive natural number and ω a primitive mth root of unity in ℂ. For a,b ∈ ZMod m, let val denote the representative in {0,…,m−1}. Then the sum over integers 0 ≤ k < m of conjugate(ω^(k·val(a)))·ω^(k·val(b)) equals m if b = a, and equals zero otherwise.

Node: `root.frobenius_approximation-a1.finite_frobenius-a1.cyclotomic_frobenius_supply-a1.cyclic_weighted_infinitude-a1.character_orthogonality-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/9

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/699

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p09_af497904fe_cwi_character_orthogonality`

```lean
∀ (m : ℕ) (ω : ℂ), 0 < m → IsPrimitiveRoot ω m → ∀ a b : ZMod m, (∑ k : Fin m, star (ω ^ (k.val * a.val)) * ω ^ (k.val * b.val)) = (if b = a then (m : ℂ) else 0)
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
- Child DAG node: `root.frobenius_approximation-a1.finite_frobenius-a1.cyclotomic_frobenius_supply-a1.cyclic_weighted_infinitude-a1.character_orthogonality-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix m > 0, a primitive mth root ω, and a,b ∈ ZMod m. Primitivity gives ω^m = 1. Hence ω ≠ 0 and ‖ω‖^m = 1. Since ‖ω‖ is nonnegative and m is positive, ‖ω‖ = 1: a nonnegative number strictly below or strictly above one has its positive integral power respectively below or above one.
2. The powers ω^j with 0 ≤ j < m are distinct. Indeed, if ω^j = ω^l and j < l < m, cancellation gives ω^(l−j) = 1. Primitivity implies m divides l−j, contradicting 0 < l−j < m. The case l < j is identical with the indices exchanged. Consequently ω^val(a) = ω^val(b) exactly when a = b, because the representatives lie in this range and determine their residue classes.
3. Put A = ω^val(a), B = ω^val(b), and u = B/A. Both A and B are nonzero and have norm one. Moreover A^m = B^m = 1, so u^m = 1. By step 2, u = 1 exactly when b = a. For every natural k, conjugate(A) = A⁻¹ and the laws of powers give conjugate(ω^(k·val(a)))·ω^(k·val(b)) = (A⁻¹B)^k = u^k.
4. If b = a, then u = 1, and the sum of its m powers indexed by Fin m is m. If b ≠ a, let S = ∑_{k=0}^{m−1} u^k. Expanding and cancelling successive terms gives (1−u)S = 1−u^m = 0. Since 1−u ≠ 0 in ℂ, S = 0. Substitution using step 3 proves the stated identity. The argument includes m = 1.

## Key steps

1. Derive ω ≠ 0 and ‖ω‖ = 1 from ω^m = 1 and m > 0.
2. Use primitivity to distinguish powers indexed by distinct canonical representatives.
3. Rewrite each conjugate-character product as a power of u = ω^val(b)/ω^val(a).
4. Evaluate the geometric sum separately for u = 1 and u ≠ 1.

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
