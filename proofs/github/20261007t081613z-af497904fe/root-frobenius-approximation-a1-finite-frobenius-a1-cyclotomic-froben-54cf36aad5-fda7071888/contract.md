<!-- theorem-id: fermat-p09/root.frobenius_approximation-a1.finite_frobenius-a1.cyclotomic_frobenius_supply-a1.bounded_euler_logarithm-a1 -->

## Theorem `Submission.p09_af497904fe_cfs_bounded_euler_logarithm`

Let E,L : ℝ → ℂ. Assume E is continuous on (1,2), L is continuous at 1 within [1,∞), L(1) ≠ 0, and exp(E(s)) = L(s) for every 1 < s < 2. Then there exist 0 < ε ≤ 1 and C ≥ 0 such that ‖E(s)‖ ≤ C whenever 1 < s < 1+ε.

Node: `root.frobenius_approximation-a1.finite_frobenius-a1.cyclotomic_frobenius_supply-a1.bounded_euler_logarithm-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/9

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/678

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p09_af497904fe_cfs_bounded_euler_logarithm`

```lean
∀ (E L : ℝ → ℂ), ContinuousOn E (Set.Ioo 1 2) → ContinuousWithinAt L (Set.Ici 1) 1 → L 1 ≠ 0 → (∀ s : ℝ, s ∈ Set.Ioo 1 2 → Complex.exp (E s) = L s) → ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, 1 < s → s < 1 + ε → ‖E s‖ ≤ C
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
- Child DAG node: `root.frobenius_approximation-a1.finite_frobenius-a1.cyclotomic_frobenius_supply-a1.bounded_euler_logarithm-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Put A = L(1). Since A ≠ 0, take c = Complex.log A. The identity Complex.exp_log gives exp(c) = A.
2. Continuity of L at 1 within [1,∞), applied with tolerance ‖A‖/2, supplies 0 < ε ≤ 1 such that ‖L(s)/A−1‖ < 1/2 whenever 1 < s < 1+ε. Write I = (1,1+ε); this interval is nonempty and contained in (1,2).
3. On the disk |z−1| < 1 define Q(z) = Σ_{n≥1} (−1)^(n+1)(z−1)^n/n. On each smaller closed disk both this series and its differentiated series converge uniformly. The geometric-series identity gives Q′(z) = 1/z. Thus exp(Q(z))/z has derivative zero on the disk. Integrating its derivative along the segment from 1 to z shows that it is constant; its value at 1 is one. Therefore exp(Q(z)) = z. Furthermore, when |z−1| ≤ 1/2, the triangle inequality gives ‖Q(z)‖ ≤ Σ_{n≥1} 2^(−n)/n ≤ Σ_{n≥1} 2^(−n) = 1.
4. For s ∈ I put H(s) = c+Q(L(s)/A). Although continuity of L was assumed only at 1, its equality with exp(E(s)) and continuity of E show that L is continuous on I. Consequently H is continuous there. Steps 1–3 give exp(H(s)) = A·L(s)/A = L(s) and ‖H(s)‖ ≤ ‖c‖+1.
5. The function D(s) = E(s)−H(s) is continuous on I and satisfies exp(D(s)) = 1. By Complex.exp_eq_one_iff, its values belong to 2πiℤ. Distinct elements of this set are separated by distance at least 2π, so it is discrete. A continuous image of the connected interval I in a discrete set consists of one point. Taking s₀ = 1+ε/2, we conclude D(s) = D(s₀) for every s ∈ I.
6. Set C = ‖c‖+1+‖D(s₀)‖, which is nonnegative. For s ∈ I, write E(s) = H(s)+D(s₀) and apply the triangle inequality to obtain ‖E(s)‖ ≤ C. Together with 0 < ε ≤ 1, this proves the exact conclusion.

## Key steps

1. Choose a logarithm of the nonzero limiting value.
2. Normalize L(s) into a disk about one using right continuity.
3. Construct and bound the power-series logarithm on that disk.
4. Add the normalization constant to obtain a bounded continuous logarithm of L(s).
5. Show that its difference from E is constant using the discrete exponential kernel.
6. Combine the bounds to obtain a uniform bound for E.

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

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/745

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
