<!-- theorem-id: fermat-p09/root.frobenius_approximation-a1.finite_frobenius-a1.cyclotomic_frobenius_supply-a1.counting_mellin_continuation-a1 -->

## Theorem `Submission.p09_af497904fe_cfs_counting_mellin_continuation`

Let a : ℕ → ℝ have nonnegative values, and let κ, α ∈ ℝ with 0 ≤ α < 1. Suppose there is C ≥ 0 such that, for every integer n ≥ 1, |Σ_{k=1}^n a(k) − κn| ≤ C n^α. Then there exists H : ℂ → ℂ, holomorphic on Re(s) > α, such that for every Re(s) > 1, LSeries(a)(s) = κ/(s−1) + H(s). Here LSeries(a)(s) uses the complex coefficients a(n) and omits n = 0.

Node: `root.frobenius_approximation-a1.finite_frobenius-a1.cyclotomic_frobenius_supply-a1.counting_mellin_continuation-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/9

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/678

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/772, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/773

## Lean problem

Declaration: `Submission.p09_af497904fe_cfs_counting_mellin_continuation`

```lean
∀ (a : ℕ → ℝ) (κ α : ℝ), (∀ n : ℕ, 0 ≤ a n) → 0 ≤ α → α < 1 → (∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 1 ≤ n → |(∑ k ∈ Finset.Icc 1 n, a k) - κ * (n : ℝ)| ≤ C * (n : ℝ) ^ α) → ∃ H : ℂ → ℂ, DifferentiableOn ℂ H {s : ℂ | α < s.re} ∧ ∀ s : ℂ, 1 < s.re → LSeries (fun n : ℕ => (a n : ℂ)) s = (κ : ℂ) / (s - 1) + H s
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
- Child DAG node: `root.frobenius_approximation-a1.finite_frobenius-a1.cyclotomic_frobenius_supply-a1.counting_mellin_continuation-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix the stated data and choose the constant C. Put A_n = Σ_{k=1}^n a(k) and K = |κ| + C. Nonnegativity gives A_n ≥ 0. Since n^α ≤ n for n ≥ 1, the counting hypothesis gives A_n ≤ K n.
2. For real t ≥ 1 define A(t) = A_{⌊t⌋} and R(t) = A(t) − κt. The function A is a locally bounded measurable step function. Since ⌊t⌋ ≥ 1, 0 ≤ t−⌊t⌋ < 1, and α ≥ 0, we obtain |R(t)| ≤ C⌊t⌋^α + |κ| ≤ (C+|κ|)t^α. Also 0 ≤ A(t) ≤ Kt.
3. Fix s ∈ ℂ with σ = Re(s) > 1. For each j ≥ 0, nonnegativity and the bound for A_n give Σ_{2^j ≤ n < 2^{j+1}} |a(n)n^(−s)| ≤ 2^(−jσ) A_{2^{j+1}} ≤ 2K·2^{j(1−σ)}. The resulting geometric series converges. Thus the Dirichlet series is absolutely convergent and equals the specified LSeries; its n = 0 term is zero by definition.
4. Finite summation by parts gives Σ_{n=1}^N a(n)n^(−s) = A_N N^(−s) + s∫₁ᴺ A(t)t^(−s−1)dt. The boundary term tends to zero because its norm is at most K N^(1−σ). The integral converges absolutely because |A(t)t^(−s−1)| ≤ Kt^(−σ). Passing to the limit therefore gives LSeries(a)(s) = s∫₁∞ A(t)t^(−s−1)dt.
5. For Re(s) > α, define I(s) = ∫₁∞ R(t)t^(−s−1)dt, viewing R(t) as complex. The integral is absolutely convergent by the bound in step 2. To verify complex differentiability, fix s₀ in this half-plane and choose η > 0 and a disk about s₀ on which Re(s) ≥ α+η. The integrand and its jth derivative in s have norms bounded by (C+|κ|)t^(−1−η)(log t)^j. These functions are integrable for j = 0 and j = 1: substituting u = log t reduces their integrals to integrals of e^(−ηu) and u e^(−ηu) on [0,∞). On finite integration intervals differentiation is justified by the same bounds, and dominated convergence passes both integrals and derivatives to the infinite interval. Hence I is holomorphic throughout Re(s) > α.
6. Define H(s) = κ+sI(s) on Re(s) > α, and define H(s) = 0 elsewhere. The half-plane is open, so step 5 proves the required DifferentiableOn assertion. For Re(s) > 1, substitute A(t) = κt+R(t) into step 4. The antiderivative t^(1−s)/(1−s), whose limit at infinity is zero, gives ∫₁∞ t^(−s)dt = 1/(s−1). Consequently LSeries(a)(s) = κs/(s−1)+sI(s) = κ/(s−1)+H(s), as required.

## Key steps

1. Use nonnegative coefficients and the counting estimate to bound cumulative sums linearly.
2. Extend cumulative sums to real arguments and bound the remainder by a constant times t^α.
3. Prove absolute convergence for Re(s) > 1 using dyadic intervals.
4. Apply finite summation by parts and pass to the improper integral.
5. Differentiate the remainder integral using integrable uniform bounds.
6. Separate κs/(s−1) into the prescribed pole and a holomorphic remainder.

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

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/801

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
