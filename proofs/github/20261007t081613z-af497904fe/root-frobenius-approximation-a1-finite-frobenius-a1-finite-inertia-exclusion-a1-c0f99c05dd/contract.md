<!-- theorem-id: fermat-p09/root.frobenius_approximation-a1.finite_frobenius-a1.finite_inertia_exclusion-a1 -->

## Theorem `Submission.p09_af497904fe_ff_finite_inertia_exclusion`

Let Ω = AlgebraicClosure ℚ and let E be an intermediate field of Ω/ℚ, finite-dimensional and Galois over ℚ. There exists a finite set S of natural numbers such that, for every natural prime ℓ outside S and every valuation subring V of E in which ℓ is a nonunit, every rational automorphism τ belonging to V.inertiaSubgroupIn ℚ is the identity. Here this inertia subgroup consists of automorphisms preserving V and acting trivially on its residue field.

Node: `root.frobenius_approximation-a1.finite_frobenius-a1.finite_inertia_exclusion-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/9

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/642

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/694, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/695

## Lean problem

Declaration: `Submission.p09_af497904fe_ff_finite_inertia_exclusion`

```lean
∀ (E : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ E] [IsGalois ℚ E], ∃ S : Finset ℕ, ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S → ∀ V : ValuationSubring E, V.LiesOverPrime ℓ → ∀ τ : E ≃ₐ[ℚ] E, τ ∈ V.inertiaSubgroupIn ℚ → τ = 1
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

- Parent DAG node: `root.frobenius_approximation-a1.finite_frobenius-a1`
- Child DAG node: `root.frobenius_approximation-a1.finite_frobenius-a1.finite_inertia_exclusion-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix E as in the statement. Choose an integral primitive element α with E = ℚ(α). Here is the finite-field argument underlying this choice. Characteristic-zero irreducible polynomials are separable, because their derivatives are nonzero and have smaller degree. Extending embeddings successively across algebraic generators by choosing roots gives as many embeddings as the extension degree. For two generators a,b, two distinct embeddings can agree on a + rb for at most one rational r unless their b-images agree, in which case they never agree there. Avoiding the finitely many exceptional rational values produces a primitive element; induction handles a finite generating family. Multiplying this element by a suitable nonzero integer makes it integral: if its monic rational polynomial is f of degree n, choose an integer N clearing all its coefficients, so N^n f(X/N) is monic integral and annihilates the scaled element. Scaling does not change the generated field.
2. Let f ∈ ℤ[X] be the monic minimal polynomial of α and let α₁,…,αₙ be its distinct roots in E, with α₁ = α. Normality places all roots in E and separability makes them distinct. The discriminant D = ∏_{i<j}(αᵢ−αⱼ)^2 is a nonzero rational integer. Indeed, the displayed expression is symmetric in the roots and is an integer polynomial in their elementary symmetric functions, which are the coefficients of f. Nonzero factors make D nonzero. For n = 1 the empty product is 1.
3. Let S be the finite set of natural prime divisors of |D|. Fix a prime ℓ outside S and a valuation subring V with V.LiesOverPrime ℓ. By definition, the image of ℓ belongs to V.nonunits. Every integer belongs to V because V is a subring containing 1.
4. Every element of E integral over ℤ belongs to V. To prove this directly, suppose an integral element x did not belong to V. Then x ≠ 0 and the valuation property gives x⁻¹ ∈ V. This inverse is a nonunit, since a V-inverse for it would put x in V. Divide a monic integral equation for x by its leading power of x. The result expresses 1 as a sum of multiples of positive powers of x⁻¹. Every summand belongs to the maximal ideal of V, a contradiction. In particular all the αᵢ belong to V.
5. Since ℓ does not divide D, there are integers u,v with uD + vℓ = 1. If D were a nonunit of V, both terms on the left would belong to its maximal ideal, contradicting the equation. Thus D is a unit of V. Its product expression then implies that every difference αᵢ−αⱼ, for i ≠ j, is a unit. Consequently the images of the αᵢ in the residue field of V are pairwise distinct.
6. Let τ belong to V.inertiaSubgroupIn ℚ. Unfolding this subgroup gives a decomposition-subgroup element whose underlying field automorphism is τ and whose action on the residue field is the identity. Therefore τ(α) and α have equal residue images. Since τ fixes ℚ, τ(α) is one of the αᵢ. Their pairwise distinct residue images force τ(α) = α.
7. The automorphism τ fixes ℚ and the generator α, hence fixes every element of ℚ(α) = E. Thus τ is the identity. The chosen S works for every ℓ and V in the statement.

## Key steps

1. Choose an integral primitive element of the finite separable extension.
2. Use its nonzero integral discriminant to define the finite exceptional set.
3. Show that valuation subrings contain integral elements and that the discriminant is a unit away from the exceptional primes.
4. Deduce that distinct conjugates have distinct residue images.
5. An inertia automorphism must fix the primitive element and therefore the entire field.

## Reference use

### local-project

Queries:
- `def IsFrobeniusAt|def LiesOverPrime|inertiaSubgroupIn|exists.*[Ff]robenius|[Cc]hebotarev`
- `ray.class|RayClass|rayClass|partial.zeta|partialZeta`
- `exp_log|log_exp|norm_log|continuous.*log|tendsto|residue|pole`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/project/Definitions/Def_EllipticCurve_FrobeniusTrace.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/project/Definitions/Def_FLTPrelim_Ramification.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/Valuation/RamificationGroup.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/Analysis/SpecialFunctions/Complex/Log.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/Analysis/Complex/Polynomial/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/NumberTheory/NumberField/DedekindZeta.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/NumberTheory`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/project/Definitions`

The snapshot pins project 20574e45daf714e745af8e649c7b61b21eed5644 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. The inspected definitions identify IsFrobeniusAt with the actual decomposition-subgroup residue action and inertiaSubgroupIn with its embedded kernel. Complex.exp_log supplies the missing normalization constant, and Complex.exp_eq_one_iff identifies the discrete logarithm ambiguity. The snapshot contains Complex.exists_root and positive Dedekind-zeta residue results. The ray-class/partial-zeta search found no matches in the listed NumberTheory and Definitions roots; the child proof supplies that argument. Rechecked interface, instance and logarithm-fact diagnostics use only propext, Classical.choice and Quot.sound.


## Acceptance

The exact contract must pass the machine comparator and an independent reviewer's comparator rerun, without changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/796

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
