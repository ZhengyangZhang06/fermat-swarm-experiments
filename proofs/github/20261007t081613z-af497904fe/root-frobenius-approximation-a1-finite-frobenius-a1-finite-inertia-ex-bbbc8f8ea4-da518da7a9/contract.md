<!-- theorem-id: fermat-p09/root.frobenius_approximation-a1.finite_frobenius-a1.finite_inertia_exclusion-a1.conjugate_separation-a1 -->

## Theorem `Submission.p09_af497904fe_fie_conjugate_separation`

Let Ω = AlgebraicClosure ℚ, let E be an intermediate field of Ω/ℚ that is finite-dimensional and Galois over ℚ, and let α ∈ E be integral over ℤ. There exists a nonzero integer D such that, for every natural prime ℓ not dividing D.natAbs and every valuation subring V of E with V.LiesOverPrime ℓ, every rational conjugate σ(α) belongs to V, and for all rational automorphisms σ,τ of E, membership σ(α)−τ(α) ∈ V.nonunits implies σ(α)=τ(α). Here V.LiesOverPrime ℓ means that the image of ℓ is a nonunit of V, and V.nonunits is viewed as a subset of E.

Node: `root.frobenius_approximation-a1.finite_frobenius-a1.finite_inertia_exclusion-a1.conjugate_separation-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/9

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/677

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/710, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/712

## Lean problem

Declaration: `Submission.p09_af497904fe_fie_conjugate_separation`

```lean
∀ (E : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ E] [IsGalois ℚ E] (α : E), IsIntegral ℤ α → ∃ D : ℤ, D ≠ 0 ∧ ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ D.natAbs → ∀ V : ValuationSubring E, V.LiesOverPrime ℓ → (∀ σ : E ≃ₐ[ℚ] E, σ α ∈ V) ∧ ∀ σ τ : E ≃ₐ[ℚ] E, σ α - τ α ∈ V.nonunits → σ α = τ α
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

- Parent DAG node: `root.frobenius_approximation-a1.finite_frobenius-a1.finite_inertia_exclusion-a1`
- Child DAG node: `root.frobenius_approximation-a1.finite_frobenius-a1.finite_inertia_exclusion-a1.conjugate_separation-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix E and an integral element α. Let f ∈ ℤ[X] be its monic minimal polynomial. Since ℤ is integrally closed and ℚ is its fraction field, the coefficient extension of f to ℚ is the rational minimal polynomial of α; this is the compatibility statement minpoly.isIntegrallyClosed_eq_field_fractions'. In particular its degree n is positive. Normality of E/ℚ makes this polynomial split in E, and separability makes its roots distinct. Enumerate them as β₁,…,βₙ. Every βᵢ is integral over ℤ because it satisfies the monic polynomial f. Every rational automorphism σ sends α to one of these roots, since it fixes the coefficients of f.
2. Form δ=∏_{i<j}(βᵢ−βⱼ)^2 in E. Every factor is nonzero, so δ≠0. The polynomial ∏_{i<j}(Xᵢ−Xⱼ)^2 has integer coefficients and is invariant under every permutation of its variables: permutations only reorder unordered pairs and possibly reverse differences, whose squares are unchanged. The fundamental theorem of symmetric polynomials over ℤ, supplied by MvPolynomial.esymmAlgHom_surjective, expresses it as an integer polynomial in the elementary symmetric polynomials.
3. The elementary symmetric functions of β₁,…,βₙ are, with alternating signs, the coefficients of f, hence are integers. Evaluating the expression from step 2 therefore gives an integer D whose image in E equals δ. Since δ≠0, D≠0. When n=1, the product is empty and D=1. This construction depends only on α and E.
4. Every element x of E integral over ℤ belongs to every valuation subring V of E. Indeed, suppose x∉V. Then x≠0, and the valuation property gives t=x⁻¹∈V. The element t cannot be a unit of V, since its inverse in E is x; a V-inverse would put x in V. Thus t lies in the maximal ideal m of V. Take a monic integral equation x^r+∑_{i<r} a_i x^i=0, with r≥1. Every integer belongs to V. Dividing the equation by x^r yields 1+∑_{i<r} a_i t^(r−i)=0. Each exponent r−i is positive, so every summand lies in m. The equation would imply 1∈m, contradicting that m is proper. This proves the claim, and in particular all βᵢ and all σ(α) belong to V.
5. Now fix a natural prime ℓ with ℓ∤D.natAbs and a valuation subring V satisfying V.LiesOverPrime ℓ. Primality and nondivisibility imply that D and ℓ are relatively prime as integers. Bézout's identity gives integers u,v with uD+vℓ=1. The element ℓ lies in the maximal ideal m of V by the LiesOverPrime hypothesis. If D were a nonunit of V, then D would also lie in m. Since u and v belong to V, the displayed identity would put 1 in m. Therefore D is a unit of V.
6. The equality D=∏_{i<j}(βᵢ−βⱼ)^2 holds in V, since all roots belong to V and V embeds injectively into E. If any difference between distinct roots were a nonunit of V, its square would lie in m. Multiplying by the remaining factors, which belong to V, would put D in m, contradicting step 5. Thus every difference between distinct roots is a unit of V.
7. For arbitrary rational automorphisms σ and τ, step 4 gives σ(α),τ(α)∈V. If these values were unequal, they would be distinct roots of f, and step 6 would make their difference a unit of V. Such a difference cannot belong to V.nonunits. Consequently σ(α)−τ(α)∈V.nonunits implies σ(α)=τ(α). Together with the containment conclusion of step 4, this proves both assertions uniformly for every permitted ℓ and V, using the nonzero integer D constructed above.

## Key steps

1. Use the integral minimal polynomial and Galois hypotheses to enumerate distinct integral roots in E.
2. Express the squared root-difference product as an integer using symmetric polynomials.
3. Show that this integer is nonzero, including the degree-one case.
4. Prove directly that every valuation subring contains every integral element.
5. Use Bézout's identity to make D a unit whenever ℓ does not divide its absolute value.
6. Deduce that differences between distinct roots are units of the valuation subring.
7. Conclude containment and separation for all rational conjugates.

## Reference use

### local-project

Queries:
- `inertiaSubgroupIn|LiesOverPrime|primitive|discrim`
- `integral|nonunits|inertia|residue|decomposition`
- `theorem|lemma`
- `integral.*primitive|primitive.*integral`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/project/Definitions/Def_FLTPrelim_Ramification.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/FieldTheory/PrimitiveElement.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/NumberTheory/NumberField/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/FieldTheory/Minpoly/IsIntegrallyClosed.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/MvPolynomial/Symmetric/FundamentalTheorem.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/Valuation/ValuationSubring.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/Valuation/RamificationGroup.lean`
- `/tmp/p09-fie-decomposition-cq2vidxw/Interfaces.lean`
- `/tmp/p09-fie-decomposition-cq2vidxw/report.json`

The snapshot pins project 20574e45daf714e745af8e649c7b61b21eed5644 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. Field.exists_primitive_element supplies primitive generation; the scoped integral-primitive search found no match in PrimitiveElement.lean or NumberField/Basic.lean. minpoly.isIntegrallyClosed_eq_field_fractions' identifies the integral and rational minimal polynomials. MvPolynomial.esymmAlgHom_surjective supplies the integral symmetric-polynomial argument. ValuationSubring.coe_mem_nonunits_iff identifies ambient nonunits with the maximal ideal, while the project definition embeds the inertia kernel into rational automorphisms. Both proposed types elaborated after import Submission using Lean 4.33.1 and freshly compiled frozen Definitions. The inspected supporting declarations depend only on propext, Classical.choice and Quot.sound. The diagnostic records clean pinned dependencies, the matching header-policy digest, exact omitted lines, reversible original/build hashes, and successful absence checks for all eight targets. Original sources remained unchanged; these checks do not constitute proof acceptance.


## Acceptance

The exact contract must pass the machine comparator and an independent reviewer's comparator rerun, without changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/793

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
