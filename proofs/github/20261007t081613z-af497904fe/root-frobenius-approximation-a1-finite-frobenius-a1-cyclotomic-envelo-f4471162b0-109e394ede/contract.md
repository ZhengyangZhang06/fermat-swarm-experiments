<!-- theorem-id: fermat-p09/root.frobenius_approximation-a1.finite_frobenius-a1.cyclotomic_envelope-a1.cyclotomic_intersection-a1.cyclotomic_subfield_ramification-a1 -->

## Theorem `Submission.p09_af497904fe_ci_cyclotomic_subfield_ramification`

Let Ω = AlgebraicClosure ℚ, let q be a natural prime, and let ζ ∈ Ω be a primitive qth root of unity. Let D be a finite-dimensional intermediate field of Ω/ℚ contained in ℚ(ζ). Then there exists a prime ideal R of the ring of integers O_D whose contraction to ℤ is (q) and whose ramification index over ℤ equals [D:ℚ]. No Galois assumption on D is required.

Node: `root.frobenius_approximation-a1.finite_frobenius-a1.cyclotomic_envelope-a1.cyclotomic_intersection-a1.cyclotomic_subfield_ramification-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/9

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/691

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/728, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/729

## Lean problem

Declaration: `Submission.p09_af497904fe_ci_cyclotomic_subfield_ramification`

```lean
∀ (q : ℕ) (ζ : AlgebraicClosure ℚ), q.Prime → IsPrimitiveRoot ζ q → ∀ (D : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ D], D ≤ IntermediateField.adjoin ℚ ({ζ} : Set (AlgebraicClosure ℚ)) → ∃ R : Ideal (NumberField.RingOfIntegers D), R.IsPrime ∧ R.LiesOver (Ideal.span {(q : ℤ)}) ∧ Ideal.ramificationIdx R ℤ = Module.finrank ℚ D
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

- Parent DAG node: `root.frobenius_approximation-a1.finite_frobenius-a1.cyclotomic_envelope-a1.cyclotomic_intersection-a1`
- Child DAG node: `root.frobenius_approximation-a1.finite_frobenius-a1.cyclotomic_envelope-a1.cyclotomic_intersection-a1.cyclotomic_subfield_ramification-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix q, ζ, and D satisfying the hypotheses, and put C = ℚ(ζ). Since q is prime, q ≥ 2. Primitivity gives ζ^q = 1 and ζ ≠ 1. Thus ζ is integral, being a root of the monic integer polynomial X^q − 1, and C is a finite extension of ℚ.
2. Let Φ(X) = 1 + X + ⋯ + X^(q−1). The identity (X−1)Φ(X) = X^q−1 gives Φ(ζ) = 0. Moreover Φ(X+1) = ∑_{k=1}^q binomial(q,k) X^(k−1). This polynomial is monic, has constant coefficient q, and every other nonleading coefficient is divisible by q. To verify irreducibility, suppose it had a proper factorization over ℚ. Gauss's lemma for a monic integer polynomial supplies monic integer factors of positive degree. Reducing modulo q, their product is X^(q−1), so each reduced factor is a positive power of X. Both original constant coefficients are therefore divisible by q. Their product is q, contradicting q² ∤ q. Translation preserves irreducibility, so Φ is the minimal polynomial of ζ and [C:ℚ] = q−1.
3. The q−1 elements ζ^i, for 1 ≤ i < q, are distinct primitive qth roots and are exactly the roots of Φ. They lie in C. Consequently C/ℚ is normal and separable, and its rational embeddings into Ω are the automorphisms sending ζ to these powers. Set α = 1−ζ. The norm product formula gives N_{C/ℚ}(α) = ∏_{i=1}^{q−1}(1−ζ^i) = Φ(1) = q.
4. For 1 ≤ i < q, define u_i = (1−ζ^i)/(1−ζ). The geometric-sum identity identifies u_i with 1 + ζ + ⋯ + ζ^(i−1), so u_i belongs to O_C. The numerator is an automorphic conjugate of α; hence its norm is q, and N(u_i) = 1. Choose an integral basis of O_C. Multiplication by u_i has an integer matrix whose determinant is its field norm, namely one: the same integral basis is a rational basis of C. The adjugate matrix is therefore an integer inverse. Applied to the coordinate vector of 1, it produces v_i ∈ O_C with u_i v_i = 1. Thus every u_i is a unit of O_C.
5. Let A = αO_C. The norm-index formula for a principal ideal, represented in the snapshot by Ideal.absNorm_span_singleton, gives |O_C/A| = |N(α)| = q. A unital ring with prime cardinality q is canonically the field ℤ/qℤ: its additive group has order q, and its nonzero identity generates that group. Thus A is maximal and contracts to (q) in ℤ. Multiplying 1−ζ^i = u_i α over 1 ≤ i < q gives q = (∏ u_i)α^(q−1). Taking ideals yields qO_C = A^(q−1). If B is any prime above (q), then A^(q−1) ⊆ B. Since q−1 is positive and B is prime, A ⊆ B; maximality of A and properness of B imply B = A. Hence A is the unique prime of C above q and its residue field is ℤ/qℤ.
6. Use the inclusion D ⊆ C to embed O_D into O_C, and let R be the contraction of A. This inclusion is integral: every element of O_C satisfies a monic polynomial over ℤ, whose coefficients also belong to O_D. Contraction preserves primality, and contraction through ℤ shows R lies above (q).
7. Let Q be any prime of O_D above (q). The lying-over theorem for the integral injective extension O_D ⊆ O_C, formalized by Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain, supplies a prime B of O_C contracting to Q. Its contraction to ℤ is (q), so step 5 gives B = A. Therefore Q = R. Thus R is the unique prime of O_D above q.
8. The inclusion induces an injective ring homomorphism O_D/R → O_C/A. Its image contains every integer multiple of 1. Since O_C/A is the prime field ℤ/qℤ, these multiples exhaust the target. The injection is consequently an isomorphism compatible with the maps from ℤ/qℤ. It follows that the residue degree of R over (q) is one.
9. The integer ring O_D is finite free over ℤ, hence finite flat, and its ℤ-rank is [D:ℚ], as recorded by NumberField.RingOfIntegers.rank. Apply Ideal.sum_ramification_inertia_eq_finrank to (q) and O_D. By step 7 the sum has exactly the prime R, and by step 8 its residue-degree factor is one. The formula therefore gives e(R/q) = [D:ℚ]. Together with step 6 this proves the required existence statement. All steps apply when q = 2 as well.

## Key steps

1. Use the Eisenstein translate of the prime cyclotomic polynomial to compute [ℚ(ζ):ℚ] = q−1.
2. Compute N(1−ζ) = q and prove that each geometric-sum quotient (1−ζ^i)/(1−ζ) is an integral unit.
3. Deduce qO_C = ((1−ζ)O_C)^(q−1), with a unique prime above q and residue field ℤ/qℤ.
4. Contract that prime to O_D and use lying-over to prove uniqueness below.
5. Identify O_D/R with the prime residue field and obtain residue degree one.
6. Apply the finite-flat ramification-inertia degree formula and the integer-ring rank equality.

## Reference use

### local-project

Queries:
- `inertia_ramification|sum_ramification_inertia|ramificationIdx_mul|ramificationIdx.*finrank`
- `ramif|norm_sub_one|norm_one_sub|isUnit.*sub|span.*pow|unique`
- `ramificationIdx.*tower|ramificationIdx.*mul|ramificationIdx_algebra_tower|exists.*over|liesOver`
- `totallyRamified|totally_ramified|ramificationIdx.*finrank`
- `def LiesOverPrime|def inertiaSubgroupIn`
- `finrank_eq_one_iff|eq_bot.*finrank|finrank.*eq_bot`
- `absNorm_span_singleton|absNorm.*[Cc]ard|card.*absNorm`

Files inspected:
- `.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/manifest.json`
- `.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/project/Definitions/Def_FLTPrelim_Ramification.lean`
- `.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/NumberTheory/Cyclotomic/Basic.lean`
- `.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/NumberTheory/NumberField/Cyclotomic/Ideal.lean`
- `.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/NumberTheory/NumberField/Basic.lean`
- `.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/RamificationInertia/Basic.lean`
- `.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/RamificationInertia/Ramification.lean`
- `.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/Ideal/GoingUp.lean`
- `.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/Ideal/Norm/AbsNorm.lean`
- `.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean`

Verified the recorded project revision 20574e45daf714e745af8e649c7b61b21eed5644 and mathlib revision db584cd6d46c92f209a44c0f1c829460d327499d, with clean tracked snapshot contents. Found the exact nonunit and valuation-inertia definitions, prime-cyclotomic prime uniqueness and inertia-degree-one results, integral extensions between integer rings, lying-over, Ideal.ramificationIdx_tower, the non-Galois formula Ideal.sum_ramification_inertia_eq_finrank, NumberField.RingOfIntegers.rank, Ideal.absNorm_span_singleton, and IntermediateField.finrank_eq_one_iff. The targeted totallyRamified|totally_ramified|ramificationIdx.*finrank search found no match in the NumberField/Cyclotomic directory. The supporting declarations audited in the interface diagnostic depend only on propext, Classical.choice, and Quot.sound.


## Acceptance

The exact contract must pass the machine comparator and an independent reviewer's comparator rerun, without changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: Pending

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
