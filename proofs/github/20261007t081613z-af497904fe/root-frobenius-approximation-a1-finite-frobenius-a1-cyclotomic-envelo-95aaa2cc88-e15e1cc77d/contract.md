<!-- theorem-id: fermat-p09/root.frobenius_approximation-a1.finite_frobenius-a1.cyclotomic_envelope-a1.cyclotomic_intersection-a1.cyclotomic_subfield_ramification-a1.cyclotomic_prime_residue-a1 -->

## Theorem `Submission.p09_af497904fe_csr_cyclotomic_prime_residue`

Let Ω = AlgebraicClosure ℚ, let q be a natural prime, and let ζ ∈ Ω be a primitive qth root of unity. Put C = ℚ(ζ). Then C is finite-dimensional over ℚ, and there exists a prime ideal A of O_C whose contraction to ℤ is (q), whose quotient O_C/A has exactly q elements, and such that every prime ideal B of O_C contracting to (q) equals A.

Node: `root.frobenius_approximation-a1.finite_frobenius-a1.cyclotomic_envelope-a1.cyclotomic_intersection-a1.cyclotomic_subfield_ramification-a1.cyclotomic_prime_residue-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/9

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/713

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p09_af497904fe_csr_cyclotomic_prime_residue`

```lean
∀ (q : ℕ) (ζ : AlgebraicClosure ℚ), q.Prime → IsPrimitiveRoot ζ q → let C := IntermediateField.adjoin ℚ ({ζ} : Set (AlgebraicClosure ℚ)); FiniteDimensional ℚ C ∧ ∃ A : Ideal (NumberField.RingOfIntegers C), A.IsPrime ∧ A.LiesOver (Ideal.span {(q : ℤ)}) ∧ Nat.card (NumberField.RingOfIntegers C ⧸ A) = q ∧ ∀ B : Ideal (NumberField.RingOfIntegers C), B.IsPrime → B.LiesOver (Ideal.span {(q : ℤ)}) → B = A
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

- Parent DAG node: `root.frobenius_approximation-a1.finite_frobenius-a1.cyclotomic_envelope-a1.cyclotomic_intersection-a1.cyclotomic_subfield_ramification-a1`
- Child DAG node: `root.frobenius_approximation-a1.finite_frobenius-a1.cyclotomic_envelope-a1.cyclotomic_intersection-a1.cyclotomic_subfield_ramification-a1.cyclotomic_prime_residue-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix q and ζ satisfying the hypotheses, and put C = ℚ(ζ). Since q is prime, q ≥ 2. Primitivity gives ζ^q = 1 and ζ ≠ 1. The monic integer polynomial X^q − 1 therefore proves that ζ is integral over ℤ and algebraic over ℚ. Consequently C is finite-dimensional over ℚ, and ζ and α = 1−ζ belong to O_C, with α ≠ 0.
2. Set Φ(X) = ∑_{j=0}^{q−1} X^j. The identity (X−1)Φ(X) = X^q−1 and ζ ≠ 1 imply Φ(ζ) = 0. Its translate is Φ(X+1) = ∑_{k=1}^q binomial(q,k)X^(k−1). It is monic with constant coefficient q. For 1 ≤ k < q, the identity k binomial(q,k) = q binomial(q−1,k−1), together with q prime and q not dividing k, shows that q divides binomial(q,k).
3. Suppose Φ(X+1) were reducible over ℚ. Gauss's lemma for monic integer polynomials gives monic integer factors of positive degree. Their reductions modulo q retain those degrees and multiply to X^(q−1). Unique factorization in the polynomial ring over ℤ/qℤ forces both reductions to be positive powers of X. Thus both original constant coefficients are divisible by q. Their product is the constant coefficient q of Φ(X+1), contradicting q² not dividing q. Translation is a polynomial-ring automorphism, so Φ is irreducible over ℚ. Since Φ is monic and annihilates ζ, it is the minimal polynomial of ζ, and [C:ℚ] = q−1.
4. For 1 ≤ i < q, the elements ζ^i are distinct primitive qth roots: equality of two such powers would make q divide their nonzero difference of exponents, and each i is coprime to q. They are q−1 distinct roots of Φ and hence exhaust its roots. Every rational embedding of C is determined by the image of ζ, and each of these roots defines such an embedding. Its image is C because an inverse of i modulo q expresses ζ as a power of ζ^i. These embeddings are therefore automorphisms of C. The norm product formula and the factorization of Φ give N_{C/ℚ}(α) = ∏_{i=1}^{q−1}(1−ζ^i) = Φ(1) = q.
5. For each 1 ≤ i < q, put u_i = (1−ζ^i)/(1−ζ). The geometric-sum identity gives u_i = ∑_{j=0}^{i−1} ζ^j, so u_i is integral and belongs to O_C. Its numerator is an automorphic conjugate of α and has norm q. Multiplicativity of the norm gives N(u_i)q = q, and q ≠ 0 gives N(u_i) = 1. Choose an integral basis of O_C, which is also a rational basis of C. Multiplication by u_i has an integer matrix with determinant N(u_i) = 1. Its adjugate is an integer inverse. Applying this inverse to the coordinate vector of 1 produces v_i ∈ O_C with u_i v_i = 1. Thus every u_i is a unit.
6. Let A = αO_C. The principal-ideal norm-index formula, represented by Ideal.absNorm_span_singleton, gives |O_C/A| = |N_{C/ℚ}(α)| = q. This also proves that the quotient is finite and nontrivial. Its additive group has prime order q. Its nonzero identity consequently has additive order q and generates the additive group. Hence the canonical map ℤ → O_C/A is surjective with kernel (q), inducing a unital ring isomorphism ℤ/qℤ ≃ O_C/A. The quotient is a field, so A is maximal and therefore prime, and its contraction to ℤ is exactly (q).
7. Multiplying the identities 1−ζ^i = u_i α over 1 ≤ i < q gives q = Uα^(q−1), where U = ∏_{i=1}^{q−1}u_i is a unit of O_C. Equality holds in O_C because its embedding into C is injective. Taking principal ideals gives qO_C = A^(q−1).
8. Let B be any prime ideal of O_C contracting to (q). Then qO_C ⊆ B, so A^(q−1) ⊆ B. For each a ∈ A, this implies a^(q−1) ∈ B. Since q−1 > 0 and B is prime, a ∈ B. Thus A ⊆ B. Maximality of A and properness of B imply B = A. The finite-dimensionality from step 1 and this ideal A establish every asserted conclusion. The argument includes q = 2, for which q−1 = 1.

## Key steps

1. Use primitivity to establish integrality, finite-dimensionality, and 1−ζ ≠ 0.
2. Apply the explicit Eisenstein argument to Φ(X+1), obtaining the minimal polynomial and degree q−1.
3. Enumerate the conjugates of ζ and compute N(1−ζ) = q.
4. Prove the geometric-sum quotients are integral units using norm one and an integral-basis determinant.
5. Use the principal-ideal norm to identify O_C/((1−ζ)) with ℤ/qℤ.
6. Obtain qO_C = ((1−ζ)O_C)^(q−1) and deduce uniqueness of the prime above q.

## Reference use

### local-project

Queries:
- `sum_ramification_inertia_eq_finrank|exists_ideal_over_prime_of_isIntegral_of_isDomain|theorem absNorm_span_singleton`
- `theorem rank|finrank|instance.*Finite|instance.*Free`
- `ramif|norm.*sub|sub.*norm|isUnit|span|finrank`
- `cyclotomic.*ramif|ramif.*cyclotomic|totally.ramif`
- `intermediateField_adjoin_isCyclotomicExtension|finiteDimensional`
- `inertiaDeg.*quotient|inertiaDeg_algebraMap|finrank.*quotient|inertiaDeg_eq`

Files inspected:
- `.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/manifest.json`
- `.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/project/Definitions`
- `.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/project/P2M`
- `.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/project/Theorems`
- `.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/NumberTheory/Cyclotomic/Basic.lean`
- `.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/NumberTheory/Cyclotomic/PrimitiveRoots.lean`
- `.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/NumberTheory/NumberField/Cyclotomic/Ideal.lean`
- `.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/NumberTheory/NumberField/Basic.lean`
- `.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/Ideal/Norm/AbsNorm.lean`
- `.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/Ideal/GoingUp.lean`
- `.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/RamificationInertia/Basic.lean`
- `.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/RamificationInertia/Inertia.lean`

Verified clean tracked snapshots at project revision 20574e45daf714e745af8e649c7b61b21eed5644 and mathlib revision db584cd6d46c92f209a44c0f1c829460d327499d, with matching pinned dependencies. The targeted cyclotomic-ramification search found no match in the project Definitions, P2M, or Theorems directories. Mathlib supplies cyclotomic prime uniqueness and norm calculations, integral extensions between integer rings, lying-over, the maximal-ideal quotient formula for inertia degree, the finite-flat ramification-inertia sum, and the integer-ring rank equality. Audited supporting declarations have only propext, Classical.choice, and Quot.sound as transitive axioms. Both proposed types elaborate after import Submission, and their implication to the exact frozen parent type passes Lean. Diagnostic evidence is in .humanize/csr-split-diagnostic-6coyxsue, including reversible policy-authorized header omission and a successful eight-target absence probe. Its audit-summary.json distinguishes concurrent committed changes to live Submission.lean from the unchanged frozen contract, header, and handoffs. These are interface diagnostics, not comparator acceptance.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/783

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
