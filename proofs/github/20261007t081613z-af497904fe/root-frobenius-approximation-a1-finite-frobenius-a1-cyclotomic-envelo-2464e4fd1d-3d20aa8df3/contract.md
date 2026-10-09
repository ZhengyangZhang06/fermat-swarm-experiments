<!-- theorem-id: fermat-p09/root.frobenius_approximation-a1.finite_frobenius-a1.cyclotomic_envelope-a1.cyclotomic_intersection-a1.cyclotomic_subfield_ramification-a1.prime_residue_descent-a1 -->

## Theorem `Submission.p09_af497904fe_csr_prime_residue_descent`

Let Ω = AlgebraicClosure ℚ. Let C and D be finite-dimensional intermediate fields of Ω/ℚ with D ⊆ C, and let q be a natural prime. Suppose A is a prime ideal of O_C contracting to (q), O_C/A has exactly q elements, and every prime ideal of O_C contracting to (q) equals A. Then there exists a prime ideal R of O_D contracting to (q) with ramification index e(R/ℤ) = [D:ℚ]. Neither C nor D is required to be Galois over ℚ.

Node: `root.frobenius_approximation-a1.finite_frobenius-a1.cyclotomic_envelope-a1.cyclotomic_intersection-a1.cyclotomic_subfield_ramification-a1.prime_residue_descent-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/9

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/713

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p09_af497904fe_csr_prime_residue_descent`

```lean
∀ (C D : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ C] [FiniteDimensional ℚ D] (q : ℕ) (A : Ideal (NumberField.RingOfIntegers C)), q.Prime → D ≤ C → A.IsPrime → A.LiesOver (Ideal.span {(q : ℤ)}) → Nat.card (NumberField.RingOfIntegers C ⧸ A) = q → (∀ B : Ideal (NumberField.RingOfIntegers C), B.IsPrime → B.LiesOver (Ideal.span {(q : ℤ)}) → B = A) → ∃ R : Ideal (NumberField.RingOfIntegers D), R.IsPrime ∧ R.LiesOver (Ideal.span {(q : ℤ)}) ∧ Ideal.ramificationIdx R ℤ = Module.finrank ℚ D
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
- Child DAG node: `root.frobenius_approximation-a1.finite_frobenius-a1.cyclotomic_envelope-a1.cyclotomic_intersection-a1.cyclotomic_subfield_ramification-a1.prime_residue_descent-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix C, D, q, and A satisfying all hypotheses. The inclusion D ⊆ C restricts to an injective unital ring homomorphism f : O_D → O_C: an element integral over ℤ remains integral after the field inclusion. This map agrees with the canonical maps from ℤ. The extension O_D → O_C is integral, since every element of O_C satisfies a monic polynomial over ℤ and mapping its coefficients to O_D gives a monic polynomial over O_D annihilating that element. This is the integer-ring integrality recorded by NumberField.RingOfIntegers.extension_algebra_isIntegral.
2. Define R = f⁻¹(A). Contraction of a prime ideal along a unital ring homomorphism is prime. Compatibility with the integer maps and the hypothesis A ∩ ℤ = (q) give R ∩ ℤ = (q). In particular, R lies above (q).
3. Let Q be any prime ideal of O_D above (q). Apply lying-over to the integral extension O_D → O_C. The injectivity of f makes its kernel zero, which is contained in Q, so the hypotheses of Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain hold. It supplies a prime ideal B of O_C with f⁻¹(B) = Q. Contracting further to ℤ gives B ∩ ℤ = (q). The assumed uniqueness above q in O_C therefore gives B = A, and hence Q = R. Thus R is the unique prime ideal of O_D above (q).
4. The assumption Nat.card(O_C/A) = q, with q prime and positive, implies that O_C/A is finite of cardinality q. It is nontrivial because A is prime and therefore proper. In its additive group of prime order q, the nonzero identity has order q and generates the group. Consequently every element is an integer multiple of 1, and the canonical map ℤ → O_C/A is surjective with kernel (q). It induces a ring isomorphism ℤ/qℤ ≃ O_C/A.
5. The map f induces a unital ring homomorphism f̄ : O_D/R → O_C/A. It is injective because R is exactly the inverse image of A. Its image contains every integer multiple of 1, since f is unital and agrees with the integer maps. By step 4 these multiples exhaust O_C/A, so f̄ is surjective and hence an isomorphism. The canonical map ℤ/(q) → O_D/R is also an isomorphism: its composite with f̄ is the isomorphism from step 4, and f̄ is bijective. Thus R is maximal, and O_D/R has dimension one over ℤ/(q) with its canonical scalar structure. Since (q) is maximal as well, Ideal.inertiaDeg_eq_of_isMaximal identifies this quotient-field dimension with the inertia degree, giving inertiaDeg(R/ℤ) = 1.
6. As D is a number field, O_D is a finite free ℤ-module, hence finite flat. NumberField.RingOfIntegers.rank identifies its ℤ-rank with [D:ℚ]. Apply Ideal.sum_ramification_inertia_eq_finrank to the prime ideal (q) and the finite flat ℤ-algebra O_D. By steps 2 and 3, the set of prime ideals above (q) is exactly the singleton {R}, so it has a finite indexing type and the sum reduces to e(R/ℤ) times inertiaDeg(R/ℤ). Step 5 makes the second factor one. The formula therefore gives e(R/ℤ) = rank_ℤ(O_D) = [D:ℚ]. Together with step 2, this R satisfies the required conclusion. No Galois hypothesis was used.

## Key steps

1. Restrict the field inclusion to an injective integral map between integer rings.
2. Contract A to obtain a prime R above (q).
3. Use lying-over and uniqueness upstairs to prove uniqueness of R downstairs.
4. Identify the upstairs quotient with the prime field using its cardinality q.
5. Show the induced quotient injection is surjective and deduce inertia degree one.
6. Collapse the finite-flat ramification-inertia sum to its single term and apply the integer-ring rank equality.

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

Solution PR: Pending

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
