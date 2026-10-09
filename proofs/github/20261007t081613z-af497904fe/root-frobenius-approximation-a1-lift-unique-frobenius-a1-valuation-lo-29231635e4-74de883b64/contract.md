<!-- theorem-id: fermat-p09/root.frobenius_approximation-a1.lift_unique_frobenius-a1.valuation_localization-a1.integral_center-a1.prime_center_of_containment-a1 -->

## Theorem `Submission.p09_af497904fe_ic_prime_center_of_containment`

Let E be an intermediate field of AlgebraicClosure ℚ over ℚ with FiniteDimensional ℚ E. Let ℓ be a natural prime and V a valuation subring of E satisfying V.LiesOverPrime ℓ, meaning (ℓ : E) ∈ V.nonunits. Assume every element of O = NumberField.RingOfIntegers E has its image in V. Then there exists an ideal q of O such that q.IsPrime, q ≠ ⊥, (ℓ : O) ∈ q, O/q is finite, and for every a ∈ O, (a : E) ∈ V.nonunits if and only if a ∈ q.

Node: `root.frobenius_approximation-a1.lift_unique_frobenius-a1.valuation_localization-a1.integral_center-a1.prime_center_of_containment-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/9

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/668

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p09_af497904fe_ic_prime_center_of_containment`

```lean
∀ (E : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ E] (ℓ : ℕ), ℓ.Prime → ∀ (V : ValuationSubring E), V.LiesOverPrime ℓ → (∀ a : NumberField.RingOfIntegers E, (a : E) ∈ V) → ∃ q : Ideal (NumberField.RingOfIntegers E), q.IsPrime ∧ q ≠ ⊥ ∧ (ℓ : NumberField.RingOfIntegers E) ∈ q ∧ Finite (NumberField.RingOfIntegers E ⧸ q) ∧ (∀ a : NumberField.RingOfIntegers E, (a : E) ∈ V.nonunits ↔ a ∈ q)
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

- Parent DAG node: `root.frobenius_approximation-a1.lift_unique_frobenius-a1.valuation_localization-a1.integral_center-a1`
- Child DAG node: `root.frobenius_approximation-a1.lift_unique_frobenius-a1.valuation_localization-a1.integral_center-a1.prime_center_of_containment-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix E, ℓ, V and the stated containment hypothesis, and write O = NumberField.RingOfIntegers E. The field E inherits characteristic zero from AlgebraicClosure ℚ. Its finite dimension over ℚ gives NumberField E, using NumberField.of_module_finite ℚ E.
2. Define f : O → V by sending a to its canonical image (a : E), with membership supplied by the containment hypothesis. The canonical map O → E preserves zero, one, addition and multiplication. Injectivity of the subtype map V → E therefore proves that f preserves these operations too. Thus f is a unital ring homomorphism.
3. Let m be the maximal ideal of V and put q = Ideal.comap f m. This is an ideal of O. Since f(1) = 1 ∉ m, it is proper. If ab ∈ q, then f(a)f(b) ∈ m. The maximal ideal m is prime, so f(a) ∈ m or f(b) ∈ m, giving a ∈ q or b ∈ q. Hence q.IsPrime.
4. For every a ∈ O, the definition of comap gives a ∈ q if and only if f(a) ∈ m. By ValuationSubring.coe_mem_nonunits_iff, the latter is equivalent to (a : E) ∈ V.nonunits. Reversing this equivalence gives exactly the required nonunit-membership condition.
5. The hypothesis V.LiesOverPrime ℓ says (ℓ : E) ∈ V.nonunits. The canonical maps preserve natural-number casts, so step 4 implies (ℓ : O) ∈ q. Since ℓ is prime, ℓ ≥ 2 and thus ℓ ≠ 0. Characteristic zero gives (ℓ : O) ≠ 0. If q = ⊥, its membership would imply (ℓ : O) = 0, a contradiction. Therefore q ≠ ⊥.
6. Choose a ℤ-basis (e_i) of O indexed by a finite set I, using NumberField.RingOfIntegers.basis and the finite ℤ-module instance. Every a ∈ O can be written a = ∑_{i∈I} c_i e_i with c_i ∈ ℤ. Since ℓ > 0, Euclidean division gives integers t_i and r_i with c_i = ℓt_i + r_i and 0 ≤ r_i < ℓ. Consequently a - ∑_{i∈I} r_i e_i = (ℓ : O) · ∑_{i∈I} t_i e_i belongs to q.
7. Map the finite set of tuples I → Fin ℓ to O/q by sending a tuple to the class of the corresponding sum of residue coefficients times e_i. Every quotient class has a representative a. The remainders from step 6 form such a tuple and yield the same class as a. This map is therefore surjective. A surjective image of a finite set is finite, so O/q is finite.
8. The ideal q satisfies primality by step 3, the required equivalence by step 4, nonzeroness and membership of ℓ by step 5, and quotient finiteness by step 7. These are all the asserted conclusions.

## Key steps

1. Equip E with its number-field structure.
2. Factor the canonical integer-ring embedding through V using the containment hypothesis.
3. Contract the maximal ideal of V and prove the contraction is proper and prime.
4. Identify contraction membership with membership in V.nonunits.
5. Use LiesOverPrime and characteristic zero to obtain membership of ℓ and nonzeroness.
6. Reduce finite integral-basis coefficients modulo ℓ.
7. Construct a surjection from a finite set of residue tuples onto O/q.
8. Assemble the ideal's required properties.

## Reference use

### local-project

Queries:
- `LiesOverPrime|coe_mem_nonunits_iff|of_module_finite|finite.*quotient|quotient.*finite|IsIntegrallyClosed|isIntegral.*mem`
- `coe_mem_nonunits_iff|isIntegrallyClosed|isIntegral|mem_or_inv_mem`
- `of_module_finite|basis|isIntegral|finite|HasFiniteQuotients`
- `theorem comap_isPrime|lemma comap_isPrime|instance comap_isPrime`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/project/Definitions/Def_FLTPrelim_Ramification.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/NumberTheory/NumberField/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/Valuation/ValuationSubring.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/Valuation/Integral.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/Ideal/Quotient/HasFiniteQuotients.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/Ideal/Maps.lean`

Confirmed the pinned project revision 20574e45daf714e745af8e649c7b61b21eed5644 and mathlib revision db584cd6d46c92f209a44c0f1c829460d327499d. LiesOverPrime is precisely natural-cast membership in V.nonunits. NumberField.Basic supplies NumberField.of_module_finite, integrality of ring-of-integers elements, and a finite integral basis. ValuationSubring supplies mem_or_inv_mem and coe_mem_nonunits_iff; Ideal.Maps supplies comap_isPrime. HasFiniteQuotients also provides quotient finiteness for domains finite over ℤ. The supporting declarations checked in Lean use only propext, Classical.choice and Quot.sound.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: Pending

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
