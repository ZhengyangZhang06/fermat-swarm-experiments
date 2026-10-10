<!-- theorem-id: fermat-p09/root.frobenius_approximation-a1.lift_unique_frobenius-a1.valuation_localization-a1.integral_center-a1.integer_mem_valuation-a1 -->

## Theorem `Submission.p09_af497904fe_ic_integer_mem_valuation`

Let E be an intermediate field of AlgebraicClosure ℚ over ℚ with FiniteDimensional ℚ E, and let V be any valuation subring of E. Then every a ∈ NumberField.RingOfIntegers E has its canonical image in V.

Node: `root.frobenius_approximation-a1.lift_unique_frobenius-a1.valuation_localization-a1.integral_center-a1.integer_mem_valuation-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/9

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/668

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p09_af497904fe_ic_integer_mem_valuation`

```lean
∀ (E : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ E] (V : ValuationSubring E), ∀ a : NumberField.RingOfIntegers E, (a : E) ∈ V
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
- Child DAG node: `root.frobenius_approximation-a1.lift_unique_frobenius-a1.valuation_localization-a1.integral_center-a1.integer_mem_valuation-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix E, V and a ∈ O, where O = NumberField.RingOfIntegers E, and put α = (a : E). By NumberField.RingOfIntegers.isIntegral_coe, there is a monic polynomial P ∈ ℤ[X] with P(α) = 0. Write n for its degree. If n = 0, monicity gives P = 1, contradicting P(α) = 0 in the nontrivial field E. Thus n > 0, and the polynomial equation has the form α^n + ∑_{i<n} c_i α^i = 0 with c_i ∈ ℤ.
2. Suppose α ∉ V. Since 0 ∈ V, α ≠ 0. The valuation-subring property gives α⁻¹ ∈ V. Let y be this inverse regarded as an element of V, and let m be the maximal ideal of the local ring V.
3. The element y is not a unit in V. Indeed, an inverse z ∈ V would give α⁻¹z = 1 in E; multiplication by α would give z = α, contradicting α ∉ V. Since the maximal ideal of a local ring consists of its nonunits, y ∈ m.
4. Multiply the polynomial equation in E by (α⁻¹)^n. Because α ≠ 0 and i < n, its leading term becomes 1 and each α^i(α⁻¹)^n becomes (α⁻¹)^(n-i). Hence 1 + ∑_{i<n} c_i y^(n-i) = 0 after embedding V into E. Every integer belongs to the unital subring V, so all terms already lie in V. Injectivity of V → E gives the same equality in V.
5. For each i < n, the exponent n-i is positive. Therefore y^(n-i) = y · y^(n-i-1) belongs to m. Multiplication by c_i and addition of the finitely many terms preserve membership in m. Their negative is also in m, but the equality in step 4 identifies that negative with 1. This contradicts the properness of m.
6. Thus α ∈ V. Since a was arbitrary, every element of O has its image in V.

## Key steps

1. Use integrality to obtain a monic vanishing polynomial of positive degree.
2. If the element is outside the valuation ring, its nonzero inverse belongs to the ring.
3. That inverse is a nonunit and hence belongs to the maximal ideal.
4. Multiply the polynomial equation by the inverse raised to its degree.
5. Every remaining term lies in the maximal ideal, forcing 1 into a proper ideal.
6. Conclude universal integral containment.

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

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/723

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
