<!-- theorem-id: fermat-p09/root.frobenius_approximation-a1.finite_frobenius-a1.cyclotomic_envelope-a1.cyclotomic_intersection-a1.unramified_subfield-a1 -->

## Theorem `Submission.p09_af497904fe_ci_unramified_subfield`

Let Ω = AlgebraicClosure ℚ. Let E and D be finite-dimensional intermediate fields of Ω/ℚ with D contained in E, and let q be a natural prime. Suppose every prime ideal of O_E above (q) has ramification index one over ℤ. Then every prime ideal of O_D above (q) also has ramification index one over ℤ. Neither field is required to be Galois over ℚ.

Node: `root.frobenius_approximation-a1.finite_frobenius-a1.cyclotomic_envelope-a1.cyclotomic_intersection-a1.unramified_subfield-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/9

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/691

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p09_af497904fe_ci_unramified_subfield`

```lean
∀ (E D : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ E] [FiniteDimensional ℚ D] (q : ℕ), q.Prime → D ≤ E → (∀ P : Ideal (NumberField.RingOfIntegers E), P.IsPrime → P.LiesOver (Ideal.span {(q : ℤ)}) → Ideal.ramificationIdx P ℤ = 1) → ∀ R : Ideal (NumberField.RingOfIntegers D), R.IsPrime → R.LiesOver (Ideal.span {(q : ℤ)}) → Ideal.ramificationIdx R ℤ = 1
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
- Child DAG node: `root.frobenius_approximation-a1.finite_frobenius-a1.cyclotomic_envelope-a1.cyclotomic_intersection-a1.unramified_subfield-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix E, D, q, the inclusion D ⊆ E, and the assumed ramification-index-one condition in E. Both fields are number fields. Their integer rings are Dedekind domains, finite free over ℤ, and the field inclusion restricts to an injective homomorphism O_D → O_E compatible with the integer maps. Indeed, an element integral over ℤ remains integral under the field inclusion.
2. The extension O_D ⊆ O_E is integral because every element of O_E satisfies a monic integer polynomial and ℤ is contained in O_D. It is also finite: any finite collection generating O_E as a ℤ-module generates it as an O_D-module. Moreover O_E is torsion-free over O_D, since both embed compatibly into the field E. A torsion-free module over a Dedekind domain is flat, so O_E is flat over O_D. These facts establish the hypotheses for lying-over and the ramification tower formula.
3. Let R be any prime ideal of O_D whose contraction to ℤ is (q). The lying-over theorem for the integral injective extension O_D ⊆ O_E, formalized by Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain, gives a prime ideal P of O_E whose contraction to O_D is R. The injectivity makes the theorem's kernel-containment hypothesis automatic.
4. Contracting P further to ℤ gives (q), because contraction along composed inclusions agrees with successive contraction. Hence the assumed condition in E applies to P and gives e(P/q) = 1.
5. Apply Ideal.ramificationIdx_tower to ℤ ⊆ O_D ⊆ O_E and the primes R and P. Flatness was established in step 2, and P lies over R by construction. The formula gives e(P/q) = e(R/q) e(P/R). Thus e(R/q) e(P/R) = 1. Both factors are natural numbers, and a product of natural numbers is one only when both factors are one. In particular e(R/q) = 1.
6. Since R was arbitrary among primes of O_D above (q), every such prime has ramification index one, as asserted.

## Key steps

1. Equip the integer-ring inclusion O_D ⊆ O_E with its integral, finite, and flat extension properties.
2. Lift an arbitrary prime R above q to a prime P of O_E by lying-over.
3. Use transitivity of contraction and the hypothesis to obtain e(P/q) = 1.
4. Apply multiplicativity in the tower and conclude e(R/q) = 1 from the natural-number product equaling one.

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

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/764

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
