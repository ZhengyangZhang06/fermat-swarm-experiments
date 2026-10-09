<!-- theorem-id: fermat-p09/root.frobenius_approximation-a1.finite_frobenius-a1.cyclotomic_envelope-a1.inertia_ramification-a1 -->

## Theorem `Submission.p09_af497904fe_ce_inertia_ramification`

Let Ω = AlgebraicClosure ℚ, and let E be a finite-dimensional Galois intermediate field of Ω/ℚ. Let q be a natural prime. Assume that, for every valuation subring V of E in which q is a nonunit, every rational automorphism belonging to V.inertiaSubgroupIn ℚ is the identity. Then every prime ideal P of the ring of integers of E lying over the integer ideal (q) has ramification index one over ℤ.

Node: `root.frobenius_approximation-a1.finite_frobenius-a1.cyclotomic_envelope-a1.inertia_ramification-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/9

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/679

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/706, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/707

## Lean problem

Declaration: `Submission.p09_af497904fe_ce_inertia_ramification`

```lean
∀ (E : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ E] [IsGalois ℚ E] (q : ℕ), q.Prime → (∀ V : ValuationSubring E, V.LiesOverPrime q → ∀ τ : E ≃ₐ[ℚ] E, τ ∈ V.inertiaSubgroupIn ℚ → τ = 1) → ∀ P : Ideal (NumberField.RingOfIntegers E), P.IsPrime → P.LiesOver (Ideal.span {(q : ℤ)}) → Ideal.ramificationIdx P ℤ = 1
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

- Parent DAG node: `root.frobenius_approximation-a1.finite_frobenius-a1.cyclotomic_envelope-a1`
- Child DAG node: `root.frobenius_approximation-a1.finite_frobenius-a1.cyclotomic_envelope-a1.inertia_ramification-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix E, q, the stated inertia hypothesis, and a prime ideal P above (q). Write O for the ring of integers of E and G for Gal(E/ℚ). The number-field integer-ring theorems apply because E is finite over ℚ: O is a Dedekind domain, is finite free over ℤ, and has fraction field E. Since q belongs to P and is nonzero in E, P is nonzero and hence maximal.
2. Realize the localization O_P inside E as V = {a/b : a,b ∈ O and b ∉ P}. The localization theorem for a nonzero prime of a Dedekind domain makes V a discrete valuation ring, hence a valuation subring of E. Its maximal ideal consists of the fractions with numerator in P. Consequently q is a nonunit in V, so V.LiesOverPrime q holds. Its residue field is canonically O/P: the residue of a/b is the residue of a divided by the nonzero residue of b. This identification is surjective since every residue class has a representative in O.
3. Let I be the ordinary ideal inertia subgroup at P inside G. Every σ ∈ I preserves P and acts trivially on O/P. Rational automorphisms preserve O because they preserve monic equations with integer coefficients. Thus σ sends a/b ∈ V to σ(a)/σ(b) ∈ V, and its inverse does likewise. Under the residue identification in step 2, this action sends the residue of a divided by the residue of b to itself. Therefore σ preserves V and acts trivially on its residue field.
4. By the definitions of the valuation decomposition subgroup and its residue-action kernel, step 3 says precisely that σ belongs to V.inertiaSubgroupIn ℚ. The assumed triviality of valuation inertia therefore gives σ = 1. Since σ was arbitrary, I is the trivial subgroup and has cardinality one.
5. Apply the finite Galois inertia-cardinality theorem, formalized by Ideal.card_inertia_eq_ramificationIdxIn, to ℤ ⊆ O and G. Its hypotheses hold: O is finite free, hence finite flat, over ℤ; both rings are domains; the residue field at (q) is the perfect finite field 𝔽_q; and the action is the Galois action. In particular, its invariant ring is ℤ, because an invariant element lies in E^G = ℚ and a rational algebraic integer is an integer. The action on O is faithful because O has fraction field E.
6. This theorem identifies |I| with the common ramification index above (q). Ideal.ramificationIdxIn_eq_ramificationIdx identifies that common index with the index of the chosen P. Step 4 therefore yields Ideal.ramificationIdx P ℤ = 1, as required.

## Key steps

1. Localize the ring of integers at a prime above q and realize the localization as a valuation subring of E.
2. Identify its residue field with the original prime quotient and show q is a nonunit.
3. Show every ideal inertia automorphism belongs to the valuation inertia subgroup.
4. Apply the hypothesis to make ideal inertia trivial.
5. Use the finite Galois inertia-cardinality formula to conclude ramification index one.

## Reference use

### local-project

Queries:
- `inertiaSubgroupIn|LiesOverPrime`
- `card.*inertia|inertia.*card|ramificationIdx.*eq|equiv.*inertia`
- `ramificationIdx_tower`
- `isDiscreteValuationRing_of_dedekind_domain`
- `exists_ideal_over_prime_of_isIntegral_of_isDomain`
- `restrict.*(Equiv|equiv)|inf_eq_bot|linearDisjoint|sup.*finrank|fixedField.*fixing|fixing.*fixedField`
- `Gal.*×.*Gal|≃\*.*×|prod.*restrictNormal|restrictNormal.*prod|exists.*algEquiv.*(sup|compositum)|exists.*prime.*(one|modEq)`
- `rg -n 'theorem|lemma' Mathlib/NumberTheory/LSeries/PrimesInAP.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/project/Definitions/Def_FLTPrelim_Ramification.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/NumberTheory/NumberField/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/NumberTheory/NumberField/Cyclotomic/Ideal.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/NumberTheory/Cyclotomic/Gal.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/NumberTheory/LSeries/PrimesInAP.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/NumberTheory/RamificationInertia/Galois.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/RamificationInertia/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/RamificationInertia/Ramification.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/DedekindDomain/Dvr.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/Ideal/GoingUp.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/Ideal/Pointwise.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/Valuation/RamificationGroup.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/FieldTheory/Galois/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/FieldTheory/Normal/Basic.lean`

Confirmed clean snapshots at project revision 20574e45daf714e745af8e649c7b61b21eed5644 and mathlib revision db584cd6d46c92f209a44c0f1c829460d327499d. LiesOverPrime means that the rational prime is a nonunit; inertiaSubgroupIn is the image of the residue-action kernel in the rational automorphism group. Found Ideal.card_inertia_eq_ramificationIdxIn, Ideal.ramificationIdxIn_eq_ramificationIdx, the ramification tower and degree formulas, prime lifting, prime-cyclotomic total ramification, restriction-map injectivity and surjectivity, and finite Galois correspondence. Nat.forall_exists_prime_gt_and_modEq and IsCyclotomicExtension.autEquivPow cover the prime-choice and cyclotomic-group infrastructure. The searched FieldTheory modules did not provide the exact unique paired-restriction interface proposed below. Supporting declarations audited by the diagnostic depend only on propext, Classical.choice, and Quot.sound.


## Acceptance

The exact contract must pass the machine comparator and an independent reviewer's comparator rerun, without changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: Pending

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
