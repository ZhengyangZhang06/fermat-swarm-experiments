<!-- theorem-id: fermat-p09/root.frobenius_approximation-a1.lift_unique_frobenius-a1.valuation_localization-a1.integral_center-a1 -->

## Theorem `Submission.p09_af497904fe_vloc_integral_center`

Let Ω = AlgebraicClosure ℚ and let E be an intermediate field of Ω/ℚ with FiniteDimensional ℚ E. Let ℓ be a natural prime and V a valuation subring of E such that V.LiesOverPrime ℓ, meaning that (ℓ : E) belongs to V.nonunits. Write O_E = NumberField.RingOfIntegers E. Every a ∈ O_E has image in V. Moreover, there exists an ideal q of O_E such that q is prime, q ≠ 0, ℓ ∈ q, O_E/q is finite, and for every a ∈ O_E its image belongs to V.nonunits if and only if a ∈ q.

Node: `root.frobenius_approximation-a1.lift_unique_frobenius-a1.valuation_localization-a1.integral_center-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/9

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/658

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/686, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/687

## Lean problem

Declaration: `Submission.p09_af497904fe_vloc_integral_center`

```lean
∀ (E : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ E] (ℓ : ℕ), ℓ.Prime → ∀ (V : ValuationSubring E), V.LiesOverPrime ℓ → (∀ a : NumberField.RingOfIntegers E, (a : E) ∈ V) ∧ ∃ q : Ideal (NumberField.RingOfIntegers E), q.IsPrime ∧ q ≠ ⊥ ∧ (ℓ : NumberField.RingOfIntegers E) ∈ q ∧ Finite (NumberField.RingOfIntegers E ⧸ q) ∧ (∀ a : NumberField.RingOfIntegers E, (a : E) ∈ V.nonunits ↔ a ∈ q)
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

- Parent DAG node: `root.frobenius_approximation-a1.lift_unique_frobenius-a1.valuation_localization-a1`
- Child DAG node: `root.frobenius_approximation-a1.lift_unique_frobenius-a1.valuation_localization-a1.integral_center-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix E, ℓ, and V satisfying the hypotheses, and write O = NumberField.RingOfIntegers E. The characteristic-zero structure inherited from Ω and the finite rational dimension give NumberField E, as expressed by NumberField.of_module_finite. The pinned Mathlib/NumberTheory/NumberField/Basic.lean supplies a finite ℤ-basis of O and integrality over ℤ of every element of O. Let m be the maximal ideal of the local ring V. By ValuationSubring.coe_mem_nonunits_iff, its image in E is V.nonunits.
2. We prove that every a ∈ O has image in V. Write α for its image in E and suppose α ∉ V. Since 0 ∈ V, α ≠ 0. The valuation-subring property gives y = α⁻¹ ∈ V. This element is not a unit in V: an inverse z ∈ V would satisfy yz = 1 in E, forcing z = α and contradicting α ∉ V. Thus y belongs to m.
3. Integrality of α gives a monic polynomial over ℤ vanishing at α. Its degree n is positive, since a monic polynomial of degree zero is 1 and cannot vanish in the field E. Write its equation as α^n + ∑_{i<n} c_i α^i = 0 with c_i ∈ ℤ. Dividing by α^n gives 1 + ∑_{i<n} c_i y^(n-i) = 0. Every integer belongs to V, and n-i ≥ 1 for each summand. Since y ∈ m and m is an ideal, each c_i y^(n-i) belongs to m. Closure under finite sums and negation implies 1 ∈ m. The equation holds in V because its embedding into E is injective. This contradicts the properness of m, proving the required containment for every a.
4. Consequently the canonical embedding O → E factors through a unital ring homomorphism f : O → V. Define q = f⁻¹(m), the ideal comap of m along f. Since m is a proper prime ideal, q is proper and prime: 1 does not map into m, and if f(ab) = f(a)f(b) belongs to m, primality of m puts f(a) or f(b) in m. By its definition and the identification of m with V.nonunits, for every a ∈ O we have a ∈ q if and only if its image in E belongs to V.nonunits.
5. The hypothesis V.LiesOverPrime ℓ states that (ℓ : E) ∈ V.nonunits. Ring homomorphisms preserve natural-number casts, so step 4 gives (ℓ : O) ∈ q. Primality of the natural number ℓ implies ℓ ≥ 2, hence ℓ ≠ 0. Characteristic zero makes (ℓ : O) nonzero. Therefore q cannot be the zero ideal.
6. Choose a finite ℤ-basis e_1,...,e_d of O. Each a ∈ O has an expansion a = ∑_i c_i e_i with c_i ∈ ℤ. Since ℓ > 0, write each coefficient as c_i = ℓ t_i + r_i with 0 ≤ r_i < ℓ. Because (ℓ : O) ∈ q, every term ℓ t_i e_i belongs to q. Thus a and ∑_i r_i e_i have the same class in O/q. The finite set of tuples (r_1,...,r_d), with each r_i in {0,...,ℓ-1}, therefore maps surjectively onto O/q. Hence O/q is finite.
7. Step 3 supplies the universal integral containment, and the ideal q from step 4 satisfies primality, nonzeroness, membership of ℓ, finiteness of the quotient, and the required nonunit-membership equivalence by steps 4–6. These are exactly the asserted conclusions.

## Key steps

1. Equip E with its number-field structure and use the finite integral basis of O_E.
2. If an algebraic integer lies outside V, its inverse is a nonunit of V.
3. Divide a monic integral equation by its leading power to force 1 into the maximal ideal, proving integral containment.
4. Contract the maximal ideal along O_E → V to obtain a prime ideal and the exact nonunit-membership equivalence.
5. Use LiesOverPrime and characteristic zero to show that the contracted prime contains ℓ and is nonzero.
6. Reduce integral-basis coefficients modulo ℓ to exhibit a finite set surjecting onto O_E/q.

## Reference use

### local-project

Queries:
- `LiesOverPrime|isDiscreteValuationRing_of_dedekind_domain|finite_quotient|nonunits`
- `integral|IntegrallyClosed|eq_of|localization|Localization|nonunits`
- `valuationSubring|ValuationSubring`
- `isIntegral|IsIntegral|isIntegrallyClosed|integralClosure`
- `p09_af497904fe_vloc_integral_center|p09_af497904fe_vloc_fraction_characterization`
- `python3 .humanize/vloc-split-diagnostic-k9wikt8l/check.py`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/project/Definitions/Def_FLTPrelim_Ramification.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/NumberTheory/NumberField/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/DedekindDomain/Dvr.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/Localization/AsSubring.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/Localization/AtPrime/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/DiscreteValuationRing/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/Valuation/ValuationSubring.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/Valuation/LocalSubring.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/IntegralClosure`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/Valuation/Integral.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/vloc-split-diagnostic-k9wikt8l/Types.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/vloc-split-diagnostic-k9wikt8l/Types.lean.log`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/vloc-split-diagnostic-k9wikt8l/report.json`

The snapshots match project 20574e45daf714e745af8e649c7b61b21eed5644 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d with clean tracked files; compiler dependencies match their clean pinned revisions. The inspected sources supply integer-ring integrality, finite freeness, Dedekind and fraction-field structures, embedded localizations, the DVR theorem, and localization maximal-ideal membership. LiesOverPrime is exactly membership of the prime's image in V.nonunits. The search for valuationSubring|ValuationSubring returned no matches in IntegralClosure or Valuation/Integral.lean; the broader search located integrally-closed instances in Valuation/LocalSubring.lean. Both proposed types elaborate after import Submission in the policy-authorized disposable copy. Additional examples check canonical integer-ring coercions, field division, nonunits interpretation, and the required number-field instances. The checked types and supporting declarations have only propext, Classical.choice, and Quot.sound as transitive axioms. Both proposed names are absent from the active DAG and imported environment. The diagnostic receipt records the required policy digest, omission of precisely lines 10–11, reversible original/build hashes, successful absence checks for all eight targets, and unchanged protected files. These are interface diagnostics, not comparator acceptance.


## Acceptance

The exact contract must pass the machine comparator and an independent reviewer's comparator rerun, without changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: Pending

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
