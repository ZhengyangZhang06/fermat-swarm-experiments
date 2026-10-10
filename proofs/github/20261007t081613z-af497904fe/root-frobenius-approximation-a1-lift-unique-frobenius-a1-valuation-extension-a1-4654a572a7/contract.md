<!-- theorem-id: fermat-p09/root.frobenius_approximation-a1.lift_unique_frobenius-a1.valuation_extension-a1 -->

## Theorem `Submission.p09_af497904fe_luf_valuation_extension`

Let Ω = AlgebraicClosure ℚ. Let E and F be finite-dimensional intermediate fields of Ω/ℚ with E ⊆ F. Let ℓ be a natural prime, and let V be a valuation subring of E in which ℓ is a nonunit. There exists a valuation subring W of F in which ℓ is a nonunit and whose inverse image under the canonical inclusion E → F is exactly V.

Node: `root.frobenius_approximation-a1.lift_unique_frobenius-a1.valuation_extension-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/9

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/643

Prerequisites: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/658

Decomposition children: None

## Lean problem

Declaration: `Submission.p09_af497904fe_luf_valuation_extension`

```lean
∀ (E F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ E] [FiniteDimensional ℚ F] (hEF : E ≤ F) (ℓ : ℕ), ℓ.Prime → ∀ (V : ValuationSubring E), V.LiesOverPrime ℓ → ∃ W : ValuationSubring F, W.LiesOverPrime ℓ ∧ ∀ x : E, IntermediateField.inclusion hEF x ∈ W ↔ x ∈ V
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

- Parent DAG node: `root.frobenius_approximation-a1.lift_unique_frobenius-a1`
- Child DAG node: `root.frobenius_approximation-a1.lift_unique_frobenius-a1.valuation_extension-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix E ⊆ F, ℓ, and V as in the statement. Apply valuation_localization to E, ℓ, and V. It gives a nonzero prime q of O_E containing ℓ, identifies V with the fractions defining A = (O_E)_q, and identifies q with the contraction of the maximal ideal of V.
2. The field inclusion E → F induces an injective ring map O_E → O_F: a monic integral equation remains valid after applying the inclusion. The upper ring O_F is integral over O_E, because every element of O_F satisfies a monic polynomial with coefficients in ℤ, and those coefficients also lie in O_E.
3. There is a prime q' of O_F contracting to q. Here is the integral prime-lifting argument, also provided by Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain in the pinned Mathlib/RingTheory/Ideal/GoingUp.lean. Let S = O_E \ q. Localize O_E and O_F at S and its image, obtaining A and B. These are nonzero rings, and B is integral over A. Choose a maximal ideal M of B. Its contraction p to A is maximal: B/M is a field integral over the embedded domain A/p. For any nonzero c ∈ A/p, its inverse in B/M is integral over A/p. Multiplying a monic equation for c⁻¹ by c^{n-1} expresses c⁻¹ as an element of A/p. Thus A/p is a field. Since A is local, p is its maximal ideal qA. Contract M to O_F to obtain q'; contraction through the localization maps then gives q' ∩ O_E = q.
4. In particular, q' contains the image of ℓ and is nonzero, because F has characteristic zero. The integer ring O_F is Dedekind with fraction field F. Therefore the pinned DVR-localization theorem makes (O_F)_{q'} a valuation ring. Embed this localization in F and call its image W. Its maximal ideal consists of fractions with numerator in q' and denominator outside q'. The image of ℓ lies in this maximal ideal, so W.LiesOverPrime ℓ holds.
5. A lower denominator b outside q maps outside q', by contraction. Consequently every fraction in A maps into W. If a fraction belongs to the maximal ideal of A, its numerator lies in q and maps into q', while its denominator remains outside q'; hence it maps into the maximal ideal of W. Through the identification A = V from step 1, the inclusion E → F therefore maps V into W and carries the maximal ideal of V into that of W.
6. Let x ∈ E lie outside V. Then x ≠ 0, and the valuation property gives x⁻¹ in the maximal ideal of V: it belongs to V but cannot be a unit there. Its image consequently belongs to the maximal ideal of W. If the image of x belonged to W, it would invert that nonunit, a contradiction. Hence the image of x does not belong to W. Combined with step 5, this proves that the inverse image of W is exactly V, completing the required conjunction.

## Key steps

1. Represent V as the localization at its contracted integer prime.
2. Use integrality of the upper integer ring to lift that prime.
3. Construct W from the upper DVR localization and retain ℓ in its maximal ideal.
4. Show that the inclusion carries V and its maximal ideal into W and its maximal ideal.
5. Exclude additional lower-field elements by applying the maximal-ideal argument to their inverses.

## Reference use

### local-project

Queries:
- `IsFrobeniusAt|LiesOverPrime|stabilizerHom_surjective|isDiscreteValuationRing_of_dedekind_domain`
- `RingOfIntegers|isDedekindDomain|isFractionRing|finite|free`
- `exists.*[Ff]robenius|[Ff]robenius.*exists|lift.*[Ff]robenius`
- `nonunits|mem_nonunits|isUnit`
- `exists.*[Ll]iesOver|exists.*[Uu]nder|exists_ideal_over|liesOver`
- `fixedField.*bot|fixed_by_all|mem_bot|mem_range|fixedField_top|isInvariant`
- `p09_af497904fe_luf_`
- `python3 .humanize/luf-split-diagnostic-20261009/check.py`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/project/Definitions/Def_FLTPrelim_Ramification.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/project/Definitions/Def_EllipticCurve_FrobeniusTrace.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/NumberTheory/NumberField/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/DedekindDomain/Dvr.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/Ideal/GoingUp.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/Invariant/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/Invariant/Galois.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/Frobenius.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/Valuation/ValuationSubring.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/Valuation/RamificationGroup.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/FieldTheory/Galois/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/luf-split-diagnostic-20261009/Types.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/luf-split-diagnostic-20261009/Types.lean.log`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/luf-split-diagnostic-20261009/report.json`

The snapshots are clean at project 20574e45daf714e745af8e649c7b61b21eed5644 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d; compiler dependencies also match their clean pinned revisions. The inspected files supply integer-ring finiteness and Dedekind properties, DVR localizations, integral prime lifting, fixed-ring identification, residue-action surjectivity, and the exact valuation Frobenius predicates. The targeted lifting search found no direct implementation of the supplied algebraic-closure lifting statement in the searched directories. All four proposed types elaborate after import Submission. Additional checks verify integer-ring actions, field inclusions, automorphism multiplication, and the frozen residue action. Checked types and supporting declarations depend only on propext, Classical.choice, and Quot.sound. Proposed names were absent from the active DAG and imported environment. The successful diagnostic receipt records policy digest 96fc18eb6b8cbdad1beec37ca318ab2cf08ac1dda8ebf7cbfe1d6d51abf32f96, omission of precisely lines 10–11, reversible original/build hashes, a successful Lean absence probe for all eight targets, and unchanged protected files. These are interface diagnostics, not proof or comparator acceptance.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/758

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
