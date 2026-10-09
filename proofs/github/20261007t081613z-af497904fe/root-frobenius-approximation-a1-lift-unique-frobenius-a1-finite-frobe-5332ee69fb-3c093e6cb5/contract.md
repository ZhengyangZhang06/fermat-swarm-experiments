<!-- theorem-id: fermat-p09/root.frobenius_approximation-a1.lift_unique_frobenius-a1.finite_frobenius_exists-a1 -->

## Theorem `Submission.p09_af497904fe_luf_finite_frobenius_exists`

Let Ω = AlgebraicClosure ℚ, and let E be a finite-dimensional Galois intermediate field of Ω/ℚ. Let ℓ be a natural prime and V a valuation subring of E in which ℓ is a nonunit. There exists a rational automorphism g of E that preserves V and acts on its residue field by x ↦ x^ℓ, in the exact sense of V.IsFrobeniusAt g ℓ.

Node: `root.frobenius_approximation-a1.lift_unique_frobenius-a1.finite_frobenius_exists-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/9

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/643

Prerequisites: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/658

Decomposition children: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/672, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/673

## Lean problem

Declaration: `Submission.p09_af497904fe_luf_finite_frobenius_exists`

```lean
∀ (E : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ E] [IsGalois ℚ E] (ℓ : ℕ), ℓ.Prime → ∀ (V : ValuationSubring E), V.LiesOverPrime ℓ → ∃ g : E ≃ₐ[ℚ] E, V.IsFrobeniusAt g ℓ
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
- Child DAG node: `root.frobenius_approximation-a1.lift_unique_frobenius-a1.finite_frobenius_exists-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix E, ℓ, and V satisfying the hypotheses. Apply valuation_localization to obtain a nonzero prime q of O_E containing ℓ, the fraction description V = (O_E)_q, finiteness of k = O_E/q, and the equality between q and the contraction of V.nonunits. Since k is a nontrivial finite domain, it is a field.
2. The contraction of q to ℤ is a proper prime containing (ℓ). The ideal (ℓ) is maximal because ℓ is prime, so that contraction is exactly (ℓ). Thus k has characteristic ℓ and its base residue field is ℤ/(ℓ), identified with 𝔽_ℓ.
3. Let G = Gal(E/ℚ), a finite group because E/ℚ is finite Galois. Its action on E restricts to O_E: rational automorphisms fix the integer coefficients of monic integral equations, and the same applies to their inverses. The action fixes ℤ. Its invariant integer ring is exactly ℤ. Indeed, an integer fixed by every element of G lies in the image of ℚ by IsGalois.mem_range_algebraMap_iff_fixed in the pinned Mathlib/FieldTheory/Galois/Basic.lean. A rational number a/b in lowest terms that satisfies a monic integral equation has b dividing a^n after clearing denominators; coprimality forces the positive denominator b to equal 1. Hence it is an integer. This verifies the invariant-ring hypothesis for the canonical G-action on O_E.
4. The map φ : k → k defined by φ(x) = x^ℓ is a ring homomorphism in characteristic ℓ. It is injective, since φ(x) = φ(y) implies (x−y)^ℓ = 0 and a field has no nonzero nilpotents. Finiteness of k makes it surjective. It fixes the prime field, because it is a unital ring homomorphism and every element of 𝔽_ℓ is represented by an integer. Thus φ is an automorphism of k over ℤ/(ℓ).
5. Apply Ideal.Quotient.stabilizerHom_surjective from the pinned Mathlib/RingTheory/Invariant/Basic.lean with base ring ℤ, upper ring O_E, group G, base prime (ℓ), and upper prime q. The rings, finite group, invariant-ring property, prime property, and contraction condition were established above. Surjectivity produces g ∈ G stabilizing q whose action on O_E/q is φ.
6. Both g and g⁻¹ preserve O_E and q. They therefore preserve the fractions with denominator outside q, so they preserve V. The residue map O_E → V/m_V has kernel q by the nonunit characterization from valuation_localization. It induces an injective map k → V/m_V. This map is surjective: every element of V is a/b with b ∉ q, and its residue is the image of [a]/[b] in the field k. Hence it is a residue-field isomorphism.
7. This isomorphism intertwines the action induced by g on both residue fields. On an integer representative, both actions send its residue to the residue of its image under g; on fractions the same equality follows by preservation of division. The action on k is φ, so the action on every residue class of V is the ℓ-power map. Together with preservation of V, this gives the witness of membership in V.decompositionSubgroup ℚ and the residue-action equality required by the frozen definition of V.IsFrobeniusAt g ℓ. The resulting g proves the existential statement.

## Key steps

1. Identify V with an integer localization having finite residue field of characteristic ℓ.
2. Verify that the finite rational Galois group acts on the integer ring with invariant ring ℤ.
3. Construct the ℓ-power automorphism of the finite residue field.
4. Lift it using Ideal.Quotient.stabilizerHom_surjective.
5. Transfer the lifted action through the equivariant residue-field identification to the frozen valuation Frobenius predicate.

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

The exact contract must pass the machine comparator and an independent reviewer's comparator rerun, without changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: Pending

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
