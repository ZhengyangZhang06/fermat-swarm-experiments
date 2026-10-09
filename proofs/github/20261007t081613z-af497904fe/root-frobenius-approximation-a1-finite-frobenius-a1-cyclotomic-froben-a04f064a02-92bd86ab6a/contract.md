<!-- theorem-id: fermat-p09/root.frobenius_approximation-a1.finite_frobenius-a1.cyclotomic_frobenius_supply-a1.counting_mellin_continuation-a1.adic_cyclotomic_character-a1 -->

## Theorem `Submission.p09_af497904fe_rhc_20261009_adic_cyclotomic_character`

Let 𝒪 be a characteristic-zero commutative discrete valuation domain, complete and separated for its maximal ideal 𝔫. Let p be prime with p ∈ 𝔫. Let R be a commutative local 𝒪-algebra whose structural map is local, and let 𝔪 be its maximal ideal. There exists a homomorphism c : Autℚ(AlgebraicClosure ℚ) → Rˣ such that, for each n ≥ 0, agreement on some intermediate field finite-dimensional over ℚ implies c(σ)−c(τ) ∈ 𝔪^n. Moreover, for every prime ℓ ≠ p, every valuation subring P lying over ℓ, and every arithmetic Frobenius σ at P above ℓ, the underlying value of c(σ) equals ℓ in R.

Node: `root.frobenius_approximation-a1.finite_frobenius-a1.cyclotomic_frobenius_supply-a1.counting_mellin_continuation-a1.adic_cyclotomic_character-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/9

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/697

Prerequisites: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/381, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/382

Decomposition children: None

## Lean problem

Declaration: `Submission.p09_af497904fe_rhc_20261009_adic_cyclotomic_character`

```lean
∀ {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] [CharZero 𝒪] (p : ℕ) [Fact p.Prime], (p : 𝒪) ∈ IsLocalRing.maximalIdeal 𝒪 → ∀ {R : Type} [CommRing R] [IsLocalRing R] [Algebra 𝒪 R], IsLocalHom (algebraMap 𝒪 R) → ∃ c : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Rˣ, (∀ n : ℕ, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧ ∀ σ τ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), (∀ x ∈ F, σ x = τ x) → ((c σ : Rˣ) : R) - ((c τ : Rˣ) : R) ∈ IsLocalRing.maximalIdeal R ^ n) ∧ (∀ (ℓ : ℕ), ℓ.Prime → ℓ ≠ p → ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ → ∀ σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), P.IsFrobeniusAt σ ℓ → ((c σ : Rˣ) : R) = (ℓ : R))
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

- Parent DAG node: `root.frobenius_approximation-a1.finite_frobenius-a1.cyclotomic_frobenius_supply-a1.counting_mellin_continuation-a1`
- Child DAG node: `root.frobenius_approximation-a1.finite_frobenius-a1.cyclotomic_frobenius_supply-a1.counting_mellin_continuation-a1.adic_cyclotomic_character-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Put Ω = AlgebraicClosure ℚ and G = Autℚ(Ω). For each n ≥ 0, the sibling finite_cyclotomic_character theorem applies to the positive integer p^n. Choose its character χ_n and its finite controlling field F_n. Let A_n(g) be the least nonnegative representative of χ_n(g), considered as an integer, and let a_n(g) be its image in 𝒪.
2. We first justify the primitive roots needed to compare levels, without requiring an additional conclusion from that sibling's interface. For every positive k, X^k−1 has k distinct roots in Ω, since it splits and its derivative does not vanish at a root. These roots form a cyclic group: for a finite subgroup of a field, form the least common multiple d of element orders; suitable powers give elements of each maximal prime-power order, whose product has order d because the orders are coprime. All subgroup elements are roots of X^d−1, so the polynomial root bound forces this element to generate the group. Thus a primitive k-th root exists.
3. Suppose n ≤ m and choose a primitive p^m-th root ζ. Then ξ = ζ^(p^(m−n)) has order p^n. The sibling action formulas give ξ^(A_m(g)) = g(ξ) = ξ^(A_n(g)): the first equality follows by applying g to the indicated power of ζ. Consequently p^n divides A_m(g)−A_n(g) in ℤ. Since p ∈ 𝔫, the image of p^n belongs to 𝔫^n, and ideal absorption gives a_m(g)−a_n(g) ∈ 𝔫^n.
4. The homomorphism laws for χ_n imply that A_n(1)−1 and A_n(gh)−A_n(g)A_n(h) are divisible by p^n. Their images therefore belong to 𝔫^n. Apply the sibling adic_character_lift theorem to obtain b : G → 𝒪ˣ satisfying b(g)−a_n(g) ∈ 𝔫^n for all n,g. This includes n = 0, where divisibility by one and membership in 𝔫^0 are automatic.
5. Write f = algebraMap 𝒪 R. Map b(g) and its inverse through f to obtain a unit c(g) of R. The ring-homomorphism laws and the homomorphism laws for b make c : G → Rˣ a homomorphism.
6. Locality gives f(𝔫) ⊆ 𝔪, since maximal ideals consist of nonunits and a local homomorphism sends nonunits to nonunits. Expressing ideal powers by finite sums of products yields f(𝔫^n) ⊆ 𝔪^n for every n.
7. If σ and τ agree on F_n, the finite-character conclusion gives χ_n(σ) = χ_n(τ), hence a_n(σ) = a_n(τ). Subtracting the two lift congruences shows b(σ)−b(τ) ∈ 𝔫^n. Apply f and step 6 to obtain c(σ)−c(τ) ∈ 𝔪^n. The field F_n is finite-dimensional, proving the required finite-field control.
8. Let ℓ ≠ p be prime, let P lie over ℓ, and let σ be arithmetic Frobenius at P. Since distinct primes are coprime, ℓ does not divide p^n for any n. The finite-character Frobenius conclusion says χ_n(σ) is the unit represented by ℓ modulo p^n. Thus p^n divides A_n(σ)−ℓ, and a_n(σ)−ℓ ∈ 𝔫^n.
9. Adding the lift congruence gives b(σ)−ℓ ∈ 𝔫^n for every n. Separatedness of 𝒪 makes b(σ) = ℓ as underlying scalars. Mapping through f gives c(σ) = ℓ in R, completing both conclusions.

## Key steps

1. Choose finite cyclotomic characters and controlling fields at every p-power level.
2. Establish primitive roots and derive compatibility of the chosen exponent representatives.
3. Verify the approximate homomorphism laws and apply adic_character_lift.
4. Map the resulting units into R.
5. Use locality to transfer congruences between maximal-ideal powers.
6. Use all Frobenius congruences and separatedness to obtain exact Frobenius values.

## Reference use

### local-project

Queries:
- `rg -n '^(import|structure|def|theorem|lemma|namespace)|quadraticRelation|FrobeniusDensity' .humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/project/Definitions/Def_GaloisRep_Adic.lean`
- `rg -l 'FrobeniusDensity|cyclotomicCharacter|cyclotomicChar' .humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/project/Definitions`
- `rg -n 'modularCyclotomicCharacter|TODO|theorem.*spec|theorem.*unique' .humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/NumberTheory/Cyclotomic/CyclotomicCharacter.lean`
- `rg -n 'iInf_pow_smul_eq_bot_of_isLocalRing|exists_pow_inf_eq_pow_smul' .humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/Filtration.lean`
- `rg -n -i 'chebotarev|frobenius.*density|density.*frobenius' .humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/NumberTheory --glob '*.lean'`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/project/Definitions/Def_GaloisRep_Adic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/project/Definitions/Def_FLTPrelim_Ramification.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/project/Definitions/Def_EllipticCurve_FrobeniusTrace.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/NumberTheory/Cyclotomic/CyclotomicCharacter.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/AdicCompletion/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/Filtration.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/LinearAlgebra/Trace.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/Analysis/Complex/Polynomial/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/NumberTheory/NumberField/DedekindZeta.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/NumberTheory`

The manifest pins project 20574e45daf714e745af8e649c7b61b21eed5644 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. The inspected definitions specify adic continuity, trace, valuation nonunits and arithmetic residue Frobenius. Mathlib supplies finite cyclotomic characters, completeness including separatedness, finite-module Krull intersection, matrix-trace identification, the fundamental theorem of algebra and positive Dedekind-zeta residues. Divisibility compatibility of finite cyclotomic characters remains a TODO; the child proof supplies it. The project Definitions search found no matches for the searched character/density names, and the NumberTheory search found no Chebotarev or Frobenius-density declaration. The arithmetic child therefore supplies that argument explicitly.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: Pending

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
