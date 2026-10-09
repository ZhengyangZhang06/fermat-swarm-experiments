<!-- theorem-id: fermat-p09/root.frobenius_approximation-a1.lift_unique_frobenius-a1.finite_frobenius_exists-a1.prime_frobenius_congruence-a1 -->

## Theorem `Submission.p09_af497904fe_ffe_prime_frobenius_congruence`

Let Ω = AlgebraicClosure ℚ and let E be an intermediate field of Ω/ℚ with E/ℚ finite-dimensional and Galois. Let ℓ be a natural prime. Write O = NumberField.RingOfIntegers E. If q is a prime ideal of O containing ℓ and O/q is finite, then there exists g ∈ Autℚ(E) such that γg(a) − a^ℓ ∈ q for every a ∈ O, where γg is the ring automorphism of O obtained by restricting g.

Node: `root.frobenius_approximation-a1.lift_unique_frobenius-a1.finite_frobenius_exists-a1.prime_frobenius_congruence-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/9

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/660

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p09_af497904fe_ffe_prime_frobenius_congruence`

```lean
∀ (E : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ E] [IsGalois ℚ E] (ℓ : ℕ), ℓ.Prime → ∀ q : Ideal (NumberField.RingOfIntegers E), q.IsPrime → (ℓ : NumberField.RingOfIntegers E) ∈ q → Finite (NumberField.RingOfIntegers E ⧸ q) → ∃ g : E ≃ₐ[ℚ] E, ∀ a : NumberField.RingOfIntegers E, NumberField.RingOfIntegers.mapRingEquiv g.toRingEquiv a - a ^ ℓ ∈ q
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

- Parent DAG node: `root.frobenius_approximation-a1.lift_unique_frobenius-a1.finite_frobenius_exists-a1`
- Child DAG node: `root.frobenius_approximation-a1.lift_unique_frobenius-a1.finite_frobenius_exists-a1.prime_frobenius_congruence-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix E, ℓ, and q satisfying the hypotheses, and write O for the integer ring and k = O/q. Since q is prime, k is a nontrivial domain. It is finite by hypothesis. For each nonzero c ∈ k, multiplication by c is injective and therefore surjective, so c has an inverse. Thus k is a field.
2. Let P be the contraction of q along ℤ → O. This is a proper prime ideal: contraction preserves primality, and 1 cannot belong to P because 1 does not belong to q. Since ℓ ∈ q, the ideal (ℓ) is contained in P. The quotient ℤ/(ℓ) is a field because ℓ is prime, so (ℓ) is maximal. Consequently P = (ℓ). The kernel of ℤ → k is therefore (ℓ), and k has characteristic ℓ. In particular, q lies over P, and k has its canonical ℤ/P-algebra structure.
3. Put G = Autℚ(E). This group is finite because E/ℚ is finite-dimensional. Each g ∈ G preserves O: applying g to a monic polynomial equation with integer coefficients gives the same monic equation for g(a). Applying this also to g⁻¹ proves that the restriction γg is a ring automorphism. These restrictions give a group action on O by ring automorphisms fixing every integer. This is the canonical action, and γg is precisely NumberField.RingOfIntegers.mapRingEquiv g.toRingEquiv.
4. Verify that every element of O fixed by G comes from ℤ. If a ∈ O is fixed, its image in E is fixed by all rational automorphisms. The theorem IsGalois.mem_range_algebraMap_iff_fixed in the pinned Mathlib/FieldTheory/Galois/Basic.lean gives r ∈ ℚ whose image is a. Since a is integral over ℤ and ℚ → E is injective, r satisfies a monic polynomial with integer coefficients in ℚ. Write r = u/v with u ∈ ℤ, v a positive integer, and gcd(u,v) = 1. A monic polynomial vanishing at r has positive degree n, since a monic constant polynomial is 1. Clearing denominators gives u^n + Σ_{i<n} c_i u^i v^(n−i) = 0. Hence v divides u^n. Coprimality implies gcd(u^n,v) = 1, so v = 1. Thus r is an integer and a lies in the image of ℤ → O. Together with the fact that the action fixes integers, this proves Algebra.IsInvariant ℤ O G and the required compatibility with integer scalars.
5. Define φ : k → k by φ(x) = x^ℓ. In characteristic ℓ, the binomial coefficients between the two endpoints in the ℓth-power expansion vanish, so φ preserves addition. It also preserves multiplication and 1. If φ(x) = φ(y), then (x−y)^ℓ = 0; because k is a field and ℓ > 0, x = y. Finiteness of k makes φ surjective, hence a ring automorphism. Every unital ring homomorphism fixes integer casts. Since every element of ℤ/P is represented by an integer, φ commutes with the algebra map from ℤ/P. Thus φ is an ℤ/P-algebra automorphism of k.
6. Apply Ideal.Quotient.stabilizerHom_surjective from the pinned Mathlib/RingTheory/Invariant/Basic.lean with A = ℤ, B = O, group G, lower ideal P, and upper ideal q. The action, finite-group hypothesis, invariant-ring property, prime ideal, scalar compatibility, and lies-over condition were established in steps 2–4. The theorem supplies an element of the stabilizer of q whose induced automorphism on k is φ. Let g be its underlying element of G.
7. For any a ∈ O, evaluating this equality of quotient automorphisms at the class of a gives [γg(a)] = φ([a]) = [a]^ℓ = [a^ℓ]. Equality in O/q is equivalent to γg(a) − a^ℓ ∈ q. This holds for every a and proves the stated existential conclusion.

## Key steps

1. Make the finite prime quotient O/q a field and identify its integer kernel as (ℓ).
2. Restrict the finite rational automorphism group to O and identify its fixed elements with integers.
3. Construct the ℓ-power automorphism of O/q over ℤ/(ℓ).
4. Lift that automorphism through Ideal.Quotient.stabilizerHom_surjective.
5. Evaluate on integer-ring representatives to obtain the required congruences.

## Reference use

### local-project

Queries:
- `valuation_localization|stabilizerHom_surjective|mem_range_algebraMap_iff_fixed|def IsFrobeniusAt|def decompositionSubgroup`
- `RingOfIntegers|map|equiv|smul|IsInvariant`
- `ResidueField|residue|smul|nonunits`
- `rg -n '"lean_name"|"status"|"proof_worktree"|"worktree"' .humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/dag.json`
- `/usr/bin/python3 .humanize/ffe-split-diagnostic-lnp4jtq3/check.py`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/NumberTheory/NumberField/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/FieldTheory/Galois/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/Invariant/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/Invariant/Galois.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/Frobenius.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/Valuation/RamificationGroup.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/LocalRing/ResidueField/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/project/Definitions/Def_EllipticCurve_FrobeniusTrace.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/ffe-split-diagnostic-lnp4jtq3/report.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/ffe-split-diagnostic-lnp4jtq3/types.json`

The snapshot pins project 20574e45daf714e745af8e649c7b61b21eed5644 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. It supplies the integer-ring restriction map, fixed-field criterion, stabilizer-surjectivity theorem, and exact decomposition-group residue action. No valuation_localization declaration was found in the snapshot; the active DAG already reserves that obligation as p09_af497904fe_luf_valuation_localization. Both proposed types elaborated after literal import Submission in a disposable compiler copy, and neither proposed name collided with the inspected DAG or imported environment. Definitional checks confirmed that mapRingEquiv restricts the field automorphism and agrees with the canonical integer-ring action. The types and checked library results have only propext, Classical.choice, and Quot.sound as transitive axioms. Diagnostics verified the specified policy digest, absence of all eight omitted targets, reversible removal of exactly lines 10 and 11, and preservation of protected sources and handoffs. These are interface diagnostics, not comparator acceptance.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: Pending

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
