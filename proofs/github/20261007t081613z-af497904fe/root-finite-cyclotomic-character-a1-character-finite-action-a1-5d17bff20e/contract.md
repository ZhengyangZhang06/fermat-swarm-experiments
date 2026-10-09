<!-- theorem-id: fermat-p09/root.finite_cyclotomic_character-a1.character_finite_action-a1 -->

## Theorem `Submission.p09_af497904fe_fcc_character_finite_action`

Let Ω = AlgebraicClosure ℚ and G = Autℚ(Ω). For every positive natural number N, there exist a monoid homomorphism χ : G → (ℤ/Nℤ)ˣ and an intermediate field F of Ω/ℚ such that F is finite-dimensional over ℚ, agreement of σ and τ on every element of F implies χ(σ) = χ(τ), and σ(ζ) = ζ^a for every σ ∈ G and every ζ ∈ Ω with ζ^N = 1, where a is the least nonnegative representative of the underlying residue class of χ(σ).

Node: `root.finite_cyclotomic_character-a1.character_finite_action-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/9

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/381

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p09_af497904fe_fcc_character_finite_action`

```lean
∀ (N : ℕ) [NeZero N], ∃ (χ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (ZMod N)ˣ) (F : IntermediateField ℚ (AlgebraicClosure ℚ)), FiniteDimensional ℚ F ∧ (∀ σ τ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), (∀ x ∈ F, σ x = τ x) → χ σ = χ τ) ∧ (∀ (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (ζ : AlgebraicClosure ℚ), ζ ^ N = 1 → σ ζ = ζ ^ ((χ σ : ZMod N).val))
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

- Parent DAG node: `root.finite_cyclotomic_character-a1`
- Child DAG node: `root.finite_cyclotomic_character-a1.character_finite_action-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix N > 0 and put μ = {ζ ∈ Ω : ζ^N = 1}. The polynomial X^N − 1 has degree N and splits over Ω. Every root is nonzero. Its derivative at a root ζ is Nζ^(N−1), which is nonzero because Ω has characteristic zero. Thus its roots are distinct and μ has exactly N elements. Multiplication preserves μ, and ζ⁻¹ = ζ^(N−1) for ζ ∈ μ, so μ is a finite commutative multiplicative group.
2. Let d be the least common multiple of the orders of the elements of μ. All these orders are positive, so d > 0. For each prime power q^e occurring in the prime factorization of d, some h ∈ μ has order q^e m with q not dividing m. The element h^m has order q^e: its k-th power is one exactly when q^e m divides mk, equivalently when q^e divides k. If commuting elements x and y have coprime orders r and s, then (xy)^k = 1 implies x^k = y^(−k). This common element lies in both cyclic subgroups, so its order divides both r and s and is one. Consequently r and s both divide k, hence rs divides k. Conversely (xy)^(rs) = 1. Therefore xy has order rs. Applying this argument successively to the selected prime-power-order elements produces g ∈ μ of order d. If d = 1, take the empty product g = 1.
3. Every element of μ has order dividing d and is therefore a root of X^d − 1. A nonzero polynomial of degree d over a field has at most d distinct roots: if a is a root, division by X − a writes the polynomial as (X − a)q, and every other root is a root of q; induction on the degree proves the bound. Thus |μ| ≤ d. The d distinct powers of g all belong to μ, so |μ| ≥ d. Hence d = N and the powers of g exhaust μ. Set ζ₀ = g. In particular, ζ₀ has order N, and equality between two powers of ζ₀ is equivalent to congruence of their exponents modulo N.
4. Every σ ∈ G preserves μ because σ(ζ)^N = σ(ζ^N), and its inverse also preserves μ. There is therefore a unique integer aσ with 0 ≤ aσ < N such that σ(ζ₀) = ζ₀^aσ. Write A(σ) for its residue class in ℤ/Nℤ. If ζ ∈ μ, write ζ = ζ₀^b. Then σ(ζ) = σ(ζ₀)^b = ζ₀^(aσ b) = ζ^aσ. Thus A(σ) describes the action on every element of μ, using precisely its least nonnegative representative.
5. The identity automorphism sends ζ₀ to ζ₀, so A(1) = 1 modulo N. Also (στ)(ζ₀) = σ(ζ₀^aτ) = ζ₀^(aσ aτ), so uniqueness modulo N gives A(στ) = A(σ)A(τ). In particular, A(σ)A(σ⁻¹) = 1 and A(σ⁻¹)A(σ) = 1. Define χ(σ) to be the unit with value A(σ) and inverse A(σ⁻¹). Equality of units follows from equality of their values, so the identity and multiplication equations for A prove that χ is a monoid homomorphism. Step 4 is exactly the required action formula for χ.
6. Let F = ℚ(ζ₀), viewed as an intermediate field of Ω/ℚ. Since every element of μ is a power of ζ₀, this also equals ℚ(μ). The element ζ₀ satisfies the nonzero polynomial X^N − 1 over ℚ and is therefore algebraic. Let m be its monic minimal polynomial, of positive degree r. The evaluation map identifies ℚ[ζ₀] with ℚ[X]/(m). The polynomial m is irreducible: a factorization into two smaller positive-degree polynomials would, after evaluation at ζ₀ in the field Ω, make one smaller-degree factor vanish, contradicting minimality. Hence ℚ[X]/(m) is a field and ℚ[ζ₀] = ℚ(ζ₀). Division by m shows that 1, ζ₀, …, ζ₀^(r−1) span F over ℚ. Thus F is finite-dimensional.
7. Suppose σ and τ agree on every element of F. Since ζ₀ ∈ F, we have ζ₀^aσ = σ(ζ₀) = τ(ζ₀) = ζ₀^aτ. The order of ζ₀ is N, so aσ and aτ represent the same residue class. Therefore A(σ) = A(τ), and unit extensionality gives χ(σ) = χ(τ). This proves all the required properties.
8. The argument includes N = 1: then μ = {1}, ζ₀ = 1, and the unique residue class has representative zero. The units of ℤ/1ℤ form the trivial group, F = ℚ, and the action formula reads σ(1) = 1^0 = 1.

## Key steps

1. Show that the N-th roots of unity form a multiplicative group with exactly N elements.
2. Construct an element of order equal to the least common multiple of all element orders.
3. Use the polynomial root bound to obtain a generator of order N.
4. Describe every automorphism by a unique exponent residue and prove its action on all roots.
5. Prove multiplicativity of exponent residues and use inverse automorphisms to obtain units.
6. Adjoin the generator and prove the resulting intermediate field is finite-dimensional.
7. Use agreement on the generator to prove equality of character values.
8. Check that the construction also covers N = 1.

## Reference use

### local-project

Queries:
- `IsFrobeniusAt|LiesOverPrime|cyclotomic|Cyclotomic|rootsOfUnity|IsPrimitiveRoot`
- `exists_primitiveRoot|natCard_rootsOfUnity|autToPow|pow_inj|pow_eq_one|mem_or_inv_mem|residue.*smul|smul.*residue`
- `frobenius.*rootsOfUnity|rootsOfUnity.*frobenius|IsFrobeniusAt.*pow|FrobeniusAt.*cyclotomic|cyclotomic.*FrobeniusAt`
- `IsAlgClosed|hasEnoughRootsOfUnity|HasEnoughRootsOfUnity`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/project/Definitions/Def_FLTPrelim_Ramification.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/project/Definitions/Def_EllipticCurve_FrobeniusTrace.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/NumberTheory/Cyclotomic/CyclotomicCharacter.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/RootsOfUnity/PrimitiveRoots.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/RootsOfUnity/EnoughRootsOfUnity.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/RootsOfUnity/AlgebraicallyClosed.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/Valuation/ValuationSubring.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/Valuation/RamificationGroup.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596`

The manifest pins project 20574e45daf714e745af8e649c7b61b21eed5644 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. LiesOverPrime means the prime is a nonunit; IsFrobeniusAt specifies membership in the decomposition subgroup and the power action on the residue field. Mathlib supplies primitive-root existence, IsPrimitiveRoot.autToPow, autToPow_spec, eq_pow_of_pow_eq_one, and modularCyclotomicCharacter.spec/unique. The valuation files supply the valuation dichotomy and decomposition-group action. The targeted search for a Frobenius roots-of-unity action theorem returned no matches. Installed dependencies were checked clean at their pinned revisions. Lean checked the proposed types and the cited primitive-root declarations; their axiom lists contain only propext, Classical.choice, and Quot.sound.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: Pending

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
