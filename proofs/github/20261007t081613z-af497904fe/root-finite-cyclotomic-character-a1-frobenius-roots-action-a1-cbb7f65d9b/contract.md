<!-- theorem-id: fermat-p09/root.finite_cyclotomic_character-a1.frobenius_roots_action-a1 -->

## Theorem `Submission.p09_af497904fe_fcc_frobenius_roots_action`

Let Ω = AlgebraicClosure ℚ. Let N be a positive natural number and let ℓ be prime with ℓ not dividing N. Let P be a valuation subring of Ω such that (ℓ : Ω) belongs to P.nonunits. If σ ∈ Autℚ(Ω) satisfies P.IsFrobeniusAt σ ℓ, meaning that σ preserves P and acts on its residue field by x ↦ x^ℓ, then σ(ζ) = ζ^ℓ for every ζ ∈ Ω satisfying ζ^N = 1.

Node: `root.finite_cyclotomic_character-a1.frobenius_roots_action-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/9

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/381

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/656, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/657

## Lean problem

Declaration: `Submission.p09_af497904fe_fcc_frobenius_roots_action`

```lean
∀ (N : ℕ) [NeZero N] (ℓ : ℕ), ℓ.Prime → ¬ ℓ ∣ N → ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ → ∀ σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), P.IsFrobeniusAt σ ℓ → ∀ ζ : AlgebraicClosure ℚ, ζ ^ N = 1 → σ ζ = ζ ^ ℓ
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
- Child DAG node: `root.finite_cyclotomic_character-a1.frobenius_roots_action-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix N, ℓ, P and σ satisfying the hypotheses, and write μ = {η ∈ Ω : η^N = 1}. Every η ∈ μ is nonzero because N > 0. We have η⁻¹ = η^(N−1), and also η = (η⁻¹)^(N−1). The valuation-subring property gives η ∈ P or η⁻¹ ∈ P. In the second case, closure under powers and the latter identity give η ∈ P as well. The former identity then gives η⁻¹ ∈ P. Thus every element of μ belongs to P and is a unit of P.
2. Let k be the residue field of the local ring P, and let red : P → k be the residue homomorphism. The hypothesis P.LiesOverPrime ℓ says that ℓ is a nonunit of P. Nonunits of a local ring form its maximal ideal, so red(ℓ) = 0. The kernel of the unital map ℤ → k is a proper ideal containing ℓℤ. Since ℓ is prime, ℓℤ is maximal; therefore this kernel equals ℓℤ. Consequently k has characteristic ℓ. In particular, the image of N in k is nonzero because ℓ does not divide N.
3. Suppose ξ ∈ μ has residue one. If ξ ≠ 1, the geometric-sum identity gives (ξ − 1)(1 + ξ + ⋯ + ξ^(N−1)) = ξ^N − 1 = 0 in Ω. Since Ω is a field and ξ − 1 ≠ 0, the sum is zero. Every term belongs to P by step 1, and the inclusion P → Ω is injective, so the same sum is zero in P. Reducing it gives 1 + 1 + ⋯ + 1 = 0 with N terms, contradicting the nonvanishing of N in k established in step 2. Therefore ξ = 1.
4. Reduction is injective on μ. Indeed, suppose η and θ belong to μ and have equal residues. Step 1 shows that θ and θ⁻¹ are units in P, so their residues are mutually inverse and nonzero. The element ξ = ηθ⁻¹ belongs to P, satisfies ξ^N = η^N(θ^N)⁻¹ = 1, and has residue red(η)red(θ)⁻¹ = 1. Step 3 gives ξ = 1, hence η = θ.
5. Unpack P.IsFrobeniusAt σ ℓ. It supplies membership of σ in the decomposition subgroup of P and asserts that its induced action on k is x ↦ x^ℓ. Membership in the decomposition subgroup makes σ an automorphism of P. By the definition of the induced residue action, red(σ(u)) equals the action of σ on red(u) for every u ∈ P. Hence red(σ(u)) = red(u)^ℓ = red(u^ℓ).
6. Now let ζ ∈ Ω satisfy ζ^N = 1. Step 1 allows us to apply step 5 to ζ, yielding equal residues for σ(ζ) and ζ^ℓ. Both elements lie in μ: (σ(ζ))^N = σ(ζ^N) = 1, and (ζ^ℓ)^N = (ζ^N)^ℓ = 1. Injectivity from step 4 therefore gives σ(ζ) = ζ^ℓ, as required.
7. No step excludes N = 1. In that case ζ^N = 1 forces ζ = 1, and the conclusion is σ(1) = 1^ℓ = 1.

## Key steps

1. Use the valuation dichotomy and root-of-unity identities to place every root and its inverse in P.
2. Identify the kernel of ℤ → k(P) as ℓℤ and conclude that N is nonzero in the residue field.
3. Use the geometric-sum identity to show that a root reducing to one equals one.
4. Apply this result to quotients to prove injectivity of reduction on the N-th roots of unity.
5. Unpack Frobenius and residue-action compatibility to obtain equal reductions of σ(ζ) and ζ^ℓ.
6. Check both elements remain N-th roots of unity and apply injectivity.
7. Include the case N = 1.

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

The exact contract must pass the machine comparator and an independent reviewer's comparator rerun, without changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/684

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
