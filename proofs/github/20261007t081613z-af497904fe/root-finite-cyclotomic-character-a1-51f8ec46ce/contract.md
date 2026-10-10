<!-- theorem-id: fermat-p09/root.finite_cyclotomic_character-a1 -->

## Theorem `Submission.p09_af497904fe_finite_cyclotomic_character`

Put Ω = AlgebraicClosure ℚ and G = Autℚ(Ω). For every positive natural number N, there exist a homomorphism χ : G → (ℤ/Nℤ)ˣ and an intermediate field F of Ω/ℚ finite-dimensional over ℚ such that: agreement of σ and τ on F implies χ(σ) = χ(τ); whenever ζ ∈ Ω satisfies ζ^N = 1, σ(ζ) = ζ^a for the least nonnegative representative a of χ(σ); and, for every prime ℓ not dividing N, every valuation subring P of Ω with ℓ a nonunit, and every arithmetic Frobenius σ at P above ℓ, χ(σ) equals the unit represented by ℓ modulo N.

Node: `root.finite_cyclotomic_character-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/9

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/9

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/644, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/645

## Lean problem

Declaration: `Submission.p09_af497904fe_finite_cyclotomic_character`

```lean
∀ (N : ℕ) [NeZero N], ∃ (χ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (ZMod N)ˣ) (F : IntermediateField ℚ (AlgebraicClosure ℚ)), FiniteDimensional ℚ F ∧ (∀ σ τ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), (∀ x ∈ F, σ x = τ x) → χ σ = χ τ) ∧ (∀ (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (ζ : AlgebraicClosure ℚ), ζ ^ N = 1 → σ ζ = ζ ^ ((χ σ : ZMod N).val)) ∧ (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (P : ValuationSubring (AlgebraicClosure ℚ)), P.LiesOverPrime ℓ → ∀ σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), P.IsFrobeniusAt σ ℓ → χ σ = ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓN))
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

- Parent DAG node: `root`
- Child DAG node: `root.finite_cyclotomic_character-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Let μ_N = {ζ ∈ Ω : ζ^N = 1}. The polynomial X^N−1 splits in Ω and has no repeated roots, since its derivative N X^(N−1) is nonzero at every root in characteristic zero. Thus μ_N has exactly N elements. They are nonzero and form a multiplicative group.
2. Every finite multiplicative subgroup H of a field is cyclic. Let d be the least common multiple of its element orders. For each maximal prime power r^a dividing d, choose an element whose order has r-part r^a and raise it to the prime-to-r part of its order. This gives an element of order r^a. Products of these elements have order d: for commuting factors of coprime orders, a power of their product equal to one makes corresponding powers lie in the intersection of the cyclic subgroups; that intersection is trivial because element orders divide both coprime orders. Every element of H is a root of X^d−1. A nonzero degree-d polynomial over a field has at most d roots, by division by X−a and induction on degree. Therefore |H| ≤ d, whereas the constructed element has d distinct powers. It generates H. In particular, choose ζ₀ generating μ_N, of order N.
3. Each σ ∈ G acts bijectively on μ_N, so σ(ζ₀) = ζ₀^a for a unique residue class a modulo N. This power has order N exactly when a is coprime to N, since its order is N/gcd(a,N). Consequently a defines a unit χ(σ). Every root is a power of ζ₀, so σ(ζ) = ζ^a for every ζ ∈ μ_N. Taking the least nonnegative representative does not change these powers. Composition multiplies the exponents, and the identity has exponent one modulo N. Uniqueness of the exponent proves that χ is a monoid homomorphism.
4. Let F = ℚ(μ_N) inside Ω. This is finite-dimensional: adjoining one algebraic element gives a finite extension spanned by powers below its minimal-polynomial degree, and μ_N is finite. If σ and τ agree on F, they agree on ζ₀. Its order N then implies equality of the underlying residue classes and hence χ(σ) = χ(τ).
5. Fix a prime ℓ not dividing N and P with P.LiesOverPrime ℓ. Every ζ ∈ μ_N belongs to P. Otherwise the valuation property puts ζ⁻¹ in P, but ζ = (ζ⁻¹)^(N−1) then also belongs to P. Moreover ζ⁻¹ = ζ^(N−1) belongs to P, so ζ is a unit. The residue field k(P) has characteristic ℓ: the proper kernel of ℤ → k(P) contains (ℓ), because ℓ is a nonunit of P, and (ℓ) is maximal in ℤ.
6. Reduction is injective on μ_N. If ξ ∈ μ_N reduces to one and ξ ≠ 1, factor ξ^N−1 and cancel ξ−1 in Ω to obtain 1+ξ+⋯+ξ^(N−1) = 0. Reduction gives N = 0 in characteristic ℓ, contradicting ℓ ∤ N. Apply this to the quotient of two roots with equal reductions to prove injectivity.
7. If P.IsFrobeniusAt σ ℓ, σ preserves P and its induced action on k(P) is the ℓ-power map. Hence σ(ζ) and ζ^ℓ have equal reductions for every ζ ∈ μ_N. Both are in μ_N, so step 6 makes them equal. At ζ₀ this identifies χ(σ) with ℓ modulo N. Units are determined by their underlying values, so this is exactly the ZMod.unitOfCoprime in the statement.
8. For N = 1, μ_N = {1} and (ℤ/Nℤ)ˣ is trivial. The construction still works, and the least representative is zero, giving σ(1) = 1^0 = 1. Thus all assertions include this case.

## Key steps

1. Show that μ_N has N elements and is cyclic.
2. Define the character by the unique unit exponent and prove its homomorphism laws.
3. Use the finite field generated by μ_N to control the character.
4. Prove valuation-unit membership and injectivity of reduction away from N.
5. Identify arithmetic Frobenius with the specified residue-class unit.

## Reference use

### local-project

Queries:
- `rg -n 'modularCyclotomicCharacter|theorem spec|theorem unique|TODO|IsAdicComplete|exists_pow_inf_eq_pow_smul|iInf_pow_smul_eq_bot_of_isLocalRing|trace_eq_matrix_trace' .humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/NumberTheory/Cyclotomic/CyclotomicCharacter.lean .humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/AdicCompletion/Basic.lean .humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/Filtration.lean .humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/LinearAlgebra/Trace.lean`
- `rg -n 'Chebotarev|chebotarev|FrobeniusDensity' project/Definitions mathlib/Mathlib/NumberTheory mathlib/Mathlib/RingTheory`
- `rg -n 'smul_eq_mul|theorem sub_apply|theorem smul_apply' mathlib/Mathlib/Algebra/Algebra/Operations.lean mathlib/Mathlib/Algebra/Module/LinearMap/Defs.lean`
- `python3 .humanize/decomposition-interface-fresh-tdjulkl6/finish.py`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/project/Definitions/Def_GaloisRep_Adic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/project/Definitions/Def_FLTPrelim_Ramification.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/project/Definitions/Def_EllipticCurve_FrobeniusTrace.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/NumberTheory/Cyclotomic/CyclotomicCharacter.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/AdicCompletion/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/Filtration.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/LinearAlgebra/Trace.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/Algebra/Algebra/Operations.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/Algebra/Module/LinearMap/End.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/Algebra/Module/LinearMap/Defs.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/Valuation/RamificationGroup.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/Frobenius.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/Analysis/Complex/Polynomial/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/NumberTheory/NumberField/DedekindZeta.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/decomposition-interface-fresh-tdjulkl6/report.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/decomposition-interface-fresh-tdjulkl6/name-reservations.json`

The snapshot matches project commit 20574e45daf714e745af8e649c7b61b21eed5644 and mathlib commit db584cd6d46c92f209a44c0f1c829460d327499d; both tracked trees are clean. Relative search paths above use the stated snapshot root. The definitions confirm the exact continuity, trace, LiesOverPrime and arithmetic IsFrobeniusAt predicates. Mathlib supplies finite cyclotomic characters, adic completeness, Artin–Rees, finite-module separation and matrix trace identification; cyclotomic compatibility is explicitly a TODO and is proved below. The Chebotarev/FrobeniusDensity search returned no matches in its three searched subtrees. RingTheory/Frobenius.lean supplies Frobenius at a given prime, not the required prime-distribution assertion. Fresh disposable checks passed for all eight unchanged types after both import Submission and import Challenge, including composition, pointwise linear-map operations and ideal-action probes. Inspected type and supporting-declaration axiom dependencies are subsets of propext, Classical.choice and Quot.sound. The report records the exact policy-authorized omissions, a successful eight-target absence probe, original/build hashes and unchanged protected files. These are interface diagnostics, not comparator acceptance or accepted child proofs.


## Acceptance

The exact contract must pass the machine comparator and an independent reviewer's comparator rerun, without changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/703

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
