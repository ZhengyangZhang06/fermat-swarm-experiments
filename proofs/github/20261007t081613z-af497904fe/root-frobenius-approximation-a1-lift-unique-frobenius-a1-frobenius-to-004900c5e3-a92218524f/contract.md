<!-- theorem-id: fermat-p09/root.frobenius_approximation-a1.lift_unique_frobenius-a1.frobenius_tower_limit-a1 -->

## Theorem `Submission.p09_af497904fe_luf_frobenius_tower_limit`

Let Ω = AlgebraicClosure ℚ. Let F_i, indexed by ℕ, be an increasing sequence of finite-dimensional Galois intermediate fields of Ω/ℚ whose union is Ω. Let ℓ be a natural number and V_i a valuation subring of F_i for every i. Assume ℓ is a nonunit of every V_i, that for i ≤ j the inverse image of V_j under F_i → F_j is V_i, and that every V_i admits a rational automorphism inducing the ℓ-power map on its residue field. Then there exist a valuation subring P of Ω and a rational automorphism τ of Ω such that ℓ is a nonunit of P, P restricts to V_i for every i, and P.IsFrobeniusAt τ ℓ. Moreover, for each i there exists a rational automorphism g_i of F_i with V_i.IsFrobeniusAt g_i ℓ whose underlying map agrees with τ on F_i.

Node: `root.frobenius_approximation-a1.lift_unique_frobenius-a1.frobenius_tower_limit-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/9

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/643

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/674, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/675, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/676

## Lean problem

Declaration: `Submission.p09_af497904fe_luf_frobenius_tower_limit`

```lean
∀ (F : ℕ → IntermediateField ℚ (AlgebraicClosure ℚ)) (hmono : Monotone F), (∀ i : ℕ, FiniteDimensional ℚ (F i)) → (∀ i : ℕ, IsGalois ℚ (F i)) → (∀ x : AlgebraicClosure ℚ, ∃ i : ℕ, x ∈ F i) → ∀ (V : (i : ℕ) → ValuationSubring (F i)) (ℓ : ℕ), (∀ i : ℕ, (V i).LiesOverPrime ℓ) → (∀ (i j : ℕ) (hij : i ≤ j) (x : F i), IntermediateField.inclusion (hmono hij) x ∈ V j ↔ x ∈ V i) → (∀ i : ℕ, ∃ g : F i ≃ₐ[ℚ] F i, (V i).IsFrobeniusAt g ℓ) → ∃ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ ∧ (∀ (i : ℕ) (x : F i), (x : AlgebraicClosure ℚ) ∈ P ↔ x ∈ V i) ∧ ∃ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt τ ℓ ∧ ∀ i : ℕ, ∃ g : F i ≃ₐ[ℚ] F i, (V i).IsFrobeniusAt g ℓ ∧ ∀ x : F i, τ (x : AlgebraicClosure ℚ) = ((g x : F i) : AlgebraicClosure ℚ)
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
- Child DAG node: `root.frobenius_approximation-a1.lift_unique_frobenius-a1.frobenius_tower_limit-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix the tower F_i, the valuation rings V_i, and ℓ with all the stated hypotheses. Identify each F_i with its given subfield of Ω. Let m_i be the image in F_i of the maximal ideal of V_i. For each i, let X_i consist of the rational automorphisms a of F_i satisfying V_i.IsFrobeniusAt a ℓ. These sets are nonempty by hypothesis and finite because each F_i/ℚ is a finite extension and therefore has finitely many rational automorphisms.
2. For i ≤ j, the assumed contraction equality embeds V_i into V_j. It also contracts m_j exactly to m_i. Indeed, for any element x of a valued field, membership in the valuation ring's nonunits is equivalent to x = 0 or x⁻¹ lying outside the ring; this is ValuationSubring.mem_nonunits_iff_or in the pinned library. The field inclusion preserves zero and inverses, and membership of a lower-field element in V_j is equivalent to membership in V_i. Applying the criterion therefore proves contraction of nonunits. Consequently the maps V_i → V_j induce injective residue-field maps, compatible under composition.
3. For i ≤ j, every rational automorphism a of F_j restricts to a rational automorphism of F_i. Normality of F_i/ℚ ensures that the rational embedding obtained by restricting a maps F_i into itself; applying the same fact to a⁻¹ proves bijectivity on F_i. If a ∈ X_j, this restriction preserves V_i: use preservation of V_j and the equality V_j ∩ F_i = V_i, for both a and a⁻¹. Its residue action is the ℓ-power map. To see this, embed a lower residue class into the upper residue field. The residue embedding commutes with the restricted action, and the upper action is the ℓ-power map. Injectivity from step 2 gives the desired equality in the lower residue field. Thus restriction defines r_ij : X_j → X_i. Checking on field elements gives r_ii = id and r_ik = r_ij ∘ r_jk whenever i ≤ j ≤ k.
4. Choose y_j ∈ X_j for every j. Construct infinite subsets S_i of ℕ and elements g_i ∈ X_i recursively. For i = 0 start with ℕ; at a later step start with S_{i-1}. Remove the finitely many indices j < i. The remaining set is infinite, and the map j ↦ r_ij(y_j) takes values in the finite set X_i. At least one fiber is infinite, because otherwise the whole remaining set would be a finite union of finite sets. Choose such a fiber as S_i and its value as g_i. Thus every j ∈ S_i satisfies j ≥ i and r_ij(y_j) = g_i, and the sets S_i are nested.
5. If i ≤ k, choose j ∈ S_k. Then j ≥ k and j ∈ S_i. The restriction identities give r_ik(g_k) = r_ik(r_kj(y_j)) = r_ij(y_j) = g_i. Hence the automorphisms g_i form a compatible family. This argument uses only finiteness and nonemptiness of the X_i, not surjectivity of the restriction maps.
6. Define τ(x) = g_i(x) whenever x ∈ F_i. Exhaustion provides such an i, and compatibility makes the definition independent of the choice: two stages embed into their common stage with index their maximum. Addition, multiplication, one, and rational scalars are respected because any finitely many arguments lie in a common stage. The inverses g_i⁻¹ are compatible as well. For x ∈ F_i and j ≥ i, the element g_i⁻¹(x) lies in F_i and maps under g_j to x, so uniqueness of the preimage under g_j gives g_j⁻¹(x) = g_i⁻¹(x). Their union is a two-sided inverse of τ. Thus τ is a rational field automorphism of Ω restricting to every g_i.
7. Regard the V_i and m_i as subsets of Ω and put P = ⋃_i V_i and m = ⋃_i m_i. Step 2 makes both families nested. The set P is a subring: zero, one, additive inverses, sums, and products are checked in a common stage. For any nonzero x ∈ Ω choose i with x ∈ F_i. The valuation property in F_i puts either x or x⁻¹ in V_i and hence in P. Thus P is a valuation subring of Ω.
8. The set m is a proper ideal of P. Addition and multiplication by elements of P can be checked in a common stage, and 1 lies in none of the m_i. If x ∈ m_i had an inverse in P, that inverse would belong to some V_j. Passing to a common later stage would invert an element of its maximal ideal, a contradiction. Thus every element of m is a nonunit of P. Conversely, if x ∈ P is outside m, choose i with x ∈ V_i. Then x is outside m_i, so is a unit in V_i and therefore a unit in P. Hence m is precisely the set of nonunits of P. Since ℓ belongs to m_0 by hypothesis, P.LiesOverPrime ℓ follows.
9. The ring P restricts to V_i for every i. Membership in V_i directly implies membership in P. Conversely, if x ∈ F_i belongs to P, it belongs to some V_j. Choose k ≥ i,j. Its image belongs to V_k, and the assumed contraction equality from F_k to F_i gives x ∈ V_i. This proves the required equivalence for all i and all x ∈ F_i.
10. Each g_i and its inverse preserves V_i. Since τ and τ⁻¹ restrict to these automorphisms, both preserve P, so τ belongs to P.decompositionSubgroup ℚ. If x ∈ V_i, the Frobenius property of g_i says that the residue of g_i(x)−x^ℓ vanishes, equivalently that this difference belongs to m_i. In Ω the same difference is τ(x)−x^ℓ and belongs to m, the maximal ideal of P. Every element of P lies in some V_i, and every residue class has a representative in P. The action of τ on every residue class of P is therefore its ℓ-th power, exactly as required by the frozen definition of P.IsFrobeniusAt τ ℓ. Finally, for each i use the selected g_i as the existential witness: it belongs to X_i and agrees with τ on F_i by step 6. Together with steps 8 and 9, this proves every conjunct of the statement.

## Key steps

1. Form finite nonempty sets of finite-stage Frobenius automorphisms.
2. Derive contraction of maximal ideals and injective residue maps from contraction of valuation rings.
3. Use normality and residue-map injectivity to define compatible restriction maps on Frobenius sets.
4. Apply the nested infinite-fiber argument to obtain compatible finite-stage automorphisms.
5. Glue the automorphisms and their inverses to a rational automorphism of Ω.
6. Form the union valuation ring and identify its nonunits with the union of the finite-stage maximal ideals.
7. Verify every restriction equality and transfer the finite-stage Frobenius congruences to the union.

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
