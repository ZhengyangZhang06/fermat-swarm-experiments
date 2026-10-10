<!-- theorem-id: fermat-p09/root.frobenius_approximation-a1.lift_unique_frobenius-a1.frobenius_tower_limit-a1.frobenius_valuation_union-a1.compatible_valuation_gluing-a1 -->

## Theorem `Submission.p09_af497904fe_fvu_compatible_valuation_gluing`

Let Ω = AlgebraicClosure ℚ, let F : ℕ → IntermediateField ℚ Ω be increasing and exhaustive, let V_i be a valuation subring of F_i for every i, and let ℓ ∈ ℕ. Assume V_i.LiesOverPrime ℓ for every i. Assume also that for all i ≤ j and x ∈ F_i, the image of x in F_j belongs to V_j if and only if x ∈ V_i. Then there exists a valuation subring P of Ω such that P.LiesOverPrime ℓ and, for every i and x ∈ F_i, the image of x in Ω belongs to P if and only if x ∈ V_i.

Node: `root.frobenius_approximation-a1.lift_unique_frobenius-a1.frobenius_tower_limit-a1.frobenius_valuation_union-a1.compatible_valuation_gluing-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/9

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/676

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p09_af497904fe_fvu_compatible_valuation_gluing`

```lean
∀ (F : ℕ → IntermediateField ℚ (AlgebraicClosure ℚ)) (hmono : Monotone F), (∀ x : AlgebraicClosure ℚ, ∃ i : ℕ, x ∈ F i) → ∀ (V : (i : ℕ) → ValuationSubring (F i)) (ℓ : ℕ), (∀ i : ℕ, (V i).LiesOverPrime ℓ) → (∀ (i j : ℕ) (hij : i ≤ j) (x : F i), IntermediateField.inclusion (hmono hij) x ∈ V j ↔ x ∈ V i) → ∃ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ ∧ (∀ (i : ℕ) (x : F i), (x : AlgebraicClosure ℚ) ∈ P ↔ x ∈ V i)
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

- Parent DAG node: `root.frobenius_approximation-a1.lift_unique_frobenius-a1.frobenius_tower_limit-a1.frobenius_valuation_union-a1`
- Child DAG node: `root.frobenius_approximation-a1.lift_unique_frobenius-a1.frobenius_tower_limit-a1.frobenius_valuation_union-a1.compatible_valuation_gluing-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Write Ω = AlgebraicClosure ℚ and let ι_i : F_i → Ω be the inclusion. For each i put U_i = {ι_i(x) | x ∈ V_i}, and put P = ⋃_i U_i. Each ι_i is an injective field homomorphism. For i ≤ j, exact contraction implies that the inclusion F_i → F_j sends every x ∈ V_i into V_j. Its composite with ι_j is ι_i, so U_i ⊆ U_j.
2. Both 0 and 1 belong to U_0. If z = ι_i(x) with x ∈ V_i, then −z = ι_i(−x) belongs to U_i. If z ∈ U_i and w ∈ U_j, set k = max(i,j). By step 1 both elements belong to U_k. Since U_k is the image of the subring V_k under a ring homomorphism, z+w and zw belong to U_k. Thus P is a subring of Ω.
3. For any z ∈ Ω, exhaustion gives i with z ∈ F_i. Regard z as x ∈ F_i. The valuation-ring property gives x ∈ V_i or x⁻¹ ∈ V_i. The inclusion preserves inverses, so z ∈ P or z⁻¹ ∈ P. Together with step 2 this makes P a valuation subring of Ω.
4. Fix i and x ∈ F_i. If x ∈ V_i, then ι_i(x) ∈ U_i ⊆ P. Conversely, suppose ι_i(x) ∈ P. Choose j and y ∈ V_j with ι_j(y) = ι_i(x), and put k = max(i,j). Let x_k and y_k be the images of x and y in F_k. Their images in Ω are equal, so injectivity of ι_k gives x_k = y_k. Exact contraction for j ≤ k implies y_k ∈ V_k, hence x_k ∈ V_k. Exact contraction for i ≤ k then yields x ∈ V_i. Thus ι_i(x) ∈ P if and only if x ∈ V_i.
5. For every i and x ∈ F_i, ValuationSubring.mem_nonunits_iff_or gives ι_i(x) ∈ P.nonunits if and only if ι_i(x) = 0 or ι_i(x)⁻¹ ∉ P. Injectivity identifies the zero condition with x = 0. Preservation of inverses and step 4 identify the other condition with x⁻¹ ∉ V_i. Applying the same nonunit criterion in F_i proves ι_i(x) ∈ P.nonunits if and only if x ∈ V_i.nonunits.
6. The hypothesis V_0.LiesOverPrime ℓ means (ℓ : F_0) ∈ V_0.nonunits. Step 5 sends this to (ℓ : Ω) ∈ P.nonunits because ι_0 preserves natural-number casts. By definition this is P.LiesOverPrime ℓ. This assertion and the equivalence in step 4 are precisely the required conjunction.

## Key steps

1. Form the increasing images of the compatible valuation rings.
2. Show their union is a subring and satisfies the valuation dichotomy by exhaustion.
3. Use a common larger stage and injectivity to prove exact restriction.
4. Transfer the nonunit criterion through the inclusions.
5. Use the prime-below hypothesis at stage zero.

## Reference use

### local-project

Queries:
- `IsFrobeniusAt|LiesOverPrime|mem_nonunits_iff_or|decompositionSubgroup|residueFieldAut`
- `nonunits_comap|comap_nonunits|mem_nonunits.*comap|exists.*ValuationSubring|iUnion|directed|residue_surjective|residue.*smul|smul.*residue|residue_eq_zero_iff`
- `IsFrobeniusAt.*(iUnion|iSup|union)|(?:iUnion|iSup|union).*IsFrobeniusAt|nonunits_comap|comap_nonunits`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/project/Definitions/Def_EllipticCurve_FrobeniusTrace.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/project/Definitions/Def_FLTPrelim_Ramification.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/Valuation/ValuationSubring.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/Valuation/RamificationGroup.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/LocalRing/ResidueField/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/fvu-decomposition-rnthom8q/final-report.json`

The snapshot pins project 20574e45daf714e745af8e649c7b61b21eed5644 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. LiesOverPrime is nonunit membership; IsFrobeniusAt is decomposition-subgroup membership together with the residue power equation. The inspected nonunit criterion, maximal-ideal identification, residue surjectivity, and residue_smul support the proofs below. The final targeted search found no matching Frobenius-union or nonunit-comap lemma. Both exact child types elaborated after import Submission at frozen proof-base commit 97f32c2abc9205b480ae0c2cb521b382a16c3df0; inclusion and residue-action instance checks passed. Type and cited-library axiom checks found only propext, Classical.choice, and Quot.sound. The diagnostic report records clean pinned dependencies, authorized header omissions, their reversibility, and all eight target-absence checks. It separately records concurrent advancement of the working branch. These are interface diagnostics, not comparator acceptance.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/727

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
