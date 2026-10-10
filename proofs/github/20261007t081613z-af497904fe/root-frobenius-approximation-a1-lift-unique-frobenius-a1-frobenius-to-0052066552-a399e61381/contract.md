<!-- theorem-id: fermat-p09/root.frobenius_approximation-a1.lift_unique_frobenius-a1.frobenius_tower_limit-a1.frobenius_valuation_union-a1.frobenius_from_exhaustive_restrictions-a1 -->

## Theorem `Submission.p09_af497904fe_fvu_frobenius_from_exhaustive_restrictions`

Let Ω = AlgebraicClosure ℚ and let F : ℕ → IntermediateField ℚ Ω be exhaustive: every element of Ω lies in some F_i. Let V_i be a valuation subring of F_i for every i and let P be a valuation subring of Ω. Assume that for every i and x ∈ F_i, the image of x in Ω belongs to P if and only if x ∈ V_i. Let ℓ ∈ ℕ and τ ∈ Autℚ(Ω). Suppose that for every i there exists g ∈ Autℚ(F_i) such that V_i.IsFrobeniusAt g ℓ and τ agrees with g after embedding F_i into Ω. Then P.IsFrobeniusAt τ ℓ.

Node: `root.frobenius_approximation-a1.lift_unique_frobenius-a1.frobenius_tower_limit-a1.frobenius_valuation_union-a1.frobenius_from_exhaustive_restrictions-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/9

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/676

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p09_af497904fe_fvu_frobenius_from_exhaustive_restrictions`

```lean
∀ (F : ℕ → IntermediateField ℚ (AlgebraicClosure ℚ)), (∀ x : AlgebraicClosure ℚ, ∃ i : ℕ, x ∈ F i) → ∀ (V : (i : ℕ) → ValuationSubring (F i)) (P : ValuationSubring (AlgebraicClosure ℚ)), (∀ (i : ℕ) (x : F i), (x : AlgebraicClosure ℚ) ∈ P ↔ x ∈ V i) → ∀ (ℓ : ℕ) (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), (∀ i : ℕ, ∃ g : F i ≃ₐ[ℚ] F i, (V i).IsFrobeniusAt g ℓ ∧ ∀ x : F i, τ (x : AlgebraicClosure ℚ) = ((g x : F i) : AlgebraicClosure ℚ)) → P.IsFrobeniusAt τ ℓ
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
- Child DAG node: `root.frobenius_approximation-a1.lift_unique_frobenius-a1.frobenius_tower_limit-a1.frobenius_valuation_union-a1.frobenius_from_exhaustive_restrictions-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Write Ω = AlgebraicClosure ℚ and let ι_i : F_i → Ω be the inclusion. For each i choose g_i from the hypothesis. By the definition of IsFrobeniusAt, g_i belongs to the decomposition subgroup of V_i, so g_i maps V_i onto V_i. Consequently both g_i and g_i⁻¹ send elements of V_i into V_i.
2. For x ∈ F_i, agreement applied to g_i⁻¹(x) gives τ(ι_i(g_i⁻¹(x))) = ι_i(x). Applying τ⁻¹ proves τ⁻¹(ι_i(x)) = ι_i(g_i⁻¹(x)). Thus the given agreement also holds for the inverse automorphisms.
3. If z ∈ P, exhaustion gives i and x ∈ F_i with ι_i(x) = z. Exact restriction gives x ∈ V_i. Step 1 and agreement imply τ(z) ∈ P. Steps 1 and 2 imply τ⁻¹(z) ∈ P as well. The first inclusion gives τ(P) ⊆ P; for z ∈ P the second inclusion gives z = τ(τ⁻¹(z)) ∈ τ(P). Hence τ(P) = P, which means τ belongs to P.decompositionSubgroup ℚ. Denote this membership proof by hτ.
4. Exact restriction also identifies nonunits. Indeed, for x ∈ F_i, the criterion ValuationSubring.mem_nonunits_iff_or says that ι_i(x) ∈ P.nonunits if and only if ι_i(x) = 0 or ι_i(x)⁻¹ ∉ P. Injectivity and inverse preservation of ι_i, followed by exact restriction for x⁻¹, turn this into x = 0 or x⁻¹ ∉ V_i. Applying the criterion in V_i shows that this is equivalent to x ∈ V_i.nonunits.
5. Fix i and x ∈ V_i, with x viewed as an element of F_i when evaluating g_i. Let q_i be the residue homomorphism V_i → IsLocalRing.ResidueField V_i. The decomposition-group action on V_i is the restriction of g_i, and IsLocalRing.ResidueField.residue_smul identifies its residue action with q_i applied after this restriction. Thus the Frobenius hypothesis gives q_i(g_i(x)) = q_i(x)^ℓ = q_i(x^ℓ). Both g_i(x) and x^ℓ belong to V_i. Their difference d = g_i(x) − x^ℓ lies in V_i and satisfies q_i(d) = 0. The kernel of q_i is the maximal ideal, and ValuationSubring.coe_mem_nonunits_iff identifies its ambient image with V_i.nonunits. Hence d ∈ V_i.nonunits as an element of F_i.
6. For z ∈ P choose i and x ∈ V_i with ι_i(x) = z, using exhaustion and exact restriction as in step 3. Apply step 5 and then step 4 to obtain ι_i(g_i(x) − x^ℓ) ∈ P.nonunits. Since ι_i preserves subtraction and powers and τ(ι_i(x)) = ι_i(g_i(x)), this element equals τ(z) − z^ℓ. Consequently τ(z) − z^ℓ ∈ P.nonunits for every z ∈ P.
7. Let q_P : P → IsLocalRing.ResidueField P be the residue map. It is surjective, so any residue class a can be written q_P(z) for z ∈ P. By step 3, τ(z) defines an element of P. Step 6 and ValuationSubring.coe_mem_nonunits_iff put τ(z) − z^ℓ in the maximal ideal of P. Applying q_P gives q_P(τ(z)) = q_P(z)^ℓ. Compatibility of the residue map with the decomposition-group action identifies the left side with (τ,hτ) acting on a. Therefore (τ,hτ) acts by a ↦ a^ℓ on every residue class. Together with hτ this is exactly P.IsFrobeniusAt τ ℓ.

## Key steps

1. Choose the stage Frobenius automorphisms and establish inverse agreement.
2. Use exhaustion and exact restriction to show τ stabilizes P.
3. Identify nonunits under each field inclusion.
4. Translate each stage residue equation into a nonunit difference.
5. Transfer that difference to P and descend using residue-map surjectivity.

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

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/735

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
