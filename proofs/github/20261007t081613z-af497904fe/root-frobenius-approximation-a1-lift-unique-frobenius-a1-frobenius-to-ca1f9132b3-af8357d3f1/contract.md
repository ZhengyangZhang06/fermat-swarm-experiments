<!-- theorem-id: fermat-p09/root.frobenius_approximation-a1.lift_unique_frobenius-a1.frobenius_tower_limit-a1.compatible_automorphisms_glue-a1 -->

## Theorem `Submission.p09_af497904fe_ftl_compatible_automorphisms_glue`

Let Ω = AlgebraicClosure ℚ and let F : ℕ → IntermediateField ℚ Ω be increasing, with every element of Ω belonging to some F_i. For i ≤ j write ι_ij : F_i → F_j for inclusion. Suppose g_i is a rational automorphism of F_i for every i and ι_ij(g_i(x)) = g_j(ι_ij(x)) for every i ≤ j and x ∈ F_i. Then there exists a rational automorphism τ of Ω whose restriction to each F_i agrees with g_i under the inclusions into Ω.

Node: `root.frobenius_approximation-a1.lift_unique_frobenius-a1.frobenius_tower_limit-a1.compatible_automorphisms_glue-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/9

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/661

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p09_af497904fe_ftl_compatible_automorphisms_glue`

```lean
∀ (F : ℕ → IntermediateField ℚ (AlgebraicClosure ℚ)) (hmono : Monotone F), (∀ x : AlgebraicClosure ℚ, ∃ i : ℕ, x ∈ F i) → ∀ g : (i : ℕ) → F i ≃ₐ[ℚ] F i, (∀ (i j : ℕ) (hij : i ≤ j) (x : F i), IntermediateField.inclusion (hmono hij) (g i x) = g j (IntermediateField.inclusion (hmono hij) x)) → ∃ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ (i : ℕ) (x : F i), τ (x : AlgebraicClosure ℚ) = ((g i x : F i) : AlgebraicClosure ℚ)
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

- Parent DAG node: `root.frobenius_approximation-a1.lift_unique_frobenius-a1.frobenius_tower_limit-a1`
- Child DAG node: `root.frobenius_approximation-a1.lift_unique_frobenius-a1.frobenius_tower_limit-a1.compatible_automorphisms_glue-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Regard all F_i as subfields of Ω. For x ∈ Ω choose a stage i containing x and set t(x) equal to the image in Ω of g_i(x). To check independence, suppose x also belongs to F_j and put k = max(i,j). Compatibility identifies both proposed values with the image of g_k(x). Thus t is well-defined and agrees with every g_i on its stage.
2. The inverse automorphisms are also compatible. Fix i ≤ j and x ∈ F_i. Apply g_j to ι_ij(g_i⁻¹(x)). Compatibility for g_i and g_j gives g_j(ι_ij(g_i⁻¹(x))) = ι_ij(x). Applying g_j⁻¹ yields ι_ij(g_i⁻¹(x)) = g_j⁻¹(ι_ij(x)).
3. Define u(x) using g_i⁻¹ at any stage containing x. Step 2 and the same common-stage argument as in step 1 make this independent of the stage. If x ∈ F_i, then g_i(x) and g_i⁻¹(x) also belong to F_i. Evaluating both composites in that stage gives t(u(x)) = g_i(g_i⁻¹(x)) = x and u(t(x)) = g_i⁻¹(g_i(x)) = x. Hence u is a two-sided inverse of t.
4. Given x,y ∈ Ω, choose a common stage containing both. Its subfield structure also contains x+y and xy. Evaluating t at that stage and using the algebra-automorphism laws for g_i proves t(x+y) = t(x)+t(y) and t(xy) = t(x)t(y). Stage 0 gives t(0) = 0 and t(1) = 1. Every rational scalar belongs to F_0 and is fixed by g_0, so t fixes the image of ℚ.
5. The bijection t with inverse u, together with the identities in step 4, defines a rational algebra automorphism τ of Ω. Its agreement with every g_i is exactly the agreement established in step 1, proving the required conclusion.

## Key steps

1. Define the forward map stagewise and prove independence using a common maximum stage.
2. Derive compatibility of the inverse automorphisms.
3. Glue the inverses and verify both inverse identities.
4. Check algebra operations and rational scalars in a common stage.
5. Package the resulting bijective rational algebra map as τ.

## Reference use

### local-project

Queries:
- `IsFrobeniusAt|mem_nonunits_iff_or|exists.*compatible|inverse.*limit|restrictNormal|LiesOverPrime`
- `def IsFrobeniusAt|def LiesOverPrime|def decompositionSubgroup|theorem.*IsFrobeniusAt`
- `glue|iSup|directLimit|exists.*equiv`
- `maximalIdeal|nonunits|residue.*smul|smul.*residue`
- `p09_af497904fe_ftl_(normal_frobenius_restriction|compatible_automorphisms_glue|frobenius_valuation_union)`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/project/Definitions/Def_EllipticCurve_FrobeniusTrace.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/project/Definitions/Def_FLTPrelim_Ramification.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/Valuation/ValuationSubring.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/Valuation/RamificationGroup.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/RingTheory/LocalRing/ResidueField/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/FieldTheory/Normal/Defs.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/local-references/eac3cc806adf4596/mathlib/Mathlib/CategoryTheory/CofilteredSystem.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/Submission.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p09/.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/nodes/root-finite-inverse-limit-a1/integration-lean-audit-v1.json`
- `/runtime/review-evidence/5190b66052c64f30b33294a3056dcb3f/evidence.json`
- `/runtime/operator-header-policy-v1/policy.json`
- `/tmp/p09_tower_decomposition_eui_c1e8/TypesAfterSubmission.lean`
- `/tmp/p09_tower_decomposition_eui_c1e8/record.json`

The snapshot pins project 20574e45daf714e745af8e649c7b61b21eed5644 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. The inspected definitions identify LiesOverPrime with ambient nonunit membership and IsFrobeniusAt with decomposition-group membership plus the residue power action. ValuationSubring.mem_nonunits_iff_or and coe_mem_nonunits_iff justify nonunit contraction; residue_eq_zero_iff and residue_smul justify passing between residue equations and differences in nonunits. Normal/Defs supplies normal restriction and its commuting equation. The IntermediateField search found directed-union infrastructure but no directly applicable automorphism-gluing theorem. The inherited p09_af497904fe_finite_inverse_limit already has exact-comparator and permitted-axiom evidence, so no duplicate node is proposed. Proposed names have no matches in the inspected DAG or Submission. All three exact types compiled after literal import Submission using a disposable copy of frozen base 3915a640f981289a567a646ed42a4a5f880b9d24; their axiom reports contain only propext, Classical.choice and Quot.sound. Policy digest 96fc18eb6b8cbdad1beec37ca318ab2cf08ac1dda8ebf7cbfe1d6d51abf32f96 was checked, only original lines 10 and 11 were omitted, and Lean verified all eight omitted targets absent. Original sources remained unchanged. These are interface diagnostics, not proof acceptance.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: Pending

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
