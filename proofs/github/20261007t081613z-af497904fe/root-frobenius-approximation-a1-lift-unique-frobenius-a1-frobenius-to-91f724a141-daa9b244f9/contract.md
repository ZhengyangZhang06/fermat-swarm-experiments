<!-- theorem-id: fermat-p09/root.frobenius_approximation-a1.lift_unique_frobenius-a1.frobenius_tower_limit-a1.frobenius_valuation_union-a1 -->

## Theorem `Submission.p09_af497904fe_ftl_frobenius_valuation_union`

Let Ω = AlgebraicClosure ℚ and let F : ℕ → IntermediateField ℚ Ω be increasing and exhaustive. Let V_i be a valuation subring of F_i for every i and let ℓ ∈ ℕ. Assume (V_i).LiesOverPrime ℓ for every i, and that each inclusion F_i → F_j for i ≤ j contracts V_j exactly to V_i. Let τ be a rational automorphism of Ω. Assume that for every i there exists a rational automorphism g of F_i satisfying (V_i).IsFrobeniusAt g ℓ and τ(x) = g(x) in Ω for every x ∈ F_i. Then there exists a valuation subring P of Ω such that P.LiesOverPrime ℓ, P restricts exactly to V_i on every F_i, and P.IsFrobeniusAt τ ℓ.

Node: `root.frobenius_approximation-a1.lift_unique_frobenius-a1.frobenius_tower_limit-a1.frobenius_valuation_union-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/9

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/661

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/688, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/689

## Lean problem

Declaration: `Submission.p09_af497904fe_ftl_frobenius_valuation_union`

```lean
∀ (F : ℕ → IntermediateField ℚ (AlgebraicClosure ℚ)) (hmono : Monotone F), (∀ x : AlgebraicClosure ℚ, ∃ i : ℕ, x ∈ F i) → ∀ (V : (i : ℕ) → ValuationSubring (F i)) (ℓ : ℕ), (∀ i : ℕ, (V i).LiesOverPrime ℓ) → (∀ (i j : ℕ) (hij : i ≤ j) (x : F i), IntermediateField.inclusion (hmono hij) x ∈ V j ↔ x ∈ V i) → ∀ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ i : ℕ, ∃ g : F i ≃ₐ[ℚ] F i, (V i).IsFrobeniusAt g ℓ ∧ ∀ x : F i, τ (x : AlgebraicClosure ℚ) = ((g x : F i) : AlgebraicClosure ℚ)) → ∃ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ ∧ (∀ (i : ℕ) (x : F i), (x : AlgebraicClosure ℚ) ∈ P ↔ x ∈ V i) ∧ P.IsFrobeniusAt τ ℓ
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
- Child DAG node: `root.frobenius_approximation-a1.lift_unique_frobenius-a1.frobenius_tower_limit-a1.frobenius_valuation_union-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Identify each F_i with its subfield of Ω and write U_i for the image of V_i in Ω. The contraction hypothesis implies U_i ⊆ U_j whenever i ≤ j: an element of V_i maps into V_j. Define P as the subset ⋃_i U_i of Ω.
2. This subset is a subring. Zero and one belong to U_0. If x belongs to U_i, then −x also belongs to U_i. If x ∈ U_i and y ∈ U_j, pass to k = max(i,j); both belong to U_k, so their sum and product belong to U_k. For any x ∈ Ω, exhaustion places x in a field F_i. Its valuation subring V_i contains x or x⁻¹, and consequently P contains x or x⁻¹. Therefore this subring is a valuation subring of Ω.
3. P restricts exactly to V_i. The forward inclusion from V_i to P follows from its definition. Conversely, let x ∈ F_i have image in P. This image belongs to U_j for some j. In F_k with k = max(i,j), the images of the two representatives are equal because their images in Ω are equal and the inclusion F_k → Ω is injective. The representative from V_j maps into V_k. Hence the image of x in F_k belongs to V_k, and contraction from k to i gives x ∈ V_i.
4. Nonunits also contract exactly: for every x ∈ F_i, its image in Ω belongs to P.nonunits if and only if x ∈ (V_i).nonunits. Apply ValuationSubring.mem_nonunits_iff_or on both fields. Inclusion preserves inverses and detects zero, while step 3 identifies membership of x⁻¹ in the two valuation rings. Thus both criteria are identical. Applying this equivalence to (ℓ : F_0), which is a nonunit by hypothesis and maps to (ℓ : Ω), proves P.LiesOverPrime ℓ.
5. For each i select a witness g_i from the stagewise Frobenius hypothesis. It and its inverse preserve V_i because g_i belongs to its decomposition subgroup. The agreement with τ implies agreement of the inverses as well: for x ∈ F_i, applying the agreement to g_i⁻¹(x) gives τ(g_i⁻¹(x)) = x in Ω, and application of τ⁻¹ gives τ⁻¹(x) = g_i⁻¹(x). Therefore τ and τ⁻¹ both preserve every U_i, and hence preserve P. It follows that τ maps P onto itself and belongs to P.decompositionSubgroup ℚ.
6. Let z ∈ P. Choose i and x ∈ V_i whose image in Ω is z. The Frobenius equation for g_i in the residue field of V_i says [g_i(x)] = [x]^ℓ. Since the residue map has kernel the maximal ideal, and its ambient image is (V_i).nonunits, this is equivalent to g_i(x) − x^ℓ ∈ (V_i).nonunits. Step 4 sends this difference into P.nonunits. Agreement with τ and preservation of powers by the field inclusion identify its image with τ(z) − z^ℓ. Thus τ(z) − z^ℓ belongs to P.nonunits.
7. The residue map P → IsLocalRing.ResidueField P is surjective. For a residue class represented by z ∈ P, step 5 identifies the action induced by τ with the residue of τ(z), and step 6 makes this residue equal to the ℓ-th power of the residue of z. Hence the action is the ℓ-power map on every residue class. Together with step 5 this is exactly P.IsFrobeniusAt τ ℓ. Steps 3 and 4 give the other two required conjuncts.

## Key steps

1. Form the increasing union of the valuation rings inside Ω.
2. Verify the subring and valuation properties in common stages.
3. Prove exact restriction to each stage.
4. Contract nonunits by the inverse criterion and obtain LiesOverPrime.
5. Use local Frobenius automorphisms to prove that τ and τ⁻¹ preserve the union.
6. Transfer local Frobenius differences into the union's nonunits.
7. Use residue representatives to establish the global Frobenius action.

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

The exact contract must pass the machine comparator and an independent reviewer's comparator rerun, without changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/746

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
