<!-- theorem-id: fermat-p08/root.common_kernel-a1.uniform_stabilizer-a1 -->

## Theorem `Submission.p08_7d1ff633a4_ck_uniform_stabilizer`

Let Ω = AlgebraicClosure ℚ, let k be a field, let G be a group, and let r : G → Aut_ℚ(Ω) be a group homomorphism. Let M be a finite-dimensional k-representation of G. Assume that for every m ∈ M there is an intermediate field F of Ω/ℚ, finite-dimensional over ℚ, such that M.ρ(g)m = m whenever r(g) fixes F pointwise. Then there is one intermediate field F, finite-dimensional over ℚ, such that for every g ∈ G with r(g) fixing F pointwise, M.ρ(g)m = m for every m ∈ M.

Node: `root.common_kernel-a1.uniform_stabilizer-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/8

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/348

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p08_7d1ff633a4_ck_uniform_stabilizer`

```lean
∀ {k G : Type} [Field k] [Group G] (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (M : Rep.{0} k G) [FiniteDimensional k M], (∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧ ∀ g : G, r g ∈ F.fixingSubgroup → M.ρ g m = m) → ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧ ∀ g : G, r g ∈ F.fixingSubgroup → ∀ m : M, M.ρ g m = m
```

### Frozen project context

`Fermat/Thm_groupCohomology_bijective_theta_dualTwist_of_res_of_isOpen.lean` at `9db4b2bea94e42612c675170cfe30ec626166658` supplies the original imports, definitions and root contract. Child hypotheses are stated above; prerequisite declarations are linked in their issues.

```lean
/-
Copyright 2026 Anthropic, PBC. Licensed under Apache-2.0; see LICENSE.
Source: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_groupCohomology_bijective_theta_dualTwist_of_res_of_isOpen.lean
Modified: replaced the proof with sorry and removed P2M proof imports.
Requires the upstream Definitions modules and their dependencies.
-/

import Mathlib
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_ContinuousH2Map
import Definitions.Def_GroupCohomology_ContinuousH1
import Definitions.Def_GroupCohomology_CupProduct
import Definitions.Def_GroupCohomology_ContinuousDuality
import Definitions.Def_GroupCohomology_Selmer
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
attribute [-instance] groupCohomology.normal_comap_fixingSubgroup groupCohomology.finiteIndex_comap_fixingSubgroup

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory Module groupCohomology ExtCitation
theorem groupCohomology.bijective_theta_dualTwist_of_res_of_isOpen
    {p : ℕ} [Fact p.Prime] (q : Nat.Primes)
    (S : Subgroup (primeLocalGaloisGroup q)) (U : Subgroup S) [U.FiniteIndex] (hUp : IsUnit ((U.index : ℕ) : ZMod p))
    (hU : ∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧
      F₀.fixingSubgroup.comap ((primeLocalToGlobal q).comp S.subtype) ≤ U)
    (hTU : FiniteDimensional (ZMod p) (continuousH2 (((primeLocalToGlobal q).comp S.subtype).comp U.subtype) (Rep.res U.subtype (Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))))) ∧
      finrank (ZMod p) (continuousH2 (((primeLocalToGlobal q).comp S.subtype).comp U.subtype) (Rep.res U.subtype (Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))))) = 1)
    (M : Rep.{0} (ZMod p) S) [FiniteDimensional (ZMod p) M]
    (hsm : ∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s : S, ((primeLocalToGlobal q).comp S.subtype) s ∈ F.fixingSubgroup → M.ρ s m = m)
    (inv : continuousH2 ((primeLocalToGlobal q).comp S.subtype) (Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))) →ₗ[ZMod p] ZMod p)
    (hinv : Function.Bijective inv)
    (hres : ∀ (invU : continuousH2 (((primeLocalToGlobal q).comp S.subtype).comp U.subtype) (Rep.res U.subtype (Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))))) →ₗ[ZMod p] ZMod p),
      Function.Bijective invU →
      ∀ (θ₀ : (Rep.res U.subtype M).ρ.invariants →ₗ[ZMod p] Module.Dual (ZMod p)
          (continuousH2 (((primeLocalToGlobal q).comp S.subtype).comp U.subtype) (Rep.res U.subtype (M.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype))))),
        IsTheta0 (((primeLocalToGlobal q).comp S.subtype).comp U.subtype) (Module.Dual.eval (ZMod p) M : Rep.res U.subtype M →ₗ[ZMod p]
            Rep.res U.subtype (M.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype)) →ₗ[ZMod p]
            Rep.res U.subtype (Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))))) invU θ₀ →
      ∀ (θ₁ : continuousH1 (((primeLocalToGlobal q).comp S.subtype).comp U.subtype) (Rep.res U.subtype M) →ₗ[ZMod p] Module.Dual (ZMod p)
          (continuousH1 (((primeLocalToGlobal q).comp S.subtype).comp U.subtype) (Rep.res U.subtype (M.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype))))),
        IsTheta1 (((primeLocalToGlobal q).comp S.subtype).comp U.subtype) (Module.Dual.eval (ZMod p) M : Rep.res U.subtype M →ₗ[ZMod p]
            Rep.res U.subtype (M.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype)) →ₗ[ZMod p]
            Rep.res U.subtype (Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))))) invU θ₁ →
      ∀ (θ₂ : continuousH2 (((primeLocalToGlobal q).comp S.subtype).comp U.subtype) (Rep.res U.subtype M) →ₗ[ZMod p] Module.Dual (ZMod p)
          (Rep.res U.subtype (M.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype))).ρ.invariants),
        IsTheta2 (((primeLocalToGlobal q).comp S.subtype).comp U.subtype) (Module.Dual.eval (ZMod p) M : Rep.res U.subtype M →ₗ[ZMod p]
            Rep.res U.subtype (M.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype)) →ₗ[ZMod p]
            Rep.res U.subtype (Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))))) invU θ₂ →
      Function.Bijective θ₀ ∧ Function.Bijective θ₁ ∧ Function.Bijective θ₂)
    (θ₀ : M.ρ.invariants →ₗ[ZMod p] Module.Dual (ZMod p) (continuousH2 ((primeLocalToGlobal q).comp S.subtype) (M.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype))))
    (hθ₀ : IsTheta0 ((primeLocalToGlobal q).comp S.subtype) (Module.Dual.eval (ZMod p) M : M →ₗ[ZMod p] M.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype) →ₗ[ZMod p]
        Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))) inv θ₀)
    (θ₁ : continuousH1 ((primeLocalToGlobal q).comp S.subtype) M →ₗ[ZMod p] Module.Dual (ZMod p) (continuousH1 ((primeLocalToGlobal q).comp S.subtype) (M.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype))))
    (hθ₁ : IsTheta1 ((primeLocalToGlobal q).comp S.subtype) (Module.Dual.eval (ZMod p) M : M →ₗ[ZMod p] M.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype) →ₗ[ZMod p]
        Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))) inv θ₁)
    (θ₂ : continuousH2 ((primeLocalToGlobal q).comp S.subtype) M →ₗ[ZMod p] Module.Dual (ZMod p) (M.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype)).ρ.invariants)
    (hθ₂ : IsTheta2 ((primeLocalToGlobal q).comp S.subtype) (Module.Dual.eval (ZMod p) M : M →ₗ[ZMod p] M.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype) →ₗ[ZMod p]
        Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))) inv θ₂) :
    Function.Bijective θ₀ ∧ Function.Bijective θ₁ ∧ Function.Bijective θ₂ := by
  sorry
```

## Natural-language proof

Reviewed mathematical argument; formal verification state: `proved`.

# Parent-supplied natural-language proof

- Parent DAG node: `root.common_kernel-a1`
- Child DAG node: `root.common_kernel-a1.uniform_stabilizer-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix k, G, r, and M satisfying the hypotheses, and write Ω = AlgebraicClosure ℚ. Choose a k-basis (bᵢ) of M indexed by a finite set I. The index set is allowed to be empty.
2. For each i ∈ I, apply the pointwise hypothesis to bᵢ. Choose an intermediate field Fᵢ finite-dimensional over ℚ such that r(g) ∈ Fᵢ.fixingSubgroup implies M.ρ(g)bᵢ = bᵢ for every g ∈ G. Let F be the compositum of these finitely many fields, using ℚ inside Ω for the empty compositum. Each Fᵢ is contained in F.
3. This compositum is finite-dimensional over ℚ. Here is a direct justification of the finite-compositum fact. For finite-dimensional intermediate fields A and B, choose finite ℚ-bases (aⱼ) and (bₗ). The ℚ-span C inside Ω of the products aⱼbₗ contains 1, A, and B. Expanding products using the two bases shows that C is closed under multiplication. For any nonzero x ∈ C, multiplication by x is an injective ℚ-linear endomorphism of C, since Ω is a field. Because C is finite-dimensional, this endomorphism is surjective, so xy = 1 for some y ∈ C. Thus C is a subfield. Every subfield containing A and B contains every aⱼbₗ and their ℚ-linear combinations, so C is exactly their compositum. Induction over the finite family, beginning with ℚ, proves that F is finite-dimensional. This also follows from the pinned theorem IntermediateField.finiteDimensional_iSup_of_finite.
4. Let g ∈ G satisfy r(g) ∈ F.fixingSubgroup. Since Fᵢ ≤ F, the automorphism r(g) fixes every Fᵢ pointwise. The choice in Step 2 therefore gives M.ρ(g)bᵢ = bᵢ for every i.
5. For arbitrary m ∈ M, write m = Σᵢ cᵢbᵢ. Since M.ρ(g) is k-linear, M.ρ(g)m = Σᵢ cᵢM.ρ(g)bᵢ = Σᵢ cᵢbᵢ = m. If I is empty, this is the same empty-sum calculation and M is zero. Thus the field F satisfies both required conclusions.

## Key steps

1. Choose a finite basis of M.
2. Choose a finite-dimensional field witness for each basis vector.
3. Form their finite compositum and prove its finite dimension.
4. An automorphism fixing the compositum fixes every witness field, hence every basis vector.
5. Extend the identity action to all vectors by linearity, including the empty-basis case.

## Reference use

### local-project

Queries:
- `rg -n 'dualTwist_ρ_apply|noncomputable def cycloChar|card_rootsOfUnity_eq_self|noncomputable abbrev ofChar' project/Definitions/Def_GroupCohomology_Selmer.lean project/Definitions/Def_ExtCitation_KummerBridge.lean project/Definitions/Def_ExtCitation_AdmissibleExtension.lean project/Definitions/Def_DualSelmer_ExtConditions.lean`
- `rg -n 'lemma unique|finiteDimensional_iSup_of_finite|theorem finiteDimensional_adjoin' mathlib/Mathlib/NumberTheory/Cyclotomic/CyclotomicCharacter.lean mathlib/Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean`
- `p08_7d1ff633a4_ck_uniform_stabilizer|p08_7d1ff633a4_ck_cyclotomic_kernel|p08_7d1ff633a4_normal_refinement`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/project/Definitions/Def_GroupCohomology_Selmer.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/project/Definitions/Def_ExtCitation_KummerBridge.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/project/Definitions/Def_ExtCitation_AdmissibleExtension.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/project/Definitions/Def_DualSelmer_ExtConditions.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/mathlib/Mathlib/NumberTheory/Cyclotomic/CyclotomicCharacter.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/mathlib/Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/common-kernel-decomposition-check-20261008/Types.lean.log`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/common-kernel-decomposition-check-20261008/receipt.json`

The relative rg commands ran from the supplied snapshot root. The manifest pins project 9db4b2bea94e42612c675170cfe30ec626166658 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. Inspected sources provide finite-dimensional finite composita and adjunctions, the required roots-of-unity cardinality, modularCyclotomicCharacter.unique, and the character and twisted-dual action formulas. No reference-source match exists for either proposed identifier or p08_7d1ff633a4_normal_refinement; the latter is an existing DAG prerequisite. Both proposed identifiers are absent from all ten local active DAGs. Both exact child types elaborated after import Submission in a disposable compiler copy. The policy digest matched, Lean confirmed both omitted targets absent, and reversible header-copy hashes were recorded; original sources remain unchanged. The checked library declarations have only propext, Classical.choice, and Quot.sound among their transitive axioms. These are interface diagnostics, not comparator acceptance of child proofs.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/435

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
