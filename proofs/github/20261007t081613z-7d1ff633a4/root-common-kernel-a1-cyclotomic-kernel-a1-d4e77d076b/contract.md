<!-- theorem-id: fermat-p08/root.common_kernel-a1.cyclotomic_kernel-a1 -->

## Theorem `Submission.p08_7d1ff633a4_ck_cyclotomic_kernel`

Let p be prime and Ω = AlgebraicClosure ℚ. There exists an intermediate field F of Ω/ℚ, finite-dimensional over ℚ, such that ExtCitation.cycloChar p σ = 1 in (ZMod p)ˣ for every rational algebra automorphism σ of Ω that fixes F pointwise.

Node: `root.common_kernel-a1.cyclotomic_kernel-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/8

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/348

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p08_7d1ff633a4_ck_cyclotomic_kernel`

```lean
∀ {p : ℕ} [Fact p.Prime], ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧ ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ F.fixingSubgroup → ExtCitation.cycloChar p σ = 1
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
- Child DAG node: `root.common_kernel-a1.cyclotomic_kernel-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix a prime p and write Ω = AlgebraicClosure ℚ. Then p ≥ 2 and p ≠ 0. Let R = {ζ ∈ Ω : ζ^p = 1}. This is the root set in Ω of X^p − 1. The polynomial is monic of degree p, hence nonzero, so R is finite.
2. Let F = ℚ(R), the intermediate field generated by R. To prove finite dimension, enumerate R and adjoin its elements successively. Over any field L arising at an intermediate stage, the next root ζ satisfies the monic equation X^p − 1. Thus L[ζ] is spanned over L by 1, ζ, …, ζ^(p−1). For nonzero x ∈ L[ζ], multiplication by x is an injective endomorphism of this finite-dimensional L-vector space, hence surjective. In particular x has an inverse in L[ζ]. Consequently L[ζ] is already L(ζ), and L(ζ)/L is finite-dimensional. The tower formula applied to the finitely many adjunctions proves that F/ℚ is finite-dimensional. Every element of R belongs to F by construction.
3. The polynomial X^p − 1 splits over the algebraically closed field Ω. For any root ζ, the equation ζ^p = 1 gives ζ ≠ 0. Since Ω has characteristic zero, p is nonzero in Ω. Therefore the derivative at ζ, namely pζ^(p−1), is nonzero. A repeated root would produce a factor (X − ζ)^2, whose product-rule derivative vanishes at ζ, a contradiction. Thus all roots are simple. A split polynomial of degree p with only simple roots has exactly p distinct roots.
4. Each ζ ∈ R is a unit with inverse ζ^(p−1), and this unit has p-th power 1. Conversely, the underlying field element of a unit with p-th power 1 lies in R. These assignments are inverse, since a unit is determined by its underlying field element. Hence Nat.card (rootsOfUnity p Ω) = p. This is precisely the cardinality equality provided by the pinned theorem ExtCitation.card_rootsOfUnity_eq_self.
5. Let σ be a rational algebra automorphism of Ω with σ ∈ F.fixingSubgroup. For every t ∈ rootsOfUnity p Ω, its underlying field element belongs to R and therefore to F. Thus σ fixes that field element.
6. Set c = 1 in ZMod p. Because p ≥ 2, c.val = 1. Step 5 gives σ(t) = t = t^(c.val) for every p-th root of unity, interpreting the equality in Ω. Apply modularCyclotomicCharacter.unique to the ring automorphism underlying σ, using the cardinality equality from Step 4. It follows that 1 equals the underlying residue of modularCyclotomicCharacter evaluated at σ. By the pinned definition of ExtCitation.cycloChar, this is the underlying residue of ExtCitation.cycloChar p σ. The coercion from units to ZMod p is injective, so ExtCitation.cycloChar p σ = 1 as units. Together with Step 2, this proves the required existence statement.

## Key steps

1. Take the finite root set of X^p − 1 in the algebraic closure.
2. Adjoin these roots and prove finite dimension by successive finite adjunctions.
3. Use splitting and the nonvanishing derivative to obtain exactly p distinct roots.
4. Identify those roots with rootsOfUnity p Ω to establish the character's cardinality hypothesis.
5. An automorphism fixing the generated field fixes every p-th root of unity.
6. Apply modularCyclotomicCharacter.unique with residue 1 and lift equality to units.

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

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/416

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
