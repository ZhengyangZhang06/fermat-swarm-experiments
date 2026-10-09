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
