# Parent-supplied natural-language proof

- Parent DAG node: `root`
- Child DAG node: `root.rank_one_transfer-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Put f = ℓ ∘ C. By surjectivity of ℓ choose z ∈ V with ℓ(z) = 1. Define v = n⁻¹·R(z). Linearity and the composite identity give f(v) = n⁻¹ℓ(C(Rz)) = n⁻¹ℓ(n·z) = n⁻¹n = 1.
2. Therefore v ≠ 0, since a linear map sends zero to zero and 1 ≠ 0 in a field. As W is finite-dimensional of dimension one, choose a basis consisting of one vector e. Write v = c·e. Nonvanishing of v implies c ≠ 0. Every w ∈ W can be written d·e and hence equals (d/c)·v.
3. This scalar expression is unique. If a·v = b·v, then (a−b)·v = 0. If a−b were nonzero, multiplying by its inverse would give v = 0. Thus a = b. Moreover, linearity and f(v) = 1 give f(a·v) = a for every a ∈ k.
4. For every a ∈ k, the vector a·v maps to a, proving surjectivity. If f(w₁) = f(w₂), write w₁ = a·v and w₂ = b·v using Step 2. Step 3 gives f(w₁) = a and f(w₂) = b, so a = b and w₁ = w₂. Thus f is injective as well, proving the required bijectivity.

## Key steps

1. Choose z with ℓ(z) = 1 and normalize R(z) by n⁻¹.
2. Use the composite identity to obtain a vector v with transferred functional value one.
3. Use dimension one to express every vector uniquely as a multiple of v.
4. Read off injectivity and surjectivity from that scalar coordinate.

## Reference use

### local-project

Queries:
- `rg -n 'normal_comap_fixingSubgroup|finiteIndex_comap_fixingSubgroup|corestriction|projection_formula|IsTheta.*exists|exists.*IsTheta|p08_7d1ff633a4_' project/Definitions mathlib/Mathlib`
- `rg -n 'normalClosure|finiteDimensional|instModule|of_coe' mathlib/Mathlib/FieldTheory/Normal/Closure.lean mathlib/Mathlib/Algebra/Category/ModuleCat/Basic.lean`
- `rg -n 'normal_comap_fixingSubgroup|finiteIndex_comap_fixingSubgroup|IsTheta.*exists|exists.*IsTheta|p08_7d1ff633a4_' project/Definitions mathlib/Mathlib`
- `sed -n '195,240p' mathlib/Mathlib/NumberTheory/Cyclotomic/CyclotomicCharacter.lean`
- `sed -n '960,995p' mathlib/Mathlib/RepresentationTheory/Homological/GroupCohomology/LowDegree.lean`
- `git rev-parse HEAD`
- `git status --porcelain`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lean -j1 Combined.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/project/Definitions/Def_GroupCohomology_ContinuousH1.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/project/Definitions/Def_GroupCohomology_ContinuousH2.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/project/Definitions/Def_GroupCohomology_ContinuousH2Map.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/project/Definitions/Def_GroupCohomology_ContinuousDuality.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/project/Definitions/Def_GroupCohomology_CupProduct.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/project/Definitions/Def_GroupCohomology_Selmer.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/project/Definitions/Def_DualSelmer_ExtConditions.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/project/Definitions/Def_ExtCitation_KummerBridge.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/project/Definitions/Def_ExtCitation_AdmissibleExtension.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/mathlib/Mathlib/RepresentationTheory/Rep/Res.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/mathlib/Mathlib/RepresentationTheory/Homological/GroupCohomology/LowDegree.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/mathlib/Mathlib/NumberTheory/Cyclotomic/CyclotomicCharacter.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/mathlib/Mathlib/FieldTheory/Normal/Closure.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/github-theorem-prover/runs/20261007T081613Z-7d1ff633a4/local-references/f1203ade877a7c36/mathlib/Mathlib/Algebra/Category/ModuleCat/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/decomposition-type-check-20261008/Combined.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/decomposition-type-check-20261008/Combined.log`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/decomposition-type-check-20261008/combined-result.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p08/.humanize/decomposition-type-check-20261008/provenance.json`

Project revision 9db4b2bea94e42612c675170cfe30ec626166658 and mathlib revision db584cd6d46c92f209a44c0f1c829460d327499d match the manifest and have clean trees; installed dependencies also match clean pins. ContinuousH1 is an image of level cocycles in ordinary H1; continuousH2 is the quotient by boundaries from level one-cochains. Inspected the precise theta predicates, cup formula, restriction carriers, twisted-dual action, cyclotomic specification and uniqueness, normal-closure instances, and ModuleCat.of. The targeted search found no existing proposed names, fixing-subgroup instances, or theta-existence theorem. Broad corestriction matches concern ordinary homology or unrelated range restrictions, not the required continuous transfer/theta package. Fresh literal-import checks in the existing matching policy-derived Submission context passed for all five unchanged expressions, all 24 indexed additive/module instance equalities, and the global/restricted evaluation pairing coercions. Inspected type and library transitive axioms are confined to propext, Classical.choice, and Quot.sound. A separate fresh context rebuild timed out. These diagnostics do not accept any theorem proof, and no upstream target solution was imported.
