# Parent-supplied natural-language proof

- Parent DAG node: `root`
- Child DAG node: `root.linear_descent-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Suppose Θ(x) = 0. For every y′ ∈ Y′, the first compatibility gives Θ′(R_Xx)(y′) = Θ(x)(C_Yy′) = 0. Extensionality of linear functionals gives Θ′(R_Xx) = 0 = Θ′(0). Injectivity of Θ′ therefore gives R_Xx = 0.
2. Apply C_X. The composite identity yields n·x = 0. Multiplying by n⁻¹ gives x = 0 because n ≠ 0. If Θ(x₁) = Θ(x₂), linearity gives Θ(x₁−x₂) = 0, so the preceding argument implies x₁ = x₂. Thus Θ is injective.
3. Let λ ∈ Y* be arbitrary. The composite λ ∘ C_Y is a linear functional on Y′. By surjectivity of Θ′ choose x′ ∈ X′ with Θ′(x′) = λ ∘ C_Y. Define x = n⁻¹·C_Xx′.
4. For every y ∈ Y, linearity, the second compatibility, and the composite identity for Y give Θ(x)(y) = n⁻¹Θ(C_Xx′)(y) = n⁻¹Θ′(x′)(R_Yy) = n⁻¹λ(C_Y(R_Yy)) = n⁻¹λ(n·y) = λ(y). The final equality uses linearity of λ and n⁻¹n = 1. Extensionality gives Θ(x) = λ.
5. Since λ was arbitrary, Θ is surjective. Combined with Step 2, this proves bijectivity without any dimension assumption.

## Key steps

1. Use the first compatibility and injectivity of Θ′ to show ker Θ maps into ker R_X.
2. Cancel n in C_XR_X = n id to prove injectivity.
3. Lift λ ∘ C_Y through Θ′.
4. Normalize the transferred lift by n⁻¹.
5. Use the second compatibility and C_YR_Y = n id to prove surjectivity.

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
