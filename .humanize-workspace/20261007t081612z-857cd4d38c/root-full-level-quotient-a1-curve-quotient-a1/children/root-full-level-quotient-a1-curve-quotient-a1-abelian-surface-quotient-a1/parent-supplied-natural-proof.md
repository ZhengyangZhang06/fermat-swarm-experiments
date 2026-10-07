# Parent-supplied natural-language proof

- Parent DAG node: `root.full_level_quotient-a1.curve_quotient-a1`
- Child DAG node: `root.full_level_quotient-a1.curve_quotient-a1.abelian_surface_quotient-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Let h be the assumed bundle and let T = S/J, β = Spec(Ideal.Quotient.mk J), A_T = A ×_{Spec S} Spec T, g = pullback.fst f β, and p = pullback.snd f β. The quotient map is surjective. Consequently β is a closed immersion by AlgebraicGeometry.IsClosedImmersion.spec_of_quotient_mk in Mathlib/AlgebraicGeometry/Morphisms/ClosedImmersion.lean:115, at the pinned mathlib revision db584cd6d46c92f209a44c0f1c829460d327499d. Its underlying map is therefore injective.
2. The morphism p is the base change of f. The fields h.smooth and h.proper, together with AlgebraicGeometry.smooth_isStableUnderBaseChange in Morphisms/Smooth.lean:117 and AlgebraicGeometry.IsProper.isStableUnderBaseChange in Morphisms/Proper.lean:72 at that same revision, imply Smooth p and IsProper p.
3. The morphism g is the base change of the closed immersion β. By IsClosedImmersion.isStableUnderBaseChange in Morphisms/ClosedImmersion.lean:382, it is a closed immersion, hence a topological embedding. The pinned theorem AlgebraicGeometry.Scheme.Pullback.range_fst in Mathlib/AlgebraicGeometry/PullbackCarrier.lean:328 gives range(g) = f⁻¹(range(β)).
4. Fix t ∈ Spec T and put s = β(t). The equation g ≫ f = p ≫ β shows that g restricts to a map F_t : p⁻¹({t}) → f⁻¹({s}). This map is injective because g is. For x in f⁻¹({s}), f(x) = β(t) belongs to range(β), so step 3 supplies y ∈ A_T with g(y) = x. Commutativity gives β(p(y)) = f(g(y)) = β(t); injectivity of β gives p(y) = t. Thus y is in the required fibre and F_t is surjective.
5. Restricting a topological embedding to subspaces yields an embedding into the target subspace. Hence the bijection F_t is a homeomorphism: its inducing property identifies the source topology with the topology transported from the target, making the inverse continuous. The old fibre is nonempty and connected by h.connectedFibres s. Its homeomorphic new fibre is likewise nonempty and connected. Interpreted as a subset of A_T, this is precisely IsConnected (p.base ⁻¹' {t}).
6. A homeomorphism sends irreducible closed subsets bijectively to irreducible closed subsets, preserves inclusion in both directions, and therefore preserves the lengths of all strict chains. Thus it preserves topological Krull dimension; the pinned formal result is IsHomeomorph.topologicalKrullDim_eq in Mathlib/Topology/KrullDimension.lean:53. Applied to F_t and the assumed dimension equation for s, it gives topologicalKrullDim ↥(p.base ⁻¹' {t}) = 2. Since t was arbitrary, both the connectedness and dimension conclusions hold for every fibre.
7. Extract G : RelativeGroupLaw S f from h.hasGroupLaw. Apply the sibling theorem group_law_pullback to S, T, Ideal.Quotient.mk J, A, f, and G. Its witness H : RelativeGroupLaw T p supplies Nonempty (RelativeGroupLaw T p).
8. Assemble Smooth p, IsProper p, the connected-fibre assertions from step 5, and the group-law witness from step 7 into AbelianSchemePropertyBundle T p. Pair this bundle with the dimension assertions from step 6. This proves the exact conclusion, including when Spec T is empty, in which case the universally quantified fibre assertions are vacuous.

## Key steps

1. Recognize the quotient spectrum map and its pullback as closed immersions.
2. Transfer smoothness and properness by base change.
3. Use the pullback image formula and injectivity to identify each entire topological fibre.
4. Transfer nonempty connectedness and topological Krull dimension through the resulting homeomorphism.
5. Obtain a group-law witness from group_law_pullback and assemble the bundle.

## Reference use

### local-project

Queries:
- `structure FakeEllipticCurve|structure RelativeGroupLaw|def tangentZero|def IsTangentVector|structure AbelianSchemePropertyBundle`
- `baseChangePointToBase|baseChangePointOfBase|baseChange_mul|RelativeGroupLaw.baseChange`
- `baseChange|pullback|tangent`
- `homeomorph|Homeomorph|isConnected`
- `p07_cq_group_law_pullback_857cd4d38c|p07_cq_abelian_surface_quotient_857cd4d38c|p07_cq_level_geometry_pullback_857cd4d38c`
- `\b(sorry|admit|axiom)\b`
- `git -C .lake/packages/mathlib rev-parse HEAD`
- `git -C .lake/packages/mathlib status --porcelain`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lean /tmp/p07-cq-decomposition-857cd4d38c/TypesAgainstPrerequisites.lean`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lean -o /tmp/p07-cq-decomposition-857cd4d38c/Submission.olean Submission.lean`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lean /tmp/p07-cq-decomposition-857cd4d38c/AxiomsVerified.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/project/Definitions/Def_CerednikDrinfeld_QMModuli.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/project/Definitions/Def_AlgebraicGeometry_RelativeGroupLaw.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/project/Definitions/Def_JacJ1Iface.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/project/P2M`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/mathlib/Mathlib/AlgebraicGeometry/PullbackCarrier.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/mathlib/Mathlib/AlgebraicGeometry/Morphisms/Smooth.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/mathlib/Mathlib/AlgebraicGeometry/Morphisms/Proper.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/mathlib/Mathlib/AlgebraicGeometry/Morphisms/ClosedImmersion.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/mathlib/Mathlib/AlgebraicGeometry/Morphisms/Finite.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/mathlib/Mathlib/AlgebraicGeometry/Morphisms/Flat.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/mathlib/Mathlib/AlgebraicGeometry/Morphisms/FinitePresentation.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/mathlib/Mathlib/AlgebraicGeometry/Morphisms/FlatRank.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/mathlib/Mathlib/Topology/KrullDimension.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/Submission.lean`
- `/tmp/p07-cq-decomposition-857cd4d38c/TypesAgainstPrerequisites.lean`
- `/tmp/p07-cq-decomposition-857cd4d38c/TypesAgainstPrerequisites.log`
- `/tmp/p07-cq-decomposition-857cd4d38c/Submission.log`
- `/tmp/p07-cq-decomposition-857cd4d38c/AxiomsVerified.lean`
- `/tmp/p07-cq-decomposition-857cd4d38c/AxiomsVerified.log`

The snapshot pins project 73257f1e32d99b75813b037f28a5cf45a2db886d and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. The definitions confirm the exact group-law, bundle, curve, and level obligations. PullbackCarrier:328 supplies range_fst; ClosedImmersion:115 and :382 supply quotient closed immersions and base-change stability; Smooth:117 and Proper:72 supply the other bundle properties. Finite:60, Flat:81, FinitePresentation:85, and FlatRank:157 support the level-geometry statement. KrullDimension:53 supplies homeomorphism invariance. No relevant P2M helper or existing relative-group-law base-change construction was found. None of the proposed names occurs in the inspected DAG or handoffs. All nine dependency checkouts are clean and match their pinned revisions. The 47 prerequisite source modules match the snapshot and cached-build sources byte-for-byte. All three proposed types elaborate without warnings against Submission's unchanged five imports. Symbolic quotient-ring instance synthesis returns Ideal.Quotient.commRing J. The completed transitive axiom audit reports only propext, Classical.choice, and Quot.sound. Literal import Submission validation remains blocked: compiling the unchanged module fails on the pre-existing attribute references AlgebraicGeometry.Scheme.Hom.opensMapFinal, GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase, and RegularLocalRingQuotientAscent.dualNumberFst_apply. No source repair or proof acceptance is claimed.
