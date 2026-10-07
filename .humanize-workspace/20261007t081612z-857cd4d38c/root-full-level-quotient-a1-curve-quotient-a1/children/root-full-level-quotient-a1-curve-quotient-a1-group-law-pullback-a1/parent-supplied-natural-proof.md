# Parent-supplied natural-language proof

- Parent DAG node: `root.full_level_quotient-a1.curve_quotient-a1`
- Child DAG node: `root.full_level_quotient-a1.curve_quotient-a1.group_law_pullback-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix S, T, φ, A, f, and G as in the statement, and write β, A_T, p, and g for the specified base map, pullback, and projections. Their commutativity relation is g ≫ f = p ≫ β. For P : SchemeHomOver t p define B(W,t)(P) to have underlying morphism P.1 ≫ g. It lies over t ≫ β because (P.1 ≫ g) ≫ f = P.1 ≫ p ≫ β = t ≫ β.
2. For R : SchemeHomOver (t ≫ β) f, its defining equation R.1 ≫ f = t ≫ β permits the pullback lift of R.1 and t. Its second projection is t, so it defines a point over t. Its first projection is R.1, showing that B sends this lift to R. Conversely, the lift associated to B(P) has projections P.1 ≫ g and t, which are also the projections of P.1. Pullback uniqueness therefore identifies that lift with P. Thus these maps are inverse equivalences, and the required underlying-morphism formula holds.
3. These equivalences commute with precomposition. Indeed, for h : W' → W and h ≫ t = t', the underlying morphisms of B(W',t')(h*P) and h*(B(W,t)(P)) are respectively (h ≫ P.1) ≫ g and h ≫ (P.1 ≫ g). Associativity identifies them; their base equations agree by h ≫ t = t' and associativity. Equality of underlying morphisms is equality of these subtype points.
4. Define H.mul t P Q = B(W,t)⁻¹(G.mul (t ≫ β) (B(W,t) P) (B(W,t) Q)), H.one t = B(W,t)⁻¹(G.one (t ≫ β)), and H.inv t P = B(W,t)⁻¹(G.inv (t ≫ β) (B(W,t) P)). The inverse identities from step 2 immediately give all three required preservation equations.
5. For each fixed W,t, apply the injective B(W,t) to the proposed group-law identities. The images of the two associativity sides are G.mul (G.mul (BP) (BQ)) (BR) and G.mul (BP) (G.mul (BQ) (BR)), equal by G.mul_assoc at t ≫ β. The image of H.mul t (H.one t) P is G.mul (t ≫ β) (G.one (t ≫ β)) (BP) = BP by G.one_mul. Similarly G.mul_one proves the right identity law. The image of H.mul t (H.inv t P) P is G.mul (t ≫ β) (G.inv (t ≫ β) (BP)) (BP) = G.one (t ≫ β), which is the image of H.one t, by G.inv_mul_cancel. Injectivity proves each required law for H.
6. To prove H.mul_natural, take h : W' → W with h ≫ t = t'. Apply B(W',t') to its two sides. By steps 3 and 4, the left side becomes the precomposition by h of G.mul (t ≫ β) (BP) (BQ). The right side becomes the product, over t' ≫ β, of the precompositions of BP and BQ. These are equal by G.mul_natural, since h ≫ (t ≫ β) = t' ≫ β. Injectivity gives H.mul_natural. Thus the operations and laws define H : RelativeGroupLaw T p.
7. If G.IsCommutative, the B-images of H.mul t P Q and H.mul t Q P are equal by commutativity of G at t ≫ β. Injectivity proves H.IsCommutative. The constructed H and family B satisfy every asserted property.

## Key steps

1. Use pullback lift and projection uniqueness to construct the point equivalences.
2. Prove that the equivalences commute with precomposition by associativity.
3. Transport multiplication, identity, and inverse through the equivalences.
4. Verify the group laws and multiplication naturality by injectivity.
5. Transfer commutativity and return the preservation equations.

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
