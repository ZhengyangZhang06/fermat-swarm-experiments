# Parent-supplied natural-language proof

- Parent DAG node: `root.full_level_quotient-a1.curve_quotient-a1`
- Child DAG node: `root.full_level_quotient-a1.curve_quotient-a1.level_geometry_pullback-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix the data and hypotheses, and form the two specified pullbacks. Their projection equations are g ≫ f = p ≫ β and r ≫ c = d ≫ β, with c = ℓ ≫ f.
2. The pair r ≫ ℓ : C_T → A and d : C_T → Spec T is compatible over Spec S, because (r ≫ ℓ) ≫ f = r ≫ c = d ≫ β. Define ℓT to be its pullback lift to A_T. The lift equations give ℓT ≫ g = r ≫ ℓ and ℓT ≫ p = d.
3. To prove the square (r,ℓT,ℓ,g) is a pullback, take any universe-zero scheme W, R : W → C, and Q : W → A_T satisfying R ≫ ℓ = Q ≫ g. Set t = Q ≫ p. Then R ≫ c = (R ≫ ℓ) ≫ f = (Q ≫ g) ≫ f = (Q ≫ p) ≫ β = t ≫ β. The pullback defining C_T therefore supplies U : W → C_T with U ≫ r = R and U ≫ d = t. The morphisms U ≫ ℓT and Q have equal g-projections by the assumed equation, and equal p-projections by step 2 and the definition of t. Uniqueness for A_T gives U ≫ ℓT = Q.
4. If U' also satisfies U' ≫ r = R and U' ≫ ℓT = Q, then U' ≫ d = U' ≫ ℓT ≫ p = Q ≫ p = t. The two projections of U' and U to C and Spec T agree, so uniqueness for C_T gives U' = U. Together with ℓT ≫ g = r ≫ ℓ, this proves CategoryTheory.IsPullback r ℓT ℓ g.
5. Thus ℓT is a base change of ℓ along g. More explicitly, the universal properties identify this square with the canonical pullback square by mutually inverse comparison maps; their composites are identities by uniqueness. Since ℓ is a closed immersion, stability under base change and under isomorphism imply that ℓT is a closed immersion. These are the pinned results IsClosedImmersion.isStableUnderBaseChange and IsClosedImmersion.respectsIso in Mathlib/AlgebraicGeometry/Morphisms/ClosedImmersion.lean:382 and :91, at revision db584cd6d46c92f209a44c0f1c829460d327499d.
6. If Q = U ≫ ℓT, then Q ≫ g = U ≫ r ≫ ℓ, so Q ≫ g factors through ℓ, with witness U ≫ r. Conversely, a factorization R ≫ ℓ = Q ≫ g is exactly the compatibility used in step 3, whose lift U satisfies U ≫ ℓT = Q. This proves the claimed equivalence for every W and every Q, without an additional condition on its base morphism.
7. The morphism d = pullback.snd c β is the base change of c. Apply stability under base change of finiteness, flatness, and local finite presentation to the three hypotheses on c. The corresponding pinned results are in Mathlib/AlgebraicGeometry/Morphisms/Finite.lean:60, Morphisms/Flat.lean:81, and Morphisms/FinitePresentation.lean:85. They give IsFinite d, Flat d, and LocallyOfFinitePresentation d, respectively.
8. For each t ∈ Spec T, apply AlgebraicGeometry.Scheme.Hom.finrank_pullback_snd to c, β, and t, using the assumed Flat c and IsFinite c. Its conclusion is d.finrank(t) = c.finrank(β(t)); the exact pinned source is Mathlib/AlgebraicGeometry/Morphisms/FlatRank.lean:157. The witness ℓT, the pullback property from steps 3–4, the second projection equation from step 2, and the properties proved in steps 5–8 establish every conjunct of the statement.

## Key steps

1. Construct the induced level immersion using the two pullback projections.
2. Prove its square with the original immersion is cartesian by explicit existence and uniqueness of lifts.
3. Transfer closed immersion and prove the two-way factorization criterion.
4. Base-change finiteness, flatness, and local finite presentation of the level structure morphism.
5. Apply the finite-flat pullback rank formula.

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
