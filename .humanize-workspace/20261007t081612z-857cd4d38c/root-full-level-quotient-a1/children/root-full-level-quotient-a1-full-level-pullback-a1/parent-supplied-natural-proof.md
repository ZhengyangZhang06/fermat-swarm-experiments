# Parent-supplied natural-language proof

- Parent DAG node: `root.full_level_quotient-a1`
- Child DAG node: `root.full_level_quotient-a1.full_level_pullback-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Put β = Spec(φ), and unpack the assumed IsPullbackVia witness. In particular, the square with g, ET.f, E.f, and β is a pullback. For every universe-zero scheme W and t : W → Spec T, composition with g defines a bijection B_t from ET-points over t to E-points over t ≫ β. Its inverse sends R to the pullback lift of R and t. The projection equations prove one inverse identity, and uniqueness of a morphism with both given projections proves the other. Associativity of composition shows that these bijections commute with precomposition.
2. The multiplication component of IsPullbackVia says exactly that B_t preserves multiplication. It also preserves identity: if H is the image of the identity, multiplication preservation gives H·H = H. Multiplying on the left by H⁻¹ and using associativity yields H = 1. Induction now proves preservation of nsmulPt for every natural k. The zero case is identity preservation; the successor case uses the recursive multiplication formula and the induction hypothesis. The action component of IsPullbackVia gives B_t(pushPt(ET.act(m), Q)) = pushPt(E.act(m), B_t(Q)) for every m ∈ Λ, by associativity of composition.
3. Precomposition of E-points along any compatible scheme morphism preserves multiplication by E.L.mul_natural. It preserves identity by the same idempotence argument: the image H of identity satisfies H·H = H and hence H = 1. Induction on k then shows that precomposition preserves nsmulPt for every k. These assertions also apply to ET.L, using its corresponding group-law fields.
4. Write P = L.P. The pair of morphisms β ≫ P.1 : Spec T → E.A and id : Spec T → Spec T is compatible with the pullback square because P.1 ≫ E.f = id. Let P_T be its unique lift to ET.A. Its second projection is the identity, so it is a section of ET.f, and its first projection gives P_T.1 ≫ g = β ≫ P.1. Thus B_id(P_T) is precisely P precomposed with β, with the base maps identified by the identity laws.
5. Precompose L.torsion with β. By step 3, the resulting E-point β ≫ P is n-torsion. By step 4 it is B_id(P_T), and by step 2 its n-fold sum and identity are the images under B_id of the corresponding ET-points. Injectivity of B_id therefore gives nsmulPt ET.L id n P_T = ET.L.one id. This proves the torsion field for the prospective full-level structure.
6. Fix an algebraically closed field K and α : T → K, and put α_S = α ∘ φ. Functoriality gives Spec(α_S) = Spec(α) ≫ β. The definition of sectionAt is precomposition of the section. Therefore step 4 and associativity show that B at the geometric point α sends sectionAt(P_T,K,α) to sectionAt(P,K,α_S). Combining this identity with step 2 gives the same correspondence after applying the action of any m ∈ Λ.
7. To verify generation, let Q be an n-torsion ET-point over α. Preservation of nsmulPt and identity shows that B(Q) is an n-torsion E-point over α_S. Apply L.generates to obtain m ∈ Λ such that the action of m on sectionAt(P,K,α_S) equals B(Q). By step 6 and action compatibility, the left side is the B-image of the action of m on sectionAt(P_T,K,α). Injectivity of B gives the required equality with Q. This proves the generates field for every K, α, and Q satisfying its hypotheses.
8. For the annihilator field, fix K, α, and m ∈ Λ. By injectivity of B, preservation of identity, and step 6, the action of m kills sectionAt(P_T,K,α) if and only if it kills sectionAt(P,K,α_S). L.annihilator identifies the latter condition with the existence of y ∈ Λ such that (m : QuaternionAlgebra ℚ a 0 b) = (n : ℚ) • (y : QuaternionAlgebra ℚ a 0 b). This is exactly the required new annihilator condition; its right-hand side is unchanged by base change. Assemble P_T and the torsion, generation, and annihilator proofs into LT : ET.FullLevel n. The section equation proved in step 4 is the asserted equality for LT, completing the proof.

## Key steps

1. Obtain natural bijections on relative points from the given pullback square.
2. Derive preservation of identity, repeated addition, and quaternion actions from IsPullbackVia.
3. Show that precomposition preserves identity and repeated addition.
4. Lift the distinguished section and prove its required projection equation.
5. Transfer global n-torsion by injectivity of the point bijection.
6. Identify specialized sections and transfer generation of geometric torsion points.
7. Transfer the annihilator equivalence and assemble the full-level structure.

## Reference use

### local-project

Queries:
- `baseChange|pullback|structure RelativeGroupLaw|structure AbelianSchemePropertyBundle`
- `isStableUnderBaseChange|finrank_pullback_snd|isClosedImmersion_SpecMap|surjective`
- `FakeEllipticCurve|FullLevel|IsPullbackVia`
- `range_pullback|range.*pullback|pullback.*range|pullback.*preimage|image_preimage`
- `\b(sorry|admit|axiom)\b`
- `p07_flq_curve_quotient_857cd4d38c|p07_flq_full_level_pullback_857cd4d38c`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lean -DautoImplicit=false -DmaxHeartbeats=4000000 -DsynthInstance.maxHeartbeats=400000 -Dbackward.isDefEq.respectTransparency.types=false /tmp/p07-flq-contract-kgrows4p/TypesAgainstPrerequisites.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/project/Definitions/Def_CerednikDrinfeld_QMModuli.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/project/Definitions/Def_CerednikDrinfeld_QMFineModuli.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/project/Definitions/Def_CerednikDrinfeld_QMFormalModuleOf.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/project/Definitions/Def_AlgebraicGeometry_RelativeGroupLaw.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/project/Definitions/Def_JacJ1Iface.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/project/P2M`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/mathlib/Mathlib/AlgebraicGeometry/Morphisms/Smooth.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/mathlib/Mathlib/AlgebraicGeometry/Morphisms/Proper.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/mathlib/Mathlib/AlgebraicGeometry/Morphisms/ClosedImmersion.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/mathlib/Mathlib/AlgebraicGeometry/Morphisms/FlatRank.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/mathlib/Mathlib/AlgebraicGeometry/Morphisms/Finite.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/mathlib/Mathlib/AlgebraicGeometry/Morphisms/Flat.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/mathlib/Mathlib/AlgebraicGeometry/Morphisms/FinitePresentation.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/mathlib/Mathlib/AlgebraicGeometry/PullbackCarrier.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/Submission.lean`
- `/tmp/p07-flq-contract-kgrows4p/Submission.log`
- `/tmp/p07-flq-contract-kgrows4p/Types.lean`
- `/tmp/p07-flq-contract-kgrows4p/TypesAgainstPrerequisites.lean`
- `/tmp/p07-flq-contract-kgrows4p/TypesAgainstPrerequisites.log`

The manifest pins project 73257f1e32d99b75813b037f28a5cf45a2db886d and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. The inspected definitions confirm every curve, full-level, and IsPullbackVia field. The cited base-change results occur at Smooth:117, Proper:72, ClosedImmersion:382, and FlatRank:157; the last requires only flatness and finiteness. PullbackCarrier:328 supplies Scheme.Pullback.range_fst. The P2M search returned no matching helpers, and neither proposed name appears in the inspected DAG or handoffs. Relevant definition files had no explicit axiom or admitted-proof matches. All 47 unchanged prerequisite modules compiled. Both proposed types checked without warnings against Submission's identical five imports, and quotient-ring instance synthesis returned Ideal.Quotient.commRing J. Transitive axiom checks of the three curve/full-level/pullback declarations, one_natural, and the queried smoothness, properness, closed-immersion, rank, and pullback-range results returned only propext, Classical.choice, and Quot.sound. However, literal import Submission validation is blocked: its existing attribute commands fail on AlgebraicGeometry.Scheme.Hom.opensMapFinal, GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase, and RegularLocalRingQuotientAscent.dualNumberFst_apply. No source was repaired or theorem acceptance claimed.
