# Parent-supplied natural-language proof

- Parent DAG node: `root.full_level_quotient-a1.full_level_pullback-a1`
- Child DAG node: `root.full_level_quotient-a1.full_level_pullback-a1.pullback_point_equivalence-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix all the stated data, W and t. Write β = Spec(φ) and tS = t ≫ β. Unpack IsPullbackVia to obtain a pullback square h with g ≫ E.f = ET.f ≫ β, together with multiplication and action compatibility. For P : SchemeHomOver t ET.f, associativity gives (P.1 ≫ g) ≫ E.f = P.1 ≫ (ET.f ≫ β) = t ≫ β = tS. Define F(P) to be the E-point whose underlying morphism is P.1 ≫ g.
2. For R : SchemeHomOver tS E.f, its defining equation is R.1 ≫ E.f = t ≫ β. The pullback universal property therefore gives a morphism h.lift R.1 t R.2 : W → ET.A whose compositions with g and ET.f are respectively R.1 and t. Define I(R) to be this morphism with its second projection equation. Its first projection equation implies F(I(R)) = R by subtype extensionality.
3. The underlying morphism of I(F(P)) has compositions P.1 ≫ g and t with g and ET.f. These are also the compositions of P.1, since P.1 ≫ ET.f = t. Pullback uniqueness gives equality of the underlying morphisms, and subtype extensionality gives I(F(P)) = P. Thus F and I define an equivalence B. Its underlying-morphism formula is true by the definition of F.
4. The multiplication clause of IsPullbackVia identifies the underlying morphism of B(ET.L.mul t P Q) with that of E.L.mul tS (B P) (B Q). The points appearing in that clause have exactly the underlying morphisms defining B P and B Q; their membership proofs are irrelevant. Subtype extensionality gives the asserted multiplication equality.
5. Put H = B(ET.L.one t). Use multiplication, inverse and identity from E.L at tS in this step. Step 4 and the source identity law give H·H = H. The target group-law identities then give H = 1·H = (H⁻¹·H)·H = H⁻¹·(H·H) = H⁻¹·H = 1. Consequently B(ET.L.one t) = E.L.one tS.
6. Fix P and induct on k. For k = 0, the defining zero equation of nsmulPt reduces the claim to step 5. For k+1, the recursive equation and step 4 give B(nsmulPt ET.L t (k+1) P) = E.L.mul tS (B(nsmulPt ET.L t k P)) (B P). The induction hypothesis rewrites this to E.L.mul tS (nsmulPt E.L tS k (B P)) (B P), which is nsmulPt E.L tS (k+1) (B P) by the recursive equation. This proves preservation of every repeated sum.
7. Fix x ∈ Λ and P. By the definitions of pushPt and B, the underlying morphism of B(pushPt (ET.act x) (ET.act_over x) P) is (P.1 ≫ ET.act x) ≫ g. Associativity and the action clause ET.act x ≫ g = g ≫ E.act x rewrite this as (P.1 ≫ g) ≫ E.act x. This is the underlying morphism of pushPt (E.act x) (E.act_over x) (B P). Subtype extensionality proves action compatibility. Combining steps 3–7 supplies the equivalence and all five required properties.

## Key steps

1. Define the forward map by composition with g, using commutativity of the pullback square.
2. Define its inverse by the pullback lift and verify both inverse identities using projection equations and uniqueness.
3. Convert the given multiplication compatibility into equality of points.
4. Prove identity preservation by cancelling the idempotent image of identity.
5. Prove nsmulPt preservation by induction.
6. Prove action compatibility by associativity and the action equation in IsPullbackVia.

## Reference use

### local-project

Queries:
- `IsPullbackVia|nsmulPt|structure FullLevel|def sectionAt|mul_natural`
- `def SchemeHomOver|def schemeHomOverComp|schemeHomOverComp_coe|theorem.*nsmulPt|lemma.*nsmulPt|nsmulPt.*natural|point.*[Ee]quiv|[Pp]ullback.*[Ee]quiv`
- `noncomputable def lift|theorem lift_fst|theorem lift_snd|hom_ext|def lift`
- `p07_flp_|nsmul_precomp|pullback_point_equiv`
- `opensMapFinal|baseChangePointToBase_ofBase|dualNumberFst_apply`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/project/Definitions/Def_CerednikDrinfeld_QMFormalModuleOf.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/project/Definitions/Def_CerednikDrinfeld_QMFineModuli.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/project/Definitions/Def_CerednikDrinfeld_QMModuli.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/project/Definitions/Def_AlgebraicGeometry_RelativeGroupLaw.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/mathlib/Mathlib/CategoryTheory/Limits/Shapes/Pullback/IsPullback/Defs.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/project/Submission.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/dag.json`
- `/tmp/p07-flp-types-1n_g3clh/CheckDefinitions.lean`
- `/tmp/p07-flp-types-1n_g3clh/diagnostic-typecheck.log`

Both snapshots are clean at the manifest revisions: project 73257f1e32d99b75813b037f28a5cf45a2db886d and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. Installed dependencies also match their pinned revisions and are clean. IsPullbackVia supplies precisely the pullback, multiplication, and action compatibilities used below. RelativeGroupLaw.one_natural already proves identity preservation under precomposition. No existing nsmulPt naturality theorem or matching fake-curve pullback point-equivalence theorem was found. IsPullback.lift, lift_fst, lift_snd, and hom_ext supply the required universal-property infrastructure. Neither proposed identifier is reserved in the inspected DAG. Both exact child types pass the controller lexical validator and elaborate as Prop against Submission's unchanged definition imports with Lean 4.33.1 and the pinned options. Operations are explicitly tied to the specified relative group laws; no inline algebraic instance is constructed. Transitive axiom checks of the cited infrastructure returned only propext, Classical.choice, and Quot.sound. However, unchanged Submission.lean fails at its attribute commands on AlgebraicGeometry.Scheme.Hom.opensMapFinal, GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase, and RegularLocalRingQuotientAscent.dualNumberFst_apply. Therefore literal import Submission validation remains blocked; diagnostic elaboration is not comparator acceptance.
