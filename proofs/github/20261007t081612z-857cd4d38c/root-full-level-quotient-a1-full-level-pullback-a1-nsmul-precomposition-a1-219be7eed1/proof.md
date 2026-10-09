# Parent-supplied natural-language proof

- Parent DAG node: `root.full_level_quotient-a1.full_level_pullback-a1`
- Child DAG node: `root.full_level_quotient-a1.full_level_pullback-a1.nsmul_precomposition-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix the stated ring, schemes, group law and compatible morphisms. Write C(Q) = schemeHomOverComp ψ hψ Q. Its underlying morphism is ψ ≫ Q.1. Since (ψ ≫ Q.1) ≫ f = ψ ≫ t = t', this is a point over t'. The field L.mul_natural gives C(L.mul t Q Q') = L.mul t' (C(Q)) (C(Q')) for every Q,Q' over t.
2. Put H = C(L.one t), and write multiplication, inverse and identity using L at t'. Step 1 and L.one_mul imply H·H = H. Therefore H = 1·H = (H⁻¹·H)·H = H⁻¹·(H·H) = H⁻¹·H = 1, by the identity, inverse and associativity laws of L. Thus C(L.one t) = L.one t'. This equality is also the existing library theorem RelativeGroupLaw.one_natural.
3. Fix P and induct on k. For k = 0, nsmulPt L t 0 P is L.one t, and nsmulPt L t' 0 (C(P)) is L.one t'. Their required equality follows from step 2.
4. Suppose the equality holds for k. By the successor equation defining nsmulPt, C(nsmulPt L t (k+1) P) = C(L.mul t (nsmulPt L t k P) P). Step 1 rewrites this as L.mul t' (C(nsmulPt L t k P)) (C(P)). The induction hypothesis rewrites it as L.mul t' (nsmulPt L t' k (C(P))) (C(P)), which equals nsmulPt L t' (k+1) (C(P)) by the same successor equation. This completes the induction and proves the statement for every k and P.

## Key steps

1. Express compatible precomposition as the map C and apply multiplication naturality.
2. Show C preserves identity by the idempotence and inverse argument.
3. Prove the zero case using identity preservation.
4. Prove the successor case using multiplication naturality and the induction hypothesis.

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
