# Parent-supplied natural-language proof

- Parent DAG node: `root.rigidification_reduction-a1`
- Child DAG node: `root.rigidification_reduction-a1.isogeny_level_transport-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Put u = i.hom, v = i.inv, z = j.hom and w = j.inv. Write κ = Spec(k.toRingHom) : Spec U → Spec T and ε = Spec(k.symm.toRingHom) : Spec T → Spec U. The ring-isomorphism identities and contravariance of Spec give ε ≫ κ = id and κ ≫ ε = id. The scheme-isomorphism identities give u ≫ v = id, v ≫ u = id, z ≫ w = id and w ≫ z = id. Define Φ = v ≫ φ ≫ z and Ψ = w ≫ ψ ≫ u, the exact morphisms in the conclusion.
2. The commuting equations contained in the four pullback hypotheses are u ≫ E.f = D.f ≫ κ, v ≫ D.f = E.f ≫ ε, z ≫ F.f = H.f ≫ κ and w ≫ H.f = F.f ≫ ε. The old isogeny-pair hypothesis supplies ψ ≫ D.f = H.f as well as φ's over-base equation. Therefore Φ ≫ F.f = v ≫ φ ≫ H.f ≫ κ = v ≫ D.f ≫ κ = E.f ≫ ε ≫ κ = E.f. Likewise Ψ ≫ E.f = w ≫ ψ ≫ D.f ≫ κ = w ≫ H.f ≫ κ = F.f. Denote these proofs by hΦ and hΨ. Any alternative proof of φ's over-base equality appearing in the isogeny-pair hypothesis agrees with the given hφ by proof irrelevance.
3. For any scheme X and t : X → Spec T, composition with v sends E-points over t to D-points over t ≫ ε; composition with w sends F-points over t to H-points over t ≫ ε. For any s : X → Spec U, composition with u sends D-points over s to E-points over s ≫ κ, and composition with z sends H-points to F-points over s ≫ κ. The equations in step 2 show that all four point maps are well-defined. Each preserves multiplication: its defining IsPullbackVia multiplication equality is the equality of underlying point morphisms, and subtype extensionality makes it the corresponding equality of points. Each also carries a level factorization to a level factorization, since its IsPullbackVia level condition supplies precisely a witness through the target level immersion.
4. Let P,Q be E-points over t. Their images under mapPt Φ hΦ are obtained successively by composition with v, application of mapPt φ hφ, and composition with z. The last base is (t ≫ ε) ≫ κ = t; after this identification the underlying composite morphism is P.1 ≫ Φ, respectively Q.1 ≫ Φ. The first and third point maps preserve multiplication by step 3, and the middle map preserves multiplication by the old isogeny-pair hypothesis. Applying these three multiplication equalities in order proves mapPt Φ hΦ (E.L.mul t P Q) = F.L.mul t (mapPt Φ hΦ P) (mapPt Φ hΦ Q). For F-points P,Q, use composition with w, the old multiplication-preserving map ψ, and composition with u. The same base identity and the three corresponding equalities give the multiplication condition for Ψ. All equalities of over-base points follow from equality of underlying morphisms and proof irrelevance.
5. Fix x ∈ Λ. The action equations for v, φ and z give E.act(x) ≫ Φ = v ≫ D.act(x) ≫ φ ≫ z = v ≫ φ ≫ H.act(x) ≫ z = Φ ≫ F.act(x). The action equations for w, ψ and u give F.act(x) ≫ Ψ = w ≫ H.act(x) ≫ ψ ≫ u = w ≫ ψ ≫ D.act(x) ≫ u = Ψ ≫ E.act(x).
6. Fix any membership witness hd for the quaternion scalar obtained from d in Λ, and let x_d be that element of Λ. Cancelling z ≫ w gives Φ ≫ Ψ = v ≫ (φ ≫ ψ) ≫ u. The old scalar equation changes this to v ≫ D.act(x_d) ≫ u. The action equation E.act(x_d) ≫ v = v ≫ D.act(x_d), followed by v ≫ u = id, makes it E.act(x_d). Cancelling u ≫ v in the other product similarly gives Ψ ≫ Φ = w ≫ (ψ ≫ φ) ≫ z = w ≫ H.act(x_d) ≫ z = F.act(x_d). This works for every hd; no hypothesis asserting that such a witness exists is needed. Steps 2, 4, 5 and 6 are exactly all fields of IsIsogenyPair d E F Φ Ψ.
7. Fix any E-point P over t that factors through E.lev. The level condition for v sends P to a D-point factoring through D.lev. The assumed PreservesLevel D H φ hφ sends that point under φ to an H-point factoring through H.lev. The level condition for z supplies a factorization of its image through F.lev. After (t ≫ ε) ≫ κ = t, the underlying image is P.1 ≫ v ≫ φ ≫ z = (mapPt Φ hΦ P).1. Thus this factorization proves PreservesLevel E F Φ hΦ.
8. Return the isogeny-pair assertion from step 6 and hΦ with the level assertion from step 7.

## Key steps

1. Define the conjugated morphisms and record the ring and scheme inverse identities.
2. Prove both conjugated morphisms lie over Spec T.
3. Extract multiplication and level preservation for the four transport maps on points.
4. Compose point-map multiplication identities to prove both isogeny multiplication conditions.
5. Compose the action equations to obtain equivariance.
6. Cancel inverse isomorphisms and transport both scalar-action equations.
7. Transport a level-factorization witness through the inverse isomorphism, old isogeny, and forward isomorphism.
8. Return the isogeny pair and its forward over-base proof with level preservation.

## Reference use

### local-project

Queries:
- `rg -n 'structure Rigidification|def IsPullbackVia|structure IsPullbackVia|def IsIsogenyPair|structure IsIsogenyPair|preservesLevel|namespace Rigidification' .humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/project/Definitions`
- `rg -n 'IsPullbackVia|IsIsogenyPair' .humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/project/Theorems --glob '*.lean'`
- `rg -n 'paste_horiz|paste_vert|theorem.*comp|def mapPt|def FactorsThrough' .humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/mathlib/Mathlib/CategoryTheory/Limits/Shapes/Pullback/IsPullback .humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/project/Definitions/Def_CerednikDrinfeld_QMModuli.lean`
- `rg -n --hidden --no-ignore 'p07_rr_pullback_comp_857cd4d38c|p07_rr_isogeny_transport_857cd4d38c' /mnt/data/zhengyang-workspace/fermat-swarm-projects --glob 'dag.json' --glob '*handoff*.json' --glob '*.lean'`
- `#print axioms CerednikDrinfeld.QM.FakeEllipticCurve.IsPullbackVia`
- `#print axioms CerednikDrinfeld.QM.FakeEllipticCurve.IsIsogenyPair`
- `#print axioms CerednikDrinfeld.QM.FakeEllipticCurve.PreservesLevel`
- `#print axioms CerednikDrinfeld.QM.mapPt`
- `#print axioms CerednikDrinfeld.QM.FactorsThrough`
- `#print axioms CategoryTheory.IsPullback.paste_horiz`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/project/Definitions/Def_CerednikDrinfeld_QMFormalModuleOf.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/project/Definitions/Def_CerednikDrinfeld_QMIsogeny.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/project/Definitions/Def_CerednikDrinfeld_QMRigidification.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/project/Definitions/Def_CerednikDrinfeld_QMModuli.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/project/Theorems`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/mathlib/Mathlib/CategoryTheory/Limits/Shapes/Pullback/IsPullback/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/dag.json`
- `/tmp/p07-rr-decomposition-857cd4d38c/TypesAgainstImports.lean`
- `/tmp/p07-rr-decomposition-857cd4d38c/types-and-axioms.log`
- `/tmp/p07-rr-decomposition-857cd4d38c/literal-submission.log`
- `/tmp/p07-rr-decomposition-857cd4d38c/literal-import.log`

The manifest pins project 73257f1e32d99b75813b037f28a5cf45a2db886d and mathlib db584cd6d46c92f209a44c0f1c829460d327499d; the checked revisions match and their checked tracked sources are clean. All 47 project modules in the import closure match the snapshot and the cached source modules used for diagnostics. IsPullbackVia contains a pullback square, multiplication compatibility, action compatibility, and directional level preservation. IsIsogenyPair and PreservesLevel have exactly the conditions addressed below. Mathlib supplies IsPullback.paste_horiz. The searched project Theorems directory contains no IsPullbackVia or IsIsogenyPair matches, and the proposed-name search found no collisions. Both proposed types elaborate against Submission's five imports under Lean 4.33.1. The six audited declarations depend only on propext, Classical.choice and Quot.sound. Literal import Submission remains blocked: unchanged Submission.lean reports unknown attribute targets AlgebraicGeometry.Scheme.Hom.opensMapFinal, GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase and RegularLocalRingQuotientAscent.dualNumberFst_apply, so no importable Submission object is produced. These diagnostic checks are not comparator acceptance.
