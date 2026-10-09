# Parent-supplied natural-language proof

- Parent DAG node: `root.curve_ring_equiv-a1`
- Child DAG node: `root.curve_ring_equiv-a1.finite_flat_rank_rebase-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Write κ = Spec(k) and ε = Spec(k⁻¹). Functoriality of Spec gives κ ≫ ε = id and ε ≫ κ = id. Define qT = q ≫ κ. Consequently qT ≫ ε = q.
2. Prove that the square with top arrow id_C, left arrow qT, right arrow q, and bottom arrow ε is a pullback. Given a scheme W and a compatible pair R : W → C, t : W → Spec T satisfying R ≫ q = t ≫ ε, choose R as the lift. Its first projection is R, and its second projection is R ≫ qT = R ≫ q ≫ κ = t ≫ ε ≫ κ = t. Any lift has first projection R through id_C, so it must equal R. This proves the universal property.
3. Apply base-change stability to this square and the three hypotheses on q. Finiteness follows from AlgebraicGeometry.IsFinite.instIsStableUnderBaseChangeScheme in Mathlib/AlgebraicGeometry/Morphisms/Finite.lean:60. Flatness follows from AlgebraicGeometry.Flat.isStableUnderBaseChange in Morphisms/Flat.lean:81. Local finite presentation follows from AlgebraicGeometry.locallyOfFinitePresentation_isStableUnderBaseChange in Morphisms/FinitePresentation.lean:85. These are the results at pinned revision db584cd6d46c92f209a44c0f1c829460d327499d. Thus qT has all three required properties.
4. Fix s : Spec T. Apply AlgebraicGeometry.Scheme.Hom.finrank_of_isPullback from Mathlib/AlgebraicGeometry/Morphisms/FlatRank.lean:165 at the same revision, with fst = id_C, snd = qT, f = q, g = ε, and the pullback square from step 2. Its hypotheses are exactly the assumed flatness and finiteness of q. Its conclusion is qT.finrank(s) = q.finrank(ε(s)). Since s was arbitrary, the rank formula holds everywhere. Together with step 3 this proves the complete conclusion.

## Key steps

1. Use the inverse Spec morphisms associated to the ring isomorphism.
2. Prove the identity-total-space square is a pullback by its universal property.
3. Transfer finiteness, flatness, and local finite presentation by base change.
4. Apply finrank_of_isPullback to obtain the exact rank formula.

## Reference use

### local-project

Queries:
- `structure FakeEllipticCurve|def IsPullbackVia|structure IsPullbackVia|act_trace|def tangentZero|def tangentScale|structure RelativeGroupLaw|structure AbelianScheme`
- `rebase|ringEquiv|RingEquiv|IsPullbackVia|transport`
- `transport|ringEquiv|rebase|baseChange`
- `isStableUnderBaseChange|finrank_pullback_snd|finrank_comp|IsIso`
- `p07_cre_group_law_857cd4d38c|p07_cre_abelian_surface_857cd4d38c|p07_cre_finite_flat_rank_857cd4d38c`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lean -DautoImplicit=false -DmaxHeartbeats=4000000 -DsynthInstance.maxHeartbeats=400000 -Dbackward.isDefEq.respectTransparency.types=false /tmp/p07_cre_contract_check/TypesDiagnostic.lean`
- `#print axioms AlgebraicGeometry.IsFinite.instIsStableUnderBaseChangeScheme`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/project/Definitions/Def_AlgebraicGeometry_RelativeGroupLaw.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/project/Definitions/Def_JacJ1Iface.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/project/Definitions/Def_CerednikDrinfeld_QMModuli.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/project/Definitions/Def_CerednikDrinfeld_QMFormalModuleOf.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/project/Definitions/Def_CerednikDrinfeld_QMModuliProps.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/project/P2M`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/mathlib/Mathlib/AlgebraicGeometry/Morphisms/Smooth.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/mathlib/Mathlib/AlgebraicGeometry/Morphisms/Proper.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/mathlib/Mathlib/AlgebraicGeometry/Morphisms/Finite.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/mathlib/Mathlib/AlgebraicGeometry/Morphisms/Flat.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/mathlib/Mathlib/AlgebraicGeometry/Morphisms/FinitePresentation.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/mathlib/Mathlib/AlgebraicGeometry/Morphisms/FlatRank.lean`
- `/tmp/p07_cre_contract_check/TypesDiagnostic.lean`
- `/tmp/p07_cre_contract_check/types_diagnostic.log`
- `/tmp/p07_cre_contract_check/finite_axiom.log`
- `/tmp/p07_cre_contract_check/unchanged_submission.log`

The snapshots are clean at project revision 73257f1e32d99b75813b037f28a5cf45a2db886d and mathlib revision db584cd6d46c92f209a44c0f1c829460d327499d; all installed dependencies match lake-manifest.json and are clean. Searches using /runtime/bin/rg found no reusable rebase/transport construction in the searched project files. RelativeGroupLaw specifies exactly the group identities and multiplication naturality used below; AbelianSchemePropertyBundle consists of smoothness, properness, connected fibres, and existence of a relative group law. The geometric files provide base-change stability, and FlatRank.lean:165 provides finrank_of_isPullback. All three proposed types elaborate with Lean 4.33.1 and the pinned project options against the definition imports. The audited definitions and cited results depend only on propext, Classical.choice, and Quot.sound. The inferred finite base-change instance is AlgebraicGeometry.IsFinite.instIsStableUnderBaseChangeScheme, and Spec(k) has the required direction. No proposed name occurs as an existing declaration or active DAG reservation. However, unchanged Submission.lean fails on the attribute references AlgebraicGeometry.Scheme.Hom.opensMapFinal, GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase, and RegularLocalRingQuotientAscent.dualNumberFst_apply. Therefore the literal import Submission gate remains blocked; diagnostic elaboration is not comparator acceptance.
