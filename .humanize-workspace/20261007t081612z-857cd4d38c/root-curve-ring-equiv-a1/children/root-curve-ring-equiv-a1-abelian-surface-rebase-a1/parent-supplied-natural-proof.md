# Parent-supplied natural-language proof

- Parent DAG node: `root.curve_ring_equiv-a1`
- Child DAG node: `root.curve_ring_equiv-a1.abelian_surface_rebase-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Put κ = Spec(k), ε = Spec(k⁻¹), and fT = f ≫ κ. The inverse identities for k imply κ ≫ ε = id and ε ≫ κ = id. In particular, fT ≫ ε = f.
2. The square with top arrow id_A, left arrow fT, right arrow f, and bottom arrow ε is a pullback. To verify its universal property, take any scheme W and morphisms R : W → A and t : W → Spec T satisfying R ≫ f = t ≫ ε. The unique candidate for the lift is R because the top projection is id_A. It has the required second projection since R ≫ fT = R ≫ f ≫ κ = t ≫ ε ≫ κ = t. Thus the candidate is a lift and is unique.
3. The given bundle makes f smooth and proper. Apply stability under base change to the pullback of step 2. This makes fT smooth by AlgebraicGeometry.smooth_isStableUnderBaseChange, Mathlib/AlgebraicGeometry/Morphisms/Smooth.lean:117, and proper by AlgebraicGeometry.IsProper.isStableUnderBaseChange, Mathlib/AlgebraicGeometry/Morphisms/Proper.lean:72, both at pinned revision db584cd6d46c92f209a44c0f1c829460d327499d.
4. Fix s : Spec T. For every point x of A, fT(x) = s is equivalent to f(x) = ε(s): apply ε for the forward implication and κ for the reverse implication. Hence fT⁻¹({s}) and f⁻¹({ε(s)}) are equal subsets of the same topological space A. The latter is connected by the original bundle, so the former is connected. Equality of these subsets also identifies their subtype topologies. Therefore their topological Krull dimensions are equal, and the assumed dimension formula at ε(s) gives dimension two for the fibre of fT at s.
5. Choose G : RelativeGroupLaw U f from the original bundle's hasGroupLaw field. Apply the sibling theorem p07_cre_group_law_857cd4d38c to T,U,k,A,f,G. It supplies H : RelativeGroupLaw T fT; therefore RelativeGroupLaw T fT is nonempty. No commutativity hypothesis is needed for this application.
6. Assemble smoothness and properness from step 3, connected fibres from step 4, and existence of H from step 5 into AbelianSchemePropertyBundle T fT. The dimension statement was proved for every s in step 4. This proves both conjuncts.

## Key steps

1. Express the rebased morphism as a pullback along Spec(k⁻¹).
2. Transfer smoothness and properness using pinned base-change results.
3. Identify each new topological fibre with the old fibre over Spec(k⁻¹)(s).
4. Transfer connectedness and topological Krull dimension through equality of fibre subsets.
5. Use the group-law sibling to supply the bundle's existence field.
6. Assemble the transported bundle and dimension formula.

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
