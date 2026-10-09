# Parent-supplied natural-language proof

- Parent DAG node: `root.curve_ring_equiv-a1`
- Child DAG node: `root.curve_ring_equiv-a1.group_law_rebase-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Define κ = Spec(k) and ε = Spec(k⁻¹). Functoriality of Spec and the two inverse identities for k give κ ≫ ε = id on Spec U and ε ≫ κ = id on Spec T. Put fT = f ≫ κ.
2. Fix W and t : W → Spec T. A morphism p : W → A satisfies p ≫ fT = t if and only if p ≫ f = t ≫ ε. In the forward direction, compose with ε and use κ ≫ ε = id; in the reverse direction, compose with κ and use ε ≫ κ = id. Define B(W,t) using this equivalence of conditions, leaving p unchanged. Define its inverse in the same way. Both composites are identities because their underlying morphisms are unchanged and equality of subtype elements follows from equality of their underlying morphisms. Thus B(W,t) is an equivalence with the required underlying-morphism equality.
3. These equivalences commute with precomposition. Indeed, let ψ : W' → W and suppose ψ ≫ t = t'. Precomposing either before or after applying B gives the underlying morphism ψ ≫ p. The old base maps satisfy ψ ≫ (t ≫ ε) = t' ≫ ε by associativity. Consequently the two resulting old relative points are equal by subtype extensionality. The same argument applies to the inverse equivalences.
4. For each W,t, define H.mul t P Q to be B(W,t)⁻¹ applied to G.mul (t ≫ ε) (B(W,t) P) (B(W,t) Q). Define H.one t to be B(W,t)⁻¹ of G.one (t ≫ ε), and H.inv t P to be B(W,t)⁻¹ of G.inv (t ≫ ε) (B(W,t) P). Applying B immediately gives each of the three asserted operation-preservation equations.
5. Verify the group identities by injectivity of B(W,t). Applying B to the two sides of associativity gives, respectively, G.mul (G.mul (B P) (B Q)) (B R) and G.mul (B P) (G.mul (B Q) (B R)); these are equal by G.mul_assoc. Applying B to the left identity equation gives G.mul G.one (B P) = B P, and applying it to the right identity equation gives G.mul (B P) G.one = B P. These follow from G.one_mul and G.mul_one. Applying B to inverse cancellation gives G.mul (G.inv (B P)) (B P) = G.one, which is G.inv_mul_cancel. In every case injectivity gives the required identity for H.
6. To prove H.mul_natural for ψ and t,t' as in step 3, apply B(W',t') to the desired equality. By step 3 and the multiplication-preservation equation, its left side becomes the precomposition of G.mul (t ≫ ε) (B P) (B Q); its right side becomes G.mul (t' ≫ ε) of the two precomposed points. These are equal by G.mul_natural, using ψ ≫ (t ≫ ε) = t' ≫ ε. Injectivity of B(W',t') proves H.mul_natural. All fields of RelativeGroupLaw are now verified.
7. If G is commutative, applying B(W,t) to H.mul t P Q and H.mul t Q P gives equal points by commutativity of G. Injectivity proves commutativity of H. Together with steps 2 and 4, H and B satisfy every asserted conjunct.

## Key steps

1. Use Spec(k) and Spec(k⁻¹) as inverse base morphisms.
2. Construct equivalences of relative points that preserve underlying morphisms.
3. Prove compatibility with precomposition by subtype extensionality.
4. Transport multiplication, identity, and inverse through these equivalences.
5. Transfer the group identities and multiplication naturality by injectivity.
6. Transfer commutativity and collect the operation-preservation equations.

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
