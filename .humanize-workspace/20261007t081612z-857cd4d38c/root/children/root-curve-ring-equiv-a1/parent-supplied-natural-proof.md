# Parent-supplied natural-language proof

- Parent DAG node: `root`
- Child DAG node: `root.curve_ring_equiv-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Put e = k.symm, k* = Spec(k), and e* = Spec(e). Then e* ≫ k* and k* ≫ e* are identities. Define E.A = D.A and E.f = D.f ≫ k*. Keep D.C, D.lev, and all action morphisms unchanged. For every scheme W and t : W → Spec T, the condition Q ≫ E.f = t is equivalent to Q ≫ D.f = t ≫ e*: compose either equation with the inverse base isomorphism. This gives a bijection B_t on relative points which leaves their underlying morphisms unchanged and commutes with precomposition.
2. Transport D.L's multiplication, identity, and inverse through B_t. Injectivity of B_t proves associativity, both identity laws, inverse cancellation, and commutativity. Its precomposition compatibility proves multiplication naturality. The unchanged action maps are over Spec T after composing their original over-base equations with k*. Their identity and composition equations are unchanged. Their pointwise multiplication and addition equations follow by applying B_t and using the corresponding equations for D. This verifies every algebraic group and action field except act_trace.
3. The square with identity on the total scheme, structure maps E.f and D.f, and base map e* is a pullback. Indeed, a compatible pair R : W → D.A and t : W → Spec T satisfies R ≫ D.f = t ≫ e*; composing with k* gives R ≫ E.f = t. Its unique lift is R. Conversely, the latter equation implies the former by composing with e*. Thus E.f is a base change of D.f. Smoothness and properness follow from AlgebraicGeometry.smooth_isStableUnderBaseChange and AlgebraicGeometry.IsProper.isStableUnderBaseChange, respectively Mathlib/AlgebraicGeometry/Morphisms/Smooth.lean:117 and Morphisms/Proper.lean:72 at revision db584cd6d46c92f209a44c0f1c829460d327499d. The base homeomorphism identifies the fibre of E.f over t with the fibre of D.f over e*(t), without changing its total-space points or topology. Connectedness and topological Krull dimension two follow. The transported group law supplies the remaining bundle field.
4. For act_trace, fix an algebraically closed K, α : T → K, a finite K-module V₀, and a tangent parametrization τ satisfying its hypotheses. Put α_U = α ∘ e. The bijections B for Spec K and Spec(DualNumber K) commute with tangentZero and tangentScale and preserve group operations. Consequently the tangent restriction equation holds for a point if and only if it holds for its image. The parametrization B ∘ τ is injective and has exactly D's tangent vectors as range; its addition and scalar equations follow from those of τ. Since actions are intertwined, every linear map Φ representing an action through τ represents the same action through B ∘ τ. D.act_trace gives trace_K(Φ) = j for each integer j with m + star(m) = j. This is the desired equation for E.
5. The level immersion is unchanged, so it remains a closed immersion. A point and its image under B have the same underlying morphism; therefore their level-factorization conditions are equivalent. Under B, D.lev_sub, D.lev_one, and D.lev_stable give the corresponding fields for E. B preserves repeated addition by induction on the number of additions, proving lev_torsion from D.lev_torsion.
6. The same pullback argument as in step 3, with D.C and structure map D.lev ≫ D.f, shows that E.lev ≫ E.f is its base change along e*. Finiteness, flatness, and local finite presentation can also be seen directly: transport scalar coefficients across k and e in a finite generating family, in an exact tensor sequence, and in a finite algebra presentation. These operations preserve the corresponding properties on affine charts. The rank is N² by AlgebraicGeometry.Scheme.Hom.finrank_pullback_snd, Morphisms/FlatRank.lean:157 at the pinned revision, applied to this finite flat base change. For every algebraically closed K and α : T → K with (N : K) ≠ 0, B gives a bijection of the level-subgroup points with those of D at α_U. Composing the parametrization supplied by D.lev_fibre with B's inverse gives the required parametrization for E. Preservation of multiplication proves its addition equation. All fake elliptic curve fields are now verified.
7. Let i : D.A ≅ E.A be the identity isomorphism of their common total scheme. The square with i.inv and base e* is the pullback proved in step 3. The square with i.hom and base k* is also a pullback: a compatible pair R : W → E.A and t : W → Spec U satisfies R ≫ D.f ≫ k* = t ≫ k*, so cancellation of k* gives R ≫ D.f = t, and R is its unique lift.
8. For the square over e*, multiplication compatibility is the defining transport equation for B. For the square over k*, use the same equation at the base map t ≫ k* and cancel k* ≫ e*; it gives multiplication compatibility in the reverse direction. The unchanged actions commute with both identity morphisms. Level-factorization witnesses are unchanged in both directions. These are exactly the remaining fields of the two asserted IsPullbackVia predicates. Thus E and i satisfy the conclusion.

## Key steps

1. Relabel the base using k and identify relative points using its inverse.
2. Transport the group law and verify the unchanged action maps.
3. Prove the identity-total-space square is a pullback and verify geometric fields.
4. Transport tangent parametrizations to verify act_trace.
5. Verify all level fields, including finite flat rank and geometric parametrization.
6. Use the identity scheme isomorphism to establish both IsPullbackVia predicates.

## Reference use

### local-project

Queries:
- `rg --files -g AGENTS.md -g Submission.lean -g lakefile.lean -g lakefile.toml -g lean-toolchain -g '*decompos*' -g '*reserv*' -g '*dag*' -g '*state*' .humanize .`
- `qmap_comp_mk|quotEquiv_comp_mk|Pt.ext|def qmap|def quotEquiv|def ptX`
- `exists.*[Pp]ullback|[Pp]ullback.*exists|def.*baseChange|theorem.*baseChange|quotient.*[Ff]ullLevel|[Rr]igidification.*[Ll]ift`
- `FakeEllipticCurve.*(baseChange|quotient|rebase)|exists.*(quotient|rebase)`
- `isStableUnderBaseChange|finrank_pullback_snd|mkₐ`
- `structure AbelianSchemePropertyBundle`
- `p07_full_level_quotient_857cd4d38c|p07_curve_ring_equiv_857cd4d38c|p07_rigidification_reduction_857cd4d38c`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/nodes/root/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/project/Definitions/Def_CerednikDrinfeld_QMModuli.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/project/Definitions/Def_CerednikDrinfeld_QMFormalModuleOf.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/project/Definitions/Def_CerednikDrinfeld_QMFineModuli.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/project/Definitions/Def_CerednikDrinfeld_QMRigidification.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/project/Definitions/Def_CerednikDrinfeld_QMIsogeny.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/project/Definitions/Def_CerednikDrinfeld_RigidifiedPairClassModel.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/project/Definitions/Def_JacJ1Iface.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/project/Definitions/Def_AlgebraicGeometry_RelativeGroupLaw.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/mathlib/Mathlib/AlgebraicGeometry/Morphisms/Smooth.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/mathlib/Mathlib/AlgebraicGeometry/Morphisms/Proper.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/mathlib/Mathlib/AlgebraicGeometry/Morphisms/ClosedImmersion.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/mathlib/Mathlib/AlgebraicGeometry/Morphisms/FlatRank.lean`
- `/tmp/p07_decomposition_current_check.lean`
- `/tmp/p07_decomposition_current_type_and_axiom_check.log`
- `/tmp/p07_decomposition_current_unchanged_submission.log`

The project and mathlib snapshots are clean at the manifest revisions 73257f1e32d99b75813b037f28a5cf45a2db886d and db584cd6d46c92f209a44c0f1c829460d327499d. Ripgrep is unavailable; the recorded search expressions were searched with grep after the failed rg attempt. No reusable fake-elliptic-curve quotient or rebase construction matched the searches in Definitions and P2M. The model file already supplies qmap_comp_mk, quotEquiv_comp_mk, and Pt.ext'. The inspected definitions specify all curve, full-level, isogeny, and rigidification fields used below. The DAG contains only the root; the three identifiers and exact types below agree with the existing proposals, and no corresponding Lean declaration was found. All three types elaborate against Submission's pinned definition imports. Reflexivity checks verify that the inferred quotient O-algebra map is q composed with the original algebra map and that mkₐ has underlying ring homomorphism mk. The audited structures, quotient identities, extensionality lemma, and four cited geometric library results depend only on propext, Classical.choice, and Quot.sound. However, unchanged Submission.lean fails on unknown attribute references AlgebraicGeometry.Scheme.Hom.opensMapFinal, GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase, and RegularLocalRingQuotientAscent.dualNumberFst_apply. Thus the literal import Submission gate has not passed; these diagnostic checks are not comparator acceptance.
