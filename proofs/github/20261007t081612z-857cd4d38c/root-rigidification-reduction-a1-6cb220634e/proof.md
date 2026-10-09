# Parent-supplied natural-language proof

- Parent DAG node: `root`
- Child DAG node: `root.rigidification_reduction-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Put s = algebraMap O S π, J = (s), T = S/J, and q : S → T for the quotient. Its induced O-algebra map sends a to q(algebraMap O S a). Therefore π_T = algebraMap O T π = q(s) = 0, since s lies in J. Set U = T/(π_T), and let k₀ : T → U be the quotient. The map e : U → T sending [t] to t is well-defined because (π_T) is the zero ideal. It preserves all ring operations, and e ∘ k₀ = id_T and k₀ ∘ e = id_U. Thus k₀ is the underlying map of a ring isomorphism k : T ≃+* U with inverse e. Write k* and e* for the associated scheme morphisms.
2. Let λ : Onr/(π_Onr) → T be the residue map induced by ψ, and let λ' : Onr/(π_Onr) → U be induced by qₐ.comp ψ. On the class of a in Onr, λ' gives k₀(q(ψ(a))); therefore λ' = k₀ ∘ λ by surjectivity of the quotient map. The residue map q̄ : T → U induced by q likewise sends q(s₀) to k₀(q(s₀)) for every s₀ in S. Since q is surjective, q̄ = k₀. These are equalities of ring homomorphisms; proof fields in their quotient-map definitions do not affect them.
3. Apply the sibling theorem curve_ring_equiv to k and σ.Eb, and separately to k and σ.Ab. Obtain curves B,A over T and scheme isomorphisms i_b : σ.Eb.A ≅ B.A and i_A : σ.Ab.A ≅ A.A. Their forward maps satisfy IsPullbackVia over k₀, and their inverse maps satisfy IsPullbackVia over e. The inverse squares identify B-points over t with σ.Eb-points over t ≫ e*, by composition with i_b.inv; similarly for A. These are bijections, preserve multiplication and actions, and preserve level membership in both directions: the inverse pullback predicates give one implication and the forward predicates give the other after cancelling the isomorphisms and the inverse base maps.
4. Define the prospective rigidification by ρ.Eb = B, ρ.Ab = A, ρ.gb = i_b.inv ≫ σ.gb ≫ g, ρ.gA = i_A.inv ≫ σ.gA, ρ.d = σ.d, ρ.φ = i_b.inv ≫ σ.φ ≫ i_A.hom, and ρ.φ' = i_A.inv ≫ σ.φ' ≫ i_b.hom. These expressions have exactly the required sources and targets. The remaining steps verify each proof field of Rigidification.
5. Pullback squares compose: to lift a compatible pair into a composite square, first use the lower square's unique lift and then the upper square's unique lift; the two uniqueness statements also prove uniqueness for the composite. Apply this to the inverse square for i_b, σ.isPullback_Eb, and hg. Their base morphisms compose as e* ≫ k* ≫ q* = q*. Thus the composite is the required pullback square for ρ.gb. Multiplication compatibility follows by applying the three compatibility equations successively. The three action equations compose by associativity. For level factorization, take the witness through σ.Eb.lev supplied by the first predicate, then through V.lev supplied by the second, and finally through E.lev supplied by hg. This verifies all components of FakeEllipticCurve.IsPullbackVia q E B ρ.gb.
6. Compose the inverse square for i_A with σ.isPullback_Ab. Its base morphism is e* ≫ (λ')* = e* ≫ k* ≫ λ* = λ*, by step 2. Consequently this is the required pullback square for ρ.gA. Applying the two multiplication equations, composing the two action equations, and composing their level-factorization witnesses proves all remaining components of FakeEllipticCurve.IsPullbackVia λ A₀ A ρ.gA.
7. The inverse pullback equation gives i_b.inv ≫ σ.Eb.f = B.f ≫ e*, and the forward equation gives i_A.hom ≫ A.f = σ.Ab.f ≫ k*. Using σ.φ_over and e* ≫ k* = id yields ρ.φ ≫ A.f = B.f. Using the over-base equation for σ.φ' gives ρ.φ' ≫ B.f = A.f in the same way. Thus both isogeny maps are over Spec T, and the first equality supplies ρ.φ_over.
8. For a point Q of B over t, the image of ρ.φ(Q) under the point bijection for A is σ.φ applied to the image of Q under the point bijection for B. On underlying morphisms this is the cancellation i_A.hom ≫ i_A.inv = id. The corresponding statement for ρ.φ' follows by cancelling i_b.hom ≫ i_b.inv. Since the two point bijections preserve multiplication and are injective, σ's two multiplication-preservation equations imply those for ρ.φ and ρ.φ'. For action equivariance, substitute their definitions and use the action equations for i_b.inv, i_A.hom, i_A.inv, i_b.hom, and the two action equations for σ. Associativity gives precisely B.act(m) ≫ ρ.φ = ρ.φ ≫ A.act(m) and its reverse-map analogue.
9. Fix any membership witness for the scalar r^σ.d in Λ. Cancellation of i_A.hom ≫ i_A.inv gives ρ.φ ≫ ρ.φ' = i_b.inv ≫ (σ.φ ≫ σ.φ') ≫ i_b.hom. The old isogeny-pair equation replaces the middle composite by σ.Eb's action of that scalar. Action compatibility and i_b.inv ≫ i_b.hom = id turn the result into B's action of the same scalar. Cancelling i_b.hom ≫ i_b.inv in the other order proves ρ.φ' ≫ ρ.φ equals A's scalar action. Since ρ.d = σ.d by definition, these are the exact degree conditions in IsIsogenyPair. Together with steps 7 and 8, they establish ρ.isIsogenyPair.
10. Suppose a B-point factors through B.lev. The level equivalence of step 3 sends it to a point factoring through σ.Eb.lev. Apply σ.preservesLevel to obtain a factorization through σ.Ab.lev, then send it forward through i_A.hom to obtain a factorization through A.lev. The resulting point is its image under ρ.φ by definition. Hence ρ.preservesLevel holds. Steps 5–10 verify every proof field, so ρ is a rigidification with ρ.d = σ.d.
11. To prove the asserted rigidification pullback relation, take ub = i_b.hom and uA = i_A.hom. Its residue map is k₀ by step 2, so the two curve IsPullbackVia conditions are exactly the forward conditions supplied in step 3. The equation ub ≫ ρ.gb = σ.gb ≫ g follows by cancelling i_b.hom ≫ i_b.inv. Similarly uA ≫ ρ.gA = σ.gA. The degree equation σ.d = ρ.d is reflexive. Finally, ub ≫ ρ.φ = σ.φ ≫ i_A.hom = σ.φ ≫ uA, again by cancellation. These are all conjuncts in Rigidification.IsPullbackVia qₐ g hg ρ σ. Thus ρ is the required witness.

## Key steps

1. Show the second quotient is quotient by zero and construct its canonical ring isomorphism.
2. Identify both induced residue maps by evaluation on quotient representatives.
3. Transport the two special-fibre curves using curve_ring_equiv.
4. Define the lifted rigidification by conjugating its isogeny maps.
5. Compose pullback squares and their multiplication, action, and level compatibilities.
6. Verify the over-base, isogeny-pair, and level-preservation fields.
7. Use the forward transport isomorphisms as witnesses of the exact rigidification pullback relation.

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
