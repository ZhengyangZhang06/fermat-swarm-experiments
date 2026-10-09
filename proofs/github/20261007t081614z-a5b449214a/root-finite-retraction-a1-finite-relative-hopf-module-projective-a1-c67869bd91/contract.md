<!-- theorem-id: fermat-p05/root.finite_retraction-a1.finite_relative_hopf_module_projective-a1 -->

## Theorem `Submission.p05_fr_finite_relative_hopf_module_projective_a5b449214a`

Let k be a field. Let A and H be commutative Hopf k-algebras, with A finitely generated as a k-algebra, and let ι:A→H be an injective k-bialgebra homomorphism. Let M be an additive commutative group with compatible k-module and A-module structures, meaning (c·a)·m=c·(a·m), and suppose M is finitely generated over A. Let μ:M→M⊗_k H be k-linear. Assume (μ⊗id)μ=(id⊗Δ_H)μ after the canonical associator, and (id⊗ε_H)μ=id after the canonical identification M⊗k≅M. Assume also μ(a·m)=Σ a_1·m_0⊗ι(a_2)m_1, where Δ_A(a)=Σ a_1⊗a_2 and μ(m)=Σ m_0⊗m_1. This identity is independent of the chosen finite tensor representations; the Lean type uses Coalgebra.Repr.arbitrary for Δ_A(a). Then M is projective over A.

Node: `root.finite_retraction-a1.finite_relative_hopf_module_projective-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/5

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/232

Prerequisites: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/252, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/253

Decomposition children: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/281, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/282, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/283, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/284

## Lean problem

Declaration: `Submission.p05_fr_finite_relative_hopf_module_projective_a5b449214a`

```lean
∀ {k : Type*} [Field k] {A : Type*} [CommRing A] [HopfAlgebra k A] [Algebra.FiniteType k A] {H : Type*} [CommRing H] [HopfAlgebra k H] (ι : BialgHom k A H) (_hι : Function.Injective ι) {M : Type*} [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M] [Module.Finite A M] (μ : M →ₗ[k] TensorProduct k M H) (_hcoassoc : ∀ m : M, TensorProduct.assoc k M H H ((TensorProduct.map μ (LinearMap.id : H →ₗ[k] H)) (μ m)) = (TensorProduct.map (LinearMap.id : M →ₗ[k] M) (Coalgebra.comul (R := k))) (μ m)) (_hcounit : ∀ m : M, TensorProduct.rid k M ((TensorProduct.map (LinearMap.id : M →ₗ[k] M) (Coalgebra.counit (R := k))) (μ m)) = m) (_hcompat : ∀ (a : A) (m : M), let d := Coalgebra.Repr.arbitrary k a; μ (a • m) = ∑ i ∈ d.index, TensorProduct.map ((Algebra.lsmul k k M) (d.left i)) (LinearMap.mulLeft k (ι (d.right i))) (μ m)), Module.Projective A M
```

### Frozen project context

`Fermat/Thm_HopfAlgebra_hopfKer_eq_of_surjective_of_ker_eq_span.lean` at `2fdd42759f4ab17640ac773289b521dd69d4b26e` supplies the original imports, definitions and root contract. Child hypotheses are stated above; prerequisite declarations are linked in their issues.

```lean
/-
Copyright 2026 Anthropic, PBC. Licensed under Apache-2.0; see LICENSE.
Source: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_HopfAlgebra_hopfKer_eq_of_surjective_of_ker_eq_span.lean
Modified: replaced the proof with sorry and removed P2M proof imports.
Requires the upstream Definitions modules and their dependencies.
-/

import Mathlib
import Definitions.Def_HopfAlgebra_HopfKer
attribute [-instance] HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra
attribute [-simp] HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul

universe u v w

open scoped TensorProduct

theorem HopfAlgebra.hopfKer_eq_of_surjective_of_ker_eq_span
    {k : Type u} [Field k] {H : Type v} [CommRing H] [HopfAlgebra k H] [Algebra.FiniteType k H]
    (K : Subalgebra k H)
    (hΔ : ∀ x ∈ K, Coalgebra.comul (R := k) x ∈
      Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K, ∃ b ∈ K, t = a ⊗ₜ[k] b})
    (hS : ∀ x ∈ K, HopfAlgebra.antipode k x ∈ K)
    {B : Type w} [CommRing B] [Bialgebra k B] (q : H →ₐc[k] B) (hq : Function.Surjective q)
    (hker : RingHom.ker (q : H →+* B) =
      Ideal.span {x : H | x ∈ K ∧ Coalgebra.counit (R := k) x = 0}) :
    HopfAlgebra.hopfKer q = K := by
  sorry
```

## Natural-language proof

Reviewed mathematical argument; formal verification state: `proved`.

# Parent-supplied natural-language proof

- Parent DAG node: `root.finite_retraction-a1`
- Child DAG node: `root.finite_retraction-a1.finite_relative_hopf_module_projective-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. All tensor products in this proof are over k unless another base is displayed. Write Δ_A(a)=Σa_1⊗a_2 and μ(m)=Σm_0⊗m_1. The expression Σa_1·m_0⊗ι(a_2)m_1 is independent of these representations: the action of A on M, the map ι, and multiplication in H are k-bilinear, so the expression is obtained by applying a linear map to Δ_A(a)⊗μ(m). Thus the precise compatibility hypothesis using Coalgebra.Repr.arbitrary gives the displayed Sweedler identity.
2. A is Noetherian, and M is finitely presented. Here are the finiteness details. If every ideal of a commutative ring R is finitely generated, every submodule of R^n is finitely generated: induct on n, use the induction hypothesis on the kernel of the last-coordinate projection, and lift finitely many generators of its image ideal. To prove the corresponding ideal property for R[t], take a nonzero ideal I. The ideal generated by leading coefficients of its nonzero elements is generated by finitely many original leading coefficients: finite ideal generators involve only finitely many such coefficients. Choose corresponding f_1,…,f_s∈I and let d be their maximum degree. The elements of I of degree less than d form a submodule of R^d and have finitely many generators. If f∈I has degree at least d, express its leading coefficient using those of the f_i and subtract the corresponding multiples t^(deg(f)−deg(f_i))f_i. The degree strictly decreases. Induction generates I by the chosen f_i and the low-degree generators. The zero ideal and d=0 cause no exception. Fields have the ideal property; iteration gives it for polynomial rings in finitely many variables, and it descends to quotients. Finite generation of A as a k-algebra therefore gives the property for A. A surjection A^n→M now has a finitely generated kernel, yielding a finite presentation A^p→A^n→M→0.
3. For any finite presentation R^p→R^n→L→0 over a commutative ring R, let P be its relation matrix. For 0≤r<n define F_r(L) using this presentation to be the ideal generated by its (n−r)-minors, using injective row and column selections. Set F_r(L)=R for r≥n. Empty determinants are 1 and an unavailable positive minor size contributes no generators.
4. With the generating list of L fixed, any two finite relation-generating lists give the same ideals. Indeed, every column of one matrix is a linear combination of columns of the other. Multilinearly expand each selected determinant. Terms with repeated columns vanish, and the remaining terms are coefficients times minors of the other matrix, up to signs. This proves one inclusion; reversing the lists proves the other. The same expansion for rows proves invariance under invertible row operations, and the column argument proves invariance under invertible column operations. Cofactor expansion also shows that every minor of size s+1 belongs to the ideal generated by the s-minors; for s=0 this says it belongs to the unit ideal.
5. Adjoin a redundant generator y=Σ_i a_i m_i to a generating list of length n. The old relations, together with the relation y−Σ_i a_i m_i, generate the new kernel: subtract the last coordinate times this defining relation from any relation, leaving an old relation. An invertible row operation makes the resulting matrix diag(P,1). For r<n, its minors of size n+1−r containing both the added row and column are, up to sign, the old (n−r)-minors. Those containing neither are larger old minors and belong to their ideal by step 4; those containing exactly one vanish. For r=n the new 1-minors include 1, and for r>n both ideals are R. Thus adjoining a redundant generator preserves F_r. Given two finite generating lists, adjoin each list to the other; the resulting lists differ only by a permutation. Step 4 compares their relation lists. This proves presentation independence and invariance under module isomorphisms.
6. If φ:R→R' is a ring map, the entrywise image φ(P) presents R'⊗_R L. To see this without assuming flatness, maps from its presented cokernel into an R'-module Y correspond to lists of elements of Y satisfying the image relations; these are exactly R-linear maps L→Y, and hence R'-linear maps R'⊗_R L→Y. The resulting universal maps identify the two modules. Determinants commute with φ by the permutation formula, so F_r(R'⊗_R L)=F_r(L)R'.
7. If θ:R→R is a ring automorphism and T:L→L is an additive bijection with T(ax)=θ(a)T(x), the elements T(m_i) generate L. A coefficient tuple b is a relation among them exactly when θ⁻¹(b) is a relation among the m_i, by applying T⁻¹. Hence θ(P) is a relation matrix for these new generators. Presentation independence and the determinant formula give θ(F_r(L))=F_r(L).
8. The antipodes of A and H are algebra homomorphisms. For completeness, in either commutative Hopf algebra C put f(a⊗b)=ab, g(a⊗b)=S(ab), and h(a⊗b)=S(a)S(b). Convolution on linear maps C⊗C→C is associative by coassociativity, with unit e(a⊗b)=ε(a)ε(b)1. Multiplicativity of Δ and ε and the antipode identity for ab give g*f=e. Commutativity and the antipode identities for a and b give f*h=e. Thus g=g*(f*h)=(g*f)*h=h. The antipode identity at 1 gives S(1)=1, and S is k-linear. This proves the asserted algebra-homomorphism property.
9. Put R'=A⊗H and W=M⊗H. Give W the R'-action (a⊗h)(m⊗g)=a·m⊗hg. Bilinearity and the compatibility of the k- and A-actions make this well-defined; associativity and the unit law follow on pure tensors and extend by linearity. The maps (a⊗h)⊗_A m↦a·m⊗h and m⊗h↦(1⊗h)⊗_A m are balanced inverse R'-linear maps. Therefore W≅R'⊗_A M and step 6 gives F_r(W)=F_r(M)R'.
10. Define θ:R'→R' by θ(a⊗h)=Σa_1⊗ι(a_2)h. Define θ⁻¹(a⊗h)=Σa_1⊗ι(S_A(a_2))h. These formulas are bilinear, preserve multiplication and 1 by step 8 and the bialgebra identities, and preserve k-scalars. Coassociativity expresses θθ⁻¹(a⊗h) as Σa_1⊗ι(a_2S_A(a_3))h and θ⁻¹θ(a⊗h) as Σa_1⊗ι(S_A(a_2)a_3)h. The antipode and counit identities reduce both to a⊗h. Thus θ is a k-algebra automorphism.
11. Define T:W→W by T(m⊗h)=Σm_0⊗m_1h, and U(m⊗h)=Σm_0⊗S_H(m_1)h. Bilinearity defines k-linear maps. Coassociativity of μ expresses TU(m⊗h) as Σm_0⊗m_1S_H(m_2)h and UT(m⊗h) as Σm_0⊗S_H(m_1)m_2h. The antipode identities followed by counitality of μ reduce each expression to m⊗h. Hence T is an additive bijection. The compatibility hypothesis gives T((a⊗h)(m⊗g))=θ(a⊗h)T(m⊗g); expanding sums proves T(rw)=θ(r)T(w) for arbitrary r,w.
12. Fix r≥0 and set J=F_r(M). By steps 7, 9, and 11, θ(JR')=JR'. Identify J⊗H with its image in A⊗H. This inclusion is injective: extend a k-basis of J to a basis of A to obtain a linear retraction, and tensor that retraction with id_H. Its image is an ideal, because multiplication of a pure tensor j⊗h by a⊗g gives aj⊗gh with aj∈J. It contains j⊗1, while j⊗h=(j⊗1)(1⊗h), so this image equals JR'. For j∈J, consequently θ(j⊗1)=(id_A⊗ι)(Δ_A(j)) belongs to J⊗H.
13. Injectivity of ι supplies a k-linear retraction λ:H→A: prescribe λ on a basis of the image of ι as its inverse and extend that basis to H. Applying id_A⊗λ to the containment in step 12 sends J⊗H into J⊗A and sends (id_A⊗ι)(Δ_A(j)) to Δ_A(j). Thus Δ_A(j) lies in the span of tensors with first factor in J. Apply p05_fr_coideal_ideal_dichotomy_a5b449214a to A and J. All its hypotheses have now been verified, so every F_r(M) is zero or A.
14. Return to the finite presentation from step 2, with relation matrix P having n rows and p columns and quotient map π. For 0≤d≤n, the ideal generated by the d-minors is F_(n−d)(M), including d=0, when both are A. For d>n there is no injective row selection and the ideal is zero. Thus every determinantal ideal of P is zero or A. The map π is surjective and ker(π)=im(P) by construction. Apply p05_fr_projective_of_trivial_minors_a5b449214a with R=A and this presentation. Its conclusion is Module.Projective A M, as required.

## Key steps

1. Interpret the precise compatibility formula intrinsically using bilinearity.
2. Prove A is Noetherian and choose a finite presentation of M.
3. Establish presentation independence of determinantal presentation ideals.
4. Establish their base-change and semilinear invariance.
5. Identify M⊗H with scalar extension to A⊗H.
6. Construct the inverse coaction twists θ and T and verify T is θ-semilinear.
7. Deduce that every presentation ideal is a coideal by tensor injectivity and a linear retraction of ι.
8. Apply the coideal-ideal dichotomy to make all presentation ideals zero or A.
9. Apply the determinantal projectivity criterion to the chosen presentation.

## Reference use

### local-project

Queries:
- `class.*[Cc]omodule|structure.*[Cc]omodule|fittingIdeal|fitting_ideal|Fitting ideal`
- `Fitting|fittingIdeal|fitting_ideal|class.*[Cc]omodule|structure.*[Cc]omodule|antipode_mul|antipodeAlgHom`
- `isNoetherianRing_of_fg|finitePresentation_of_finite|exists.*[Ss]ection|exists.*[Ll]eftInverse|projective.*iff`
- `def mulVecLin|mulVecLin_apply|def lsmul|def mulLeft|submatrix`
- `p05_fr_coideal_ideal_dichotomy_a5b449214a|p05_fr_projective_of_trivial_minors_a5b449214a|p05_fr_finite_relative_hopf_module_projective_a5b449214a`
- `rg --files -uu /mnt/data/zhengyang-workspace/fermat-swarm-projects -g dag.json`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lake env lean CheckTypes.lean > ../literal-types.log 2>&1`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lake env lean CheckInstances.lean > ../instances-axioms.log 2>&1`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lake env lean HeaderPolicyCheck.lean > ../header-absence.log 2>&1`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/nodes/root-finite-retraction-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/project/Definitions/Def_HopfAlgebra_HopfKer.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/RingTheory/HopfAlgebra/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/RingTheory/HopfAlgebra/Convolution.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/RingTheory/Coalgebra/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/RingTheory/Adjoin/FG.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/Algebra/Module/FinitePresentation.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/Algebra/Module/Projective.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/LinearAlgebra/Matrix/ToLin.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/Algebra/Algebra/Tower.lean`
- `/runtime/operator-header-policy-v1/policy.json`
- `/tmp/p05-fr-decomp-mgjv880w/challenge/CheckTypes.lean`
- `/tmp/p05-fr-decomp-mgjv880w/challenge/CheckInstances.lean`
- `/tmp/p05-fr-decomp-mgjv880w/header-input-binding.json`
- `/tmp/p05-fr-decomp-mgjv880w/header-absence.log`
- `/tmp/p05-fr-decomp-mgjv880w/instances-axioms.log`
- `/tmp/p05-fr-decomp-mgjv880w/report.json`

The project and mathlib snapshots are clean at 2fdd42759f4ab17640ac773289b521dd69d4b26e and db584cd6d46c92f209a44c0f1c829460d327499d; all nine dependency checkouts match their clean pins. The snapshot supplies antipode multiplicativity, finite-presentation infrastructure, matrix presentation maps, and projective lifting. No Fitting-ideal or general comodule declaration matched the targeted search. The three proposed names have no active-DAG collision. All three literal types elaborate warning-clean after import Submission. Anonymous proofs verify the tensor action and matrix-vector semantics; nine inspected infrastructure axiom closures contain only propext, Classical.choice, and Quot.sound. Disposable compiler copies follow policy SHA256 96fc18eb6b8cbdad1beec37ca318ab2cf08ac1dda8ebf7cbfe1d6d51abf32f96, omitting exactly lines 10–11; Lean confirms all 13 targets absent. Reversible original/build hashes are retained in header-input-binding.json. Protected sources and handoffs were not edited. These are interface diagnostics; theorem acceptance still requires the configured exact-contract comparator and independent review.


## Acceptance

The exact contract must pass the machine comparator and an independent reviewer's comparator rerun, without changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: Pending

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
