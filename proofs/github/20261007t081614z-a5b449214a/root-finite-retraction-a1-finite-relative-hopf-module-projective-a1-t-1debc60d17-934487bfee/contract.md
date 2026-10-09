<!-- theorem-id: fermat-p05/root.finite_retraction-a1.finite_relative_hopf_module_projective-a1.tensor_ideal_descent-a1 -->

## Theorem `Submission.p05_fr_rhm_tensor_ideal_descent_a5b449214a`

Let k be a field, A and H commutative k-algebras, f:A→H an injective k-linear map, J an ideal of A, and t∈A⊗_k A. Extend J to A⊗_k H along the algebra homomorphism a↦a⊗1. If (id_A⊗f)(t) belongs to this extended ideal, then t belongs to the k-linear span of all a⊗b with a∈J and b∈A.

Node: `root.finite_retraction-a1.finite_relative_hopf_module_projective-a1.tensor_ideal_descent-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/5

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/254

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p05_fr_rhm_tensor_ideal_descent_a5b449214a`

```lean
∀ {k : Type*} [Field k] {A : Type*} [CommRing A] [Algebra k A] {H : Type*} [CommRing H] [Algebra k H] (f : A →ₗ[k] H) (_hf : Function.Injective f) (J : Ideal A) (t : TensorProduct k A A) (_ht : TensorProduct.map (LinearMap.id : A →ₗ[k] A) f t ∈ Ideal.map (Algebra.TensorProduct.includeLeft : A →ₐ[k] TensorProduct k A H).toRingHom J), t ∈ Submodule.span k {z : TensorProduct k A A | ∃ a ∈ J, ∃ b : A, z = TensorProduct.tmul k a b}
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

- Parent DAG node: `root.finite_retraction-a1.finite_relative_hopf_module_projective-a1`
- Child DAG node: `root.finite_retraction-a1.finite_relative_hopf_module_projective-a1.tensor_ideal_descent-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Let E_H be the k-linear span in A⊗_k H of tensors j⊗h with j∈J. It is an ideal of A⊗_k H: multiplying a generating tensor j⊗h by a pure tensor a⊗g gives aj⊗gh, whose first factor lies in J. Distributing over finite sums of pure tensors and over the linear combinations defining the span proves closure under multiplication by every element. Its additive closure and zero follow from its definition as a submodule.
2. The ideal E_H contains every j⊗1, so it contains the extension of J along a↦a⊗1. Conversely, each j⊗h=(j⊗1)(1⊗h) belongs to that extended ideal. An ideal in a k-algebra is closed under k-scalar multiplication because scalar multiplication is multiplication by the image of the scalar. Therefore the extended ideal contains their k-linear span E_H. The two are equal, so the hypothesis places (id_A⊗f)(t) in E_H.
3. Choose a k-basis of A. Injectivity of f makes its image a linearly independent subset of H. Extend that image to a basis of H, define λ on the image basis by λ(f(a_i))=a_i and on the added basis vectors by zero, and extend k-linearly. This constructs λ:H→A with λ∘f=id_A.
4. Put E_A=span_k{j⊗a:j∈J,a∈A}. The linear map id_A⊗λ carries E_H into E_A, because it sends each generating j⊗h to j⊗λ(h). Its composite with id_A⊗f is the identity on A⊗_k A: check this on a⊗b using λ(f(b))=b, then extend linearly. Applying id_A⊗λ to the membership from step 2 therefore gives t∈E_A, exactly the conclusion.

## Key steps

1. Identify the extended ideal with the span of tensors whose first factor lies in J.
2. Construct a linear retraction of the injective map f by extending a basis.
3. Apply id⊗λ to descend membership to the corresponding span in A⊗A.

## Reference use

### local-project

Queries:
- `Fitting|fittingIdeal|fitting_ideal|FinitePresentation|antipode_mul|antipode.*AlgHom`
- `fitting`
- `antipode.*(mul|AlgHom)|map_mul.*antipode|antipodeAlgHom`
- `injective.*exists|exists.*leftInverse|leftInverse`
- `det.*map|map.*det`
- `isNoetherianRing`
- `def hopfKer|hopfKer|equalizer`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/project/Definitions/Def_HopfAlgebra_HopfKer.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/Algebra/Module/FinitePresentation.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/LinearAlgebra/TensorProduct/RightExactness.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/RingTheory/TensorProduct/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/RingTheory/HopfAlgebra/Convolution.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/LinearAlgebra/Basis/VectorSpace.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean`

The snapshots are clean at project revision 2fdd42759f4ab17640ac773289b521dd69d4b26e and mathlib revision db584cd6d46c92f209a44c0f1c829460d327499d; all nine dependency checkouts match their clean pins. Relevant infrastructure includes finite presentations, tensor right exactness, tensor algebra operations, antipode identities, linear retractions, and determinants commuting with ring maps. The case-insensitive Fitting search in mathlib/RingTheory and project/Definitions found only unrelated Artinian-module decomposition results, not a Fitting-ideal API. All four proposed types elaborate after import Submission; anonymous checks verify tensor multiplication, scalar action, inclusion, and matrix-vector semantics. Nine inspected infrastructure axiom closures contain only propext, Classical.choice, and Quot.sound. No proposed name collides with the scanned DAG reservations or Submission. Policy-compliant diagnostics are recorded in /tmp/p05-rhm-decomp-hlprok3k: header-input-binding.json binds policy digest 96fc18eb6b8cbdad1beec37ca318ab2cf08ac1dda8ebf7cbfe1d6d51abf32f96, exactly omitted lines 10–11, and reversible original/build hashes; Absence.lean.log confirms all 13 targets absent under the frozen imports. Protected files remain unchanged. These are interface diagnostics, not comparator acceptance of any theorem.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/366

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
