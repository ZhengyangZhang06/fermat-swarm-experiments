<!-- theorem-id: fermat-p05/root.finite_hopf_envelope-a1.stable_subspace-a1 -->

## Theorem `Submission.p05_fhe_stable_subspace_a5b449214a`

Let k be a field and H a commutative Hopf k-algebra with comultiplication Δ. For every finite set F⊆H, there is a finite-dimensional k-subspace V⊆H containing 1 and F such that, for every x∈V, Δ(x) lies in span_k{a⊗b | a∈V, b∈H}. All tensor products are over k.

Node: `root.finite_hopf_envelope-a1.stable_subspace-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/5

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/231

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/270, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/271

## Lean problem

Declaration: `Submission.p05_fhe_stable_subspace_a5b449214a`

```lean
∀ {k : Type*} [Field k] {H : Type*} [CommRing H] [HopfAlgebra k H] (F : Finset H), ∃ V : Submodule k H, FiniteDimensional k V ∧ (1 : H) ∈ V ∧ (∀ x ∈ F, x ∈ V) ∧ (∀ x ∈ V, Coalgebra.comul (R := k) x ∈ Submodule.span k {t : TensorProduct k H H | ∃ a ∈ V, ∃ b : H, t = TensorProduct.tmul k a b})
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

- Parent DAG node: `root.finite_hopf_envelope-a1`
- Child DAG node: `root.finite_hopf_envelope-a1.stable_subspace-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Write ε for the counit, and put E=F∪{1}. Every element of an algebraic tensor product is a finite sum of pure tensors: these tensors generate the tensor product, and scalar coefficients can be absorbed into either factor. For each f∈E, choose an expression Δ(f)=Σ_r a_r⊗b_r.
2. Choose a finite basis w_1,…,w_m of the span of the b_r. Write b_r=Σ_i λ_ir w_i and put v_i=Σ_r λ_ir a_r. Tensor bilinearity gives Δ(f)=Σ_i v_i⊗w_i, with the w_i linearly independent in H. An empty family is permitted when this span is zero. Let V_f=span_k{v_i}; it is finite-dimensional.
3. Each coordinate functional on span_k{w_i} extends to a k-linear functional φ_j:H→k satisfying φ_j(w_i)=δ_ji. Indeed, extend the independent family to a basis of H and prescribe value zero on the additional basis vectors. Basis extension follows from the maximality principle: unions of chains of independent sets remain independent, and a maximal independent set spans because otherwise one can add a vector outside its span.
4. Coassociativity, with the usual tensor associativity identification, gives Σ_i Δ(v_i)⊗w_i=Σ_i v_i⊗Δ(w_i). Apply the linear map that sends a⊗b⊗c to φ_j(c)(a⊗b). The left side becomes Δ(v_j); the right side becomes Σ_i v_i⊗t_ij, where t_ij is the contraction of Δ(w_i) by φ_j in its second factor. Thus Δ(v_j) lies in span_k{a⊗b | a∈V_f, b∈H}. Linearity of Δ proves the same assertion for every element of V_f.
5. Apply the right counit identity to Δ(f)=Σ_i v_i⊗w_i. It gives f=Σ_i ε(w_i)v_i, so f∈V_f. This also covers the empty expression, when the identity gives f=0.
6. Let V be the sum of the V_f over the finite set E. The union of their finite generating families is finite and spans V, so V is finite-dimensional. Step 5 gives E⊆V, hence F⊆V and 1∈V.
7. Every x∈V is a finite sum of elements belonging to the V_f. By step 4, each corresponding comultiplication is a sum of pure tensors whose first factors lie in V_f⊆V. Linearity therefore places Δ(x) in span_k{a⊗b | a∈V, b∈H}. This proves every asserted property of V.

## Key steps

1. Express each comultiplication using linearly independent second factors.
2. Extend their coordinate functionals to the ambient vector space.
3. Contract coassociativity to obtain stability of the first-factor span.
4. Use right counitality to recover the original element in that span.
5. Sum the finitely many stable spans for F∪{1}.

## Reference use

### local-project

Queries:
- `antipode.*(mul|one)|def antipode|antipodeAlgHom|exists.*(subcoalgebra|Subcoalgebra)|FiniteDimensional|finite.*[Cc]oalgebra`
- `FiniteDimensional|finiteDimensional|exists.*[Ss]ubcoalgebra|exists.*[Ss]ubcomodule|finite.*[Ss]ubcoalgebra`
- `theorem (det_mul|det_map|mul_adjugate|adjugate_mul)|def adjugate|theorem.*det.*one|map_det`
- `exists_extension|extend|exists.*basis|finite_basis|finBasis`
- `finiteType_adjoin|finiteType.*fg|fg.*finiteType|fg_adjoin|adjoin.*finite`
- `p05_fhe_(stable_subspace|coefficient_matrix|determinant_inverse)_a5b449214a`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lake env lean /tmp/p05_fhe_typecheck_a5b449214a.lean`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lake env lean HeaderPolicyCheck.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/project/Definitions/Def_HopfAlgebra_HopfKer.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/RingTheory/Coalgebra/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/RingTheory/HopfAlgebra/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/RingTheory/HopfAlgebra/Convolution.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/LinearAlgebra/Basis/VectorSpace.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/LinearAlgebra/Matrix/Adjugate.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/RingTheory/FiniteType.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/nodes/root/decomposition-policy-validation/report.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/nodes/root/decomposition-policy-validation/challenge/HeaderPolicyCheck.lean`
- `/tmp/p05_fhe_typecheck_a5b449214a.lean`

The clean snapshots match project 2fdd42759f4ab17640ac773289b521dd69d4b26e and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. Coalgebra.Basic supplies finite tensor representations, coassociativity and counitality; the coalgebra-directory search found no finite-dimensional subcomodule existence theorem. Basis.VectorSpace supplies LinearMap.exists_extend. HopfAlgebra.Convolution already supplies antipodeAlgHom. The matrix files supply det_mul, RingHom.map_det, mul_adjugate and adjugate_mul; FiniteType supplies adjoin_of_finite. All three proposed types elaborated after import Submission under Lean 4.33.1. Kernel-checked diagnostic equalities confirmed ordinary multiplication for matrices constructed with Matrix.of. Audited infrastructure depends only on propext, Classical.choice and Quot.sound; all nine checked dependencies are clean and pinned. The existing private compiler copies were verified against policy digest 96fc18eb6b8cbdad1beec37ca318ab2cf08ac1dda8ebf7cbfe1d6d51abf32f96: only listed lines 10–11 are omitted, original hash 2e81f3c63685285e1af52e3dee0c135a8a7c8e9f37be7ad076712f55790c632c reversibly yields build hash d10948155ea0e92408d3ce320bdd5db3b7f00b622f4c9de9c98f040a414fa2f6, and the rerun Lean probe confirmed every omitted target absent. The proposed names have no current DAG or searched library collisions. These are decomposition diagnostics, not comparator acceptance of theorem proofs.


## Acceptance

The exact contract must pass the machine comparator and an independent reviewer's comparator rerun, without changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/329

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
