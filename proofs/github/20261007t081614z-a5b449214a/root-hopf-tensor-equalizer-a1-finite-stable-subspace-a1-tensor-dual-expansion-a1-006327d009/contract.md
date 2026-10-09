<!-- theorem-id: fermat-p05/root.hopf_tensor_equalizer-a1.finite_stable_subspace-a1.tensor_dual_expansion-a1 -->

## Theorem `Submission.p05_hte_fss_tensor_dual_expansion_a5b449214a`

Let k be a field and C an additive commutative group equipped with a k-module structure. For every z in C ⊗ₖ C, there exist a natural number n, families v,w : Fin n → C, and k-linear maps ell_i : C → k such that z = Σ_i v_i ⊗ w_i and ell_i(w_j) equals 1 when i = j and 0 otherwise.

Node: `root.hopf_tensor_equalizer-a1.finite_stable_subspace-a1.tensor_dual_expansion-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/5

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/264

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p05_hte_fss_tensor_dual_expansion_a5b449214a`

```lean
∀ {k : Type*} [Field k] {C : Type*} [AddCommGroup C] [Module k C] (z : TensorProduct k C C), ∃ (n : ℕ) (v w : Fin n → C) (ell : Fin n → C →ₗ[k] k), z = ∑ i : Fin n, TensorProduct.tmul k (v i) (w i) ∧ ∀ i j : Fin n, ell i (w j) = if i = j then (1 : k) else 0
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

- Parent DAG node: `root.hopf_tensor_equalizer-a1.finite_stable_subspace-a1`
- Child DAG node: `root.hopf_tensor_equalizer-a1.finite_stable_subspace-a1.tensor_dual_expansion-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Express z as a finite sum z = Σ_{r∈R} x_r ⊗ y_r. Such an expression exists by tensor-product induction: zero has an empty expression, a pure tensor has a one-term expression, and expressions for two tensors concatenate to give an expression for their sum.
2. Let W be the k-linear span of the finitely many vectors y_r. This subspace is finite-dimensional because those vectors span it. Choose a basis (b_i) indexed by Fin n for some natural number n, and let w_i be the image of b_i in C. For every r, the basis expansion of y_r gives scalars α_{r,i} with y_r = Σ_i α_{r,i} • w_i.
3. Define v_i = Σ_{r∈R} α_{r,i} • x_r. Bilinearity and the balancing relation for the tensor product give x_r ⊗ y_r = Σ_i (α_{r,i} • x_r) ⊗ w_i. Summing over r and interchanging the two finite sums gives z = Σ_i v_i ⊗ w_i.
4. The family (w_i) is linearly independent in C: any relation between its members is a relation between the basis vectors b_i in W, since the inclusion W → C is injective. Extend this independent family to a basis of C. Define ell_i to be the coordinate functional corresponding to w_i in that extended basis, so it is zero on every other basis vector. Uniqueness of basis expansions shows that coordinate extraction preserves addition and k-scalar multiplication, hence ell_i is k-linear. Its values on the original family are ell_i(w_j) = 1 if i = j and 0 otherwise.
5. If W is zero, every y_r is zero and therefore z = 0. Take n = 0 and the empty families v, w, and ell. The tensor sum is zero and the coordinate identities are vacuous. Thus the construction also covers the empty case and proves the entire assertion.

## Key steps

1. Express the tensor as a finite sum of pure tensors.
2. Choose a finite basis of the span of the second factors.
3. Expand those factors in the basis and collect the first coefficients.
4. Extend the independent right-factor family to a basis of C and take coordinate functionals.
5. Handle the zero span with empty families.

## Reference use

### local-project

Queries:
- `finiteDimensional|FiniteDimensional|coideal|exists.*subcoalgebra|exists.*[Ss]table`
- `exists.*(sum|linearIndependent)|sum.*exists|dualBasis|exists_extend|extend_apply|linearMapOf`
- `exists.*(dual|repr)|biorthogonal|dual.*exists`
- `finite_span|span.*[Ff]inite|[Ff]inite.*span`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/project/Definitions/Def_HopfAlgebra_HopfKer.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/RingTheory/Coalgebra/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/LinearAlgebra/TensorProduct/Finiteness.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/LinearAlgebra/Basis/VectorSpace.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p05/.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/local-references/29de40210f9954ae/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Defs.lean`

The snapshots match project revision 2fdd42759f4ab17640ac773289b521dd69d4b26e and mathlib revision db584cd6d46c92f209a44c0f1c829460d327499d, with no tracked modifications. Relevant infrastructure includes TensorProduct.exists_sum_tmul_eq, LinearMap.exists_extend, FiniteDimensional.span_of_finite, Coalgebra.coassoc_apply, and Coalgebra.lTensor_counit_comul. Their transitive axiom reports contain only propext, Classical.choice, and Quot.sound, or subsets thereof. The searches found no matching finite stable-subspace theorem or tensor expansion theorem supplying the required coordinate functionals.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/341

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
