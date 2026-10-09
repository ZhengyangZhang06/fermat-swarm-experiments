<!-- theorem-id: fermat-p05/root.hopf_tensor_equalizer-a1.finite_stable_subspace-a1.coefficient_span_stability-a1 -->

## Theorem `Submission.p05_hte_fss_coefficient_span_a5b449214a`

Let k be a field and C an additive commutative group with a k-module structure and a k-coalgebra structure. Let f ∈ C, n ∈ ℕ, v,w : Fin n → C, and ell_i : C →ₗ[k] k. Assume Δ(f) = Σ_i v_i ⊗ w_i and ell_i(w_j) = 1 if i = j and 0 otherwise. Set V = spanₖ{v_i | i ∈ Fin n}. Then V is finite-dimensional, f belongs to V, and for every x ∈ V, Δ(x) belongs to spanₖ{a ⊗ b | a ∈ V, b ∈ C}.

Node: `root.hopf_tensor_equalizer-a1.finite_stable_subspace-a1.coefficient_span_stability-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/5

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/264

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p05_hte_fss_coefficient_span_a5b449214a`

```lean
∀ {k : Type*} [Field k] {C : Type*} [AddCommGroup C] [Module k C] [Coalgebra k C] (f : C) (n : ℕ) (v w : Fin n → C) (ell : Fin n → C →ₗ[k] k) (hΔ : Coalgebra.comul (R := k) f = ∑ i : Fin n, TensorProduct.tmul k (v i) (w i)) (hdual : ∀ i j : Fin n, ell i (w j) = if i = j then (1 : k) else 0), let V : Submodule k C := Submodule.span k (Set.range v); FiniteDimensional k V ∧ f ∈ V ∧ ∀ x ∈ V, Coalgebra.comul (R := k) x ∈ Submodule.span k {t : TensorProduct k C C | ∃ a ∈ V, ∃ b : C, t = TensorProduct.tmul k a b}
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
- Child DAG node: `root.hopf_tensor_equalizer-a1.finite_stable_subspace-a1.coefficient_span_stability-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Write Δ for the coproduct and ε for the counit. Define V = spanₖ{v_i} and S = spanₖ{a ⊗ b | a ∈ V, b ∈ C}. The range of v is finite, so V is finite-dimensional. Each v_i belongs to V by the defining property of a linear span.
2. For each i, define the k-linear contraction R_i : C ⊗ₖ C → C by R_i(a ⊗ b) = ell_i(b) • a. Define T_i : (C ⊗ₖ C) ⊗ₖ C → C ⊗ₖ C by T_i(u ⊗ c) = ell_i(c) • u. Both maps exist by the tensor-product universal property, because their displayed formulas are bilinear. Let α be the tensor associator. For any a ∈ C and t ∈ C ⊗ₖ C, one has T_i(α⁻¹(a ⊗ t)) = a ⊗ R_i(t). Indeed, for t = b ⊗ c both sides equal ell_i(c) • (a ⊗ b), using the balancing relation; the identity then holds for all t by linearity and finite pure-tensor expansion.
3. Expand both sides of coassociativity at f using the assumed formula for Δ(f), and express them in (C ⊗ₖ C) ⊗ₖ C. This gives Σ_j Δ(v_j) ⊗ w_j = Σ_j α⁻¹(v_j ⊗ Δ(w_j)). Apply T_i. On the left the result is Σ_j ell_i(w_j) • Δ(v_j) = Δ(v_i), by the assumed coordinate identities. On the right, step 2 gives Σ_j v_j ⊗ R_i(Δ(w_j)). Consequently Δ(v_i) = Σ_j v_j ⊗ R_i(Δ(w_j)).
4. Every tensor on the right of this last equality is a generator of S, since v_j ∈ V and R_i(Δ(w_j)) ∈ C. Closure under finite sums therefore gives Δ(v_i) ∈ S for every i. The inverse image U = {x ∈ C | Δ(x) ∈ S} is a k-subspace: Δ is linear and S is a subspace. It contains all v_i, hence contains their span V. Thus every x ∈ V satisfies Δ(x) ∈ S, proving the required stability.
5. Apply the k-linear map a ⊗ b ↦ ε(b) • a to Δ(f) = Σ_i v_i ⊗ w_i. The right counit identity makes its value on Δ(f) equal to f. Therefore f = Σ_i ε(w_i) • v_i. Every summand belongs to V, so f ∈ V.
6. All these arguments permit n = 0. Explicitly, the empty expansion says Δ(f) = 0, and step 5 gives f = 0. The span V is then the zero subspace, which is finite-dimensional and stable because Δ(0) = 0. This completes the proof in every case.

## Key steps

1. Define the coefficient span V and its associated tensor span S; establish finite-dimensionality.
2. Construct contraction maps from the given coordinate functionals and check compatibility with the associator.
3. Contract coassociativity to obtain an explicit coproduct formula for each v_i.
4. Place those coproducts in S and extend stability to V using the linear inverse image of S.
5. Apply the right counit identity to express f as a linear combination of the v_i.
6. Verify that the same conclusions hold for an empty expansion.

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

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/337

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
