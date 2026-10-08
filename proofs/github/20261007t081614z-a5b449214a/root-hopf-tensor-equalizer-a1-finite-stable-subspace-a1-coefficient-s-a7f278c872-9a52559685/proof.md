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
