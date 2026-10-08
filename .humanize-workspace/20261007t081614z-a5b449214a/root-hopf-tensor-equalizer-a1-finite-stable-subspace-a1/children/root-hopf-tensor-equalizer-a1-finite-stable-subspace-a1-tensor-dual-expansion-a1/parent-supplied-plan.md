# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.hopf_tensor_equalizer-a1.finite_stable_subspace-a1.tensor_dual_expansion-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/nodes/root-hopf-tensor-equalizer-a1-finite-stable-subspace-a1-tensor-dual-expansion-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.hopf_tensor_equalizer-a1.finite_stable_subspace-a1`
- Child key: `tensor_dual_expansion`
- Declaration: `Submission.p05_hte_fss_tensor_dual_expansion_a5b449214a`
- Exact Lean type: `∀ {k : Type*} [Field k] {C : Type*} [AddCommGroup C] [Module k C] (z : TensorProduct k C C), ∃ (n : ℕ) (v w : Fin n → C) (ell : Fin n → C →ₗ[k] k), z = ∑ i : Fin n, TensorProduct.tmul k (v i) (w i) ∧ ∀ i j : Fin n, ell i (w j) = if i = j then (1 : k) else 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
