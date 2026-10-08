# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.hopf_tensor_equalizer-a1.finite_tensor_zero_witness-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/nodes/root-hopf-tensor-equalizer-a1-finite-tensor-zero-witness-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.hopf_tensor_equalizer-a1`
- Child key: `finite_tensor_zero_witness`
- Declaration: `Submission.p05_hte_finite_tensor_zero_witness_a5b449214a`
- Exact Lean type: `∀ {k : Type*} [CommRing k] {D : Type*} [CommRing D] [Algebra k D] {M : Type*} [AddCommGroup M] [Module D M] {P : Type*} [AddCommGroup P] [Module D P] (m : M) (p : P), (TensorProduct.tmul D m p : TensorProduct D M P) = 0 → ∃ S : Finset D, ∃ F : Finset M, m ∈ F ∧ ∀ (A : Subalgebra k D), (∀ d ∈ S, d ∈ A) → ∀ (N : Submodule A M), (∀ y ∈ F, y ∈ N) → ∀ hm : m ∈ N, (TensorProduct.tmul A (⟨m, hm⟩ : N) p : TensorProduct A N P) = 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
