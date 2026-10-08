# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.hopf_tensor_equalizer-a1.finite_stable_subspace-a1.coefficient_span_stability-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/nodes/root-hopf-tensor-equalizer-a1-finite-stable-subspace-a1-coefficient-s-a7f278c872/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.hopf_tensor_equalizer-a1.finite_stable_subspace-a1`
- Child key: `coefficient_span_stability`
- Declaration: `Submission.p05_hte_fss_coefficient_span_a5b449214a`
- Exact Lean type: `∀ {k : Type*} [Field k] {C : Type*} [AddCommGroup C] [Module k C] [Coalgebra k C] (f : C) (n : ℕ) (v w : Fin n → C) (ell : Fin n → C →ₗ[k] k) (hΔ : Coalgebra.comul (R := k) f = ∑ i : Fin n, TensorProduct.tmul k (v i) (w i)) (hdual : ∀ i j : Fin n, ell i (w j) = if i = j then (1 : k) else 0), let V : Submodule k C := Submodule.span k (Set.range v); FiniteDimensional k V ∧ f ∈ V ∧ ∀ x ∈ V, Coalgebra.comul (R := k) x ∈ Submodule.span k {t : TensorProduct k C C | ∃ a ∈ V, ∃ b : C, t = TensorProduct.tmul k a b}`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
