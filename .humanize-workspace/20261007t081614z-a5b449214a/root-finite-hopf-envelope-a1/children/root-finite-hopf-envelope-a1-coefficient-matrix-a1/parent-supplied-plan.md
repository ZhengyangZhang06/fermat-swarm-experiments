# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.finite_hopf_envelope-a1.coefficient_matrix-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/nodes/root-finite-hopf-envelope-a1-coefficient-matrix-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.finite_hopf_envelope-a1`
- Child key: `coefficient_matrix`
- Declaration: `Submission.p05_fhe_coefficient_matrix_a5b449214a`
- Exact Lean type: `∀ {k : Type*} [Field k] {H : Type*} [CommRing H] [HopfAlgebra k H] (V : Submodule k H) [FiniteDimensional k V] (hV : ∀ x ∈ V, Coalgebra.comul (R := k) x ∈ Submodule.span k {t : TensorProduct k H H | ∃ a ∈ V, ∃ b : H, t = TensorProduct.tmul k a b}), ∃ (n : ℕ) (c : Matrix (Fin n) (Fin n) H), (∀ x ∈ V, x ∈ Submodule.span k (Set.range (fun p : Fin n × Fin n => c p.1 p.2))) ∧ (∀ i j : Fin n, Coalgebra.comul (R := k) (c i j) = ∑ l : Fin n, TensorProduct.tmul k (c i l) (c l j)) ∧ (∀ i j : Fin n, Coalgebra.counit (R := k) (c i j) = if i = j then (1 : k) else 0)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
