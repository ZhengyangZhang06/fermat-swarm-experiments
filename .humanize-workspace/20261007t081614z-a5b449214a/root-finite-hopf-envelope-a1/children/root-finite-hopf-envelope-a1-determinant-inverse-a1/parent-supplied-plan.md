# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.finite_hopf_envelope-a1.determinant_inverse-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/nodes/root-finite-hopf-envelope-a1-determinant-inverse-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.finite_hopf_envelope-a1`
- Child key: `determinant_inverse`
- Declaration: `Submission.p05_fhe_determinant_inverse_a5b449214a`
- Exact Lean type: `∀ {k : Type*} [Field k] {H : Type*} [CommRing H] [HopfAlgebra k H] (n : ℕ) (c : Matrix (Fin n) (Fin n) H) (hΔ : ∀ i j : Fin n, Coalgebra.comul (R := k) (c i j) = ∑ l : Fin n, TensorProduct.tmul k (c i l) (c l j)) (hε : ∀ i j : Fin n, Coalgebra.counit (R := k) (c i j) = if i = j then (1 : k) else 0), ∃ u : H, Matrix.det c * u = 1 ∧ Coalgebra.comul (R := k) u = TensorProduct.tmul k u u ∧ HopfAlgebra.antipode k u = Matrix.det c ∧ (∀ i j : Fin n, HopfAlgebra.antipode k (c i j) = u * Matrix.adjugate c i j)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
