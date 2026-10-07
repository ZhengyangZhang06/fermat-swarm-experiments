# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.local_norm_order-a1.dvr_determinant_length-a1.dvr_matrix_diagonalization-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-local-norm-order-a1-dvr-determinant-length-a1-dvr-matrix-diagonalization-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.local_norm_order-a1.dvr_determinant_length-a1`
- Child key: `dvr_matrix_diagonalization`
- Declaration: `Submission.p06_9e0f5043ff_dlen_matrix_diagonalization`
- Exact Lean type: `∀ (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] (m : ℕ) (D : Matrix (Fin m) (Fin m) A), D.det ≠ 0 → ∃ (P Q : Matrix (Fin m) (Fin m) A) (d : Fin m → A), IsUnit P ∧ IsUnit Q ∧ (∀ i, d i ≠ 0) ∧ P * D * Q = Matrix.diagonal d`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
