# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.local_norm_order-a1.dvr_determinant_length-a1.diagonal_matrix_cokernel-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-local-norm-order-a1-dvr-determinant-length-a1-diagonal-matrix-cokernel-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.local_norm_order-a1.dvr_determinant_length-a1`
- Child key: `diagonal_matrix_cokernel`
- Declaration: `Submission.p06_9e0f5043ff_dlen_diagonal_cokernel`
- Exact Lean type: `∀ (R : Type*) [CommRing R] (m : ℕ) (D P Q : Matrix (Fin m) (Fin m) R) (d : Fin m → R), IsUnit P → IsUnit Q → P * D * Q = Matrix.diagonal d → Nonempty (((Fin m → R) ⧸ LinearMap.range (Matrix.mulVecLin D)) ≃ₗ[R] ((i : Fin m) → R ⧸ Ideal.span ({d i} : Set R)))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
