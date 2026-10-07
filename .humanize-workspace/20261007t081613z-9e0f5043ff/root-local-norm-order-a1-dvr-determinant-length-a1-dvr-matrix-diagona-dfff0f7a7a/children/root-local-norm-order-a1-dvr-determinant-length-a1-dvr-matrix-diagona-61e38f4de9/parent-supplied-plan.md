# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.local_norm_order-a1.dvr_determinant_length-a1.dvr_matrix_diagonalization-a1.split_divisible_pivot-a1.clear_first_column-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-local-norm-order-a1-dvr-determinant-length-a1-dvr-matrix-diagona-61e38f4de9/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.local_norm_order-a1.dvr_determinant_length-a1.dvr_matrix_diagonalization-a1.split_divisible_pivot-a1`
- Child key: `clear_first_column`
- Declaration: `Submission.p06_9e0f5043ff_sdp_clear_first_column`
- Exact Lean type: `∀ (R : Type*) [CommRing R] (m : ℕ) (B : Matrix (Fin (m + 1)) (Fin (m + 1)) R), (∀ i : Fin m, B 0 0 ∣ B i.succ 0) → ∃ U : Matrix (Fin (m + 1)) (Fin (m + 1)) R, IsUnit U ∧ (∀ j : Fin (m + 1), (U * B) 0 j = B 0 j) ∧ (∀ i : Fin m, (U * B) i.succ 0 = 0)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
