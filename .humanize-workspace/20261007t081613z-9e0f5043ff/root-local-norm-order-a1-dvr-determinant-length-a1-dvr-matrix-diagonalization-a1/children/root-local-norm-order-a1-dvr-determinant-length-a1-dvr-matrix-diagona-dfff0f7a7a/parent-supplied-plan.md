# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.local_norm_order-a1.dvr_determinant_length-a1.dvr_matrix_diagonalization-a1.split_divisible_pivot-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-local-norm-order-a1-dvr-determinant-length-a1-dvr-matrix-diagona-dfff0f7a7a/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.local_norm_order-a1.dvr_determinant_length-a1.dvr_matrix_diagonalization-a1`
- Child key: `split_divisible_pivot`
- Declaration: `Submission.p06_9e0f5043ff_dmd_split_divisible_pivot`
- Exact Lean type: `∀ (R : Type*) [CommRing R] (m : ℕ) (D : Matrix (Fin (m + 1)) (Fin (m + 1)) R) (r c : Fin (m + 1)), (∀ i j, D r c ∣ D i j) → ∃ (P Q : Matrix (Fin (m + 1)) (Fin (m + 1)) R) (C : Matrix (Fin m) (Fin m) R), IsUnit P ∧ IsUnit Q ∧ P * D * Q = Matrix.of (fun i j => Fin.cases (Fin.cases (D r c) (fun _ => 0) j) (fun i' => Fin.cases 0 (fun j' => C i' j') j) i)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
