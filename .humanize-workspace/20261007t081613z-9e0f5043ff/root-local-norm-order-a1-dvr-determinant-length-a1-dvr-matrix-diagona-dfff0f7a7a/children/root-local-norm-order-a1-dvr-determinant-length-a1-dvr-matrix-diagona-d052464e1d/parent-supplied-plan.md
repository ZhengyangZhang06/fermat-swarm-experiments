# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.local_norm_order-a1.dvr_determinant_length-a1.dvr_matrix_diagonalization-a1.split_divisible_pivot-a1.clear_first_row-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-local-norm-order-a1-dvr-determinant-length-a1-dvr-matrix-diagona-d052464e1d/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.local_norm_order-a1.dvr_determinant_length-a1.dvr_matrix_diagonalization-a1.split_divisible_pivot-a1`
- Child key: `clear_first_row`
- Declaration: `Submission.p06_9e0f5043ff_sdp_clear_first_row`
- Exact Lean type: `∀ (R : Type*) [CommRing R] (m : ℕ) (H : Matrix (Fin (m + 1)) (Fin (m + 1)) R), (∀ i : Fin m, H i.succ 0 = 0) → (∀ j : Fin m, H 0 0 ∣ H 0 j.succ) → ∃ V : Matrix (Fin (m + 1)) (Fin (m + 1)) R, IsUnit V ∧ H * V = Matrix.of (fun i j => Fin.cases (Fin.cases (H 0 0) (fun _ => 0) j) (fun i' => Fin.cases 0 (fun j' => H i'.succ j'.succ) j) i)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
