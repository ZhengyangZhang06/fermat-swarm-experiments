# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.local_norm_order-a1.dvr_determinant_length-a1.dvr_matrix_diagonalization-a1.finite_family_dividing_member-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-local-norm-order-a1-dvr-determinant-length-a1-dvr-matrix-diagona-c588ebcc13/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.local_norm_order-a1.dvr_determinant_length-a1.dvr_matrix_diagonalization-a1`
- Child key: `finite_family_dividing_member`
- Declaration: `Submission.p06_9e0f5043ff_dmd_finite_family_dividing_member`
- Exact Lean type: `∀ (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] (ι : Type*) [Fintype ι] (a : ι → A), (∃ i, a i ≠ 0) → ∃ i, a i ≠ 0 ∧ ∀ j, a i ∣ a j`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
