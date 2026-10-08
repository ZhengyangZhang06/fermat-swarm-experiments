# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.finite_retraction-a1.projective_of_trivial_minors-a1.unit_minor_splitting-a1.inner_inverse_of_minors-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/nodes/root-finite-retraction-a1-projective-of-trivial-minors-a1-unit-minor-a44555b14f/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.finite_retraction-a1.projective_of_trivial_minors-a1.unit_minor_splitting-a1`
- Child key: `inner_inverse_of_minors`
- Declaration: `Submission.p05_ums_inner_inverse_of_minors_a5b449214a`
- Exact Lean type: `∀ {R : Type*} [CommRing R] (n p d : ℕ) (P : Matrix (Fin n) (Fin p) R) (rows : Fin d ↪ Fin n) (cols : Fin d ↪ Fin p) (_hunit : IsUnit (Matrix.det (P.submatrix rows cols))) (_hnext : ∀ (rows' : Fin (d + 1) ↪ Fin n) (cols' : Fin (d + 1) ↪ Fin p), Matrix.det (P.submatrix rows' cols') = 0), ∃ Q : Matrix (Fin p) (Fin n) R, P * Q * P = P`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
