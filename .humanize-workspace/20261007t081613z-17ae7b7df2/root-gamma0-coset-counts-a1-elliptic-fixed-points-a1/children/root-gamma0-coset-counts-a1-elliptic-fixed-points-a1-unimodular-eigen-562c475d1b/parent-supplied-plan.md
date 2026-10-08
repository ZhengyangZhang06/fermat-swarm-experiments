# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.gamma0_coset_counts-a1.elliptic_fixed_points-a1.unimodular_eigenrow_normalization-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/nodes/root-gamma0-coset-counts-a1-elliptic-fixed-points-a1-unimodular-eigen-562c475d1b/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.gamma0_coset_counts-a1.elliptic_fixed_points-a1`
- Child key: `unimodular_eigenrow_normalization`
- Declaration: `Submission.p10_17ae7b7d_efp_unimodular_eigenrow_iff`
- Exact Lean type: `∀ (R : Type) [CommRing R] (k r s : R), (∃ x y : R, x * r + y * s = 1) → ((∃ u : Rˣ, s = (u : R) * r ∧ k * s - r = (u : R) * s) ↔ IsUnit r ∧ ∃! t : R, s = r * t ∧ t ^ 2 - k * t + 1 = 0)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
