# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.gamma0_coset_counts-a1.coset_index-a1.prime_power_row_cardinality-a1.unit_chart_equivalence-a1.unimodular_iff_unit_coordinate-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/nodes/root-gamma0-coset-counts-a1-coset-index-a1-prime-power-row-cardinalit-af66d3eb5a/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.gamma0_coset_counts-a1.coset_index-a1.prime_power_row_cardinality-a1.unit_chart_equivalence-a1`
- Child key: `unimodular_iff_unit_coordinate`
- Declaration: `Submission.p10_17ae7b7d_uce_unimodular_iff_unit_coord`
- Exact Lean type: `∀ (p a : ℕ), p.Prime → 0 < a → ∀ r s : ZMod (p ^ a), (∃ x y : ZMod (p ^ a), x * r + y * s = 1) ↔ IsUnit r ∨ IsUnit s`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
