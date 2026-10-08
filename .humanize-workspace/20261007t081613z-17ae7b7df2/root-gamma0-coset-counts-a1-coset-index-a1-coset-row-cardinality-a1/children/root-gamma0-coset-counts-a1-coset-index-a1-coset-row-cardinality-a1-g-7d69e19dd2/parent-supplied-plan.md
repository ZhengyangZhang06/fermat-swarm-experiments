# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.gamma0_coset_counts-a1.coset_index-a1.coset_row_cardinality-a1.gamma0_bottom_row_criterion-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/nodes/root-gamma0-coset-counts-a1-coset-index-a1-coset-row-cardinality-a1-g-7d69e19dd2/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.gamma0_coset_counts-a1.coset_index-a1.coset_row_cardinality-a1`
- Child key: `gamma0_bottom_row_criterion`
- Declaration: `Submission.p10_17ae7b7d_crcard_gamma0_row_criterion`
- Exact Lean type: `∀ (N : ℕ) [NeZero N] (A B : Matrix.SpecialLinearGroup (Fin 2) ℤ), B * A⁻¹ ∈ CongruenceSubgroup.Gamma0 N ↔ ∃ u : (ZMod N)ˣ, (u : ZMod N) * (A 1 0 : ZMod N) = (B 1 0 : ZMod N) ∧ (u : ZMod N) * (A 1 1 : ZMod N) = (B 1 1 : ZMod N)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
