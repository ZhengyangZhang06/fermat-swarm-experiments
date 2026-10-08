# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.gamma0_coset_counts-a1.coset_index-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/nodes/root-gamma0-coset-counts-a1-coset-index-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.gamma0_coset_counts-a1`
- Child key: `coset_index`
- Declaration: `Submission.p10_17ae7b7d_cc_index`
- Exact Lean type: `∀ (N : ℕ) [NeZero N], let Q := (Matrix.SpecialLinearGroup (Fin 2) ℤ) ⧸ CongruenceSubgroup.Gamma0 N; Finite Q ∧ Nat.card Q = ModularCurve.dedekindPsi N`

## Sibling prerequisites

- `root.gamma0_coset_counts-a1.lift_unimodular_row-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
