# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.gamma0_coset_counts-a1.coset_index-a1.prime_power_row_cardinality-a1.unit_chart_equivalence-a1.normalized_quotient_rigidity-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/nodes/root-gamma0-coset-counts-a1-coset-index-a1-prime-power-row-cardinalit-c133016709/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.gamma0_coset_counts-a1.coset_index-a1.prime_power_row_cardinality-a1.unit_chart_equivalence-a1`
- Child key: `normalized_quotient_rigidity`
- Declaration: `Submission.p10_17ae7b7d_uce_normalized_quot_eq_iff`
- Exact Lean type: `∀ (R : Type) [CommRing R], let U := {v : R × R // ∃ x y : R, x * v.1 + y * v.2 = 1}; let rel : U → U → Prop := fun v w => ∃ u : Rˣ, (u : R) * v.1.1 = w.1.1 ∧ (u : R) * v.1.2 = w.1.2; ∀ v w : U, (v.1.1 = 1 ∨ (¬ IsUnit v.1.1 ∧ v.1.2 = 1)) → (w.1.1 = 1 ∨ (¬ IsUnit w.1.1 ∧ w.1.2 = 1)) → (Quot.mk rel v = Quot.mk rel w ↔ v = w)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
