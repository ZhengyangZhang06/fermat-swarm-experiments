# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.gamma0_coset_counts-a1.coset_index-a1.crt_row_cardinality-a1.ring_equiv_row_classes-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/nodes/root-gamma0-coset-counts-a1-coset-index-a1-crt-row-cardinality-a1-rin-c0ac07a37c/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.gamma0_coset_counts-a1.coset_index-a1.crt_row_cardinality-a1`
- Child key: `ring_equiv_row_classes`
- Declaration: `Submission.p10_17ae7b7d_crt_ring_equiv_rows`
- Exact Lean type: `∀ (R S : Type) [CommRing R] [CommRing S], (R ≃+* S) → let P := fun (A : Type) [CommRing A] => Quot (fun v w : {v : A × A // ∃ x y : A, x * v.1 + y * v.2 = 1} => ∃ u : Aˣ, (u : A) * v.1.1 = w.1.1 ∧ (u : A) * v.1.2 = w.1.2); Nonempty (P R ≃ P S)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
