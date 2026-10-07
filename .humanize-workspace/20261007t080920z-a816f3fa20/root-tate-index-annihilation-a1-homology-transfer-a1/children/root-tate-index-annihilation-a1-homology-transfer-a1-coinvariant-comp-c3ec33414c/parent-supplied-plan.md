# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tate_index_annihilation-a1.homology_transfer-a1.coinvariant_complex_transfer-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/nodes/root-tate-index-annihilation-a1-homology-transfer-a1-coinvariant-comp-c3ec33414c/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tate_index_annihilation-a1.homology_transfer-a1`
- Child key: `coinvariant_complex_transfer`
- Declaration: `Submission.p04_ht_coinvariant_complex_transfer`
- Exact Lean type: `∀ {k G : Type _} [CommRing k] [Group G] [Fintype G] (A : Rep k G) (H : Subgroup G) [Fintype H] (C : ChainComplex (Rep k G) ℕ) (n : ℕ), ∃ T : (C.coinvariantsTensorObj A).homology n →ₗ[k] ((((Rep.resFunctor (k := k) H.subtype).mapHomologicalComplex (ComplexShape.down ℕ)).obj C).coinvariantsTensorObj (Rep.res H.subtype A)).homology n, ∃ P : ((((Rep.resFunctor (k := k) H.subtype).mapHomologicalComplex (ComplexShape.down ℕ)).obj C).coinvariantsTensorObj (Rep.res H.subtype A)).homology n →ₗ[k] (C.coinvariantsTensorObj A).homology n, ∀ x : (C.coinvariantsTensorObj A).homology n, P (T x) = H.index • x`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
