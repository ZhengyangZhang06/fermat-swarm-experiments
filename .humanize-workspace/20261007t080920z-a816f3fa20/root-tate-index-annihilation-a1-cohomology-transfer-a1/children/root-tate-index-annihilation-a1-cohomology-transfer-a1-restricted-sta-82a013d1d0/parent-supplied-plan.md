# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tate_index_annihilation-a1.cohomology_transfer-a1.restricted_standard_homotopy-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/nodes/root-tate-index-annihilation-a1-cohomology-transfer-a1-restricted-sta-82a013d1d0/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tate_index_annihilation-a1.cohomology_transfer-a1`
- Child key: `restricted_standard_homotopy`
- Declaration: `Submission.p04_tia_coh_restricted_standard_homotopy_equiv`
- Exact Lean type: `∀ {k G : Type _} [CommRing k] [Group G] (H : Subgroup G), Nonempty (HomotopyEquiv (((Rep.resFunctor H.subtype).mapHomologicalComplex (ComplexShape.down ℕ)).obj (Rep.standardComplex k G)) (Rep.standardComplex k H))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
