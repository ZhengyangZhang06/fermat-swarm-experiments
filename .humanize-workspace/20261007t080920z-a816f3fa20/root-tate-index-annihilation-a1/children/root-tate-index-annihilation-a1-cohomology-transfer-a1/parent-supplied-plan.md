# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tate_index_annihilation-a1.cohomology_transfer-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/nodes/root-tate-index-annihilation-a1-cohomology-transfer-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tate_index_annihilation-a1`
- Child key: `cohomology_transfer`
- Declaration: `Submission.p04_tia_cohomology_transfer`
- Exact Lean type: `∀ {k G : Type _} [CommRing k] [Group G] [Fintype G] (A : Rep k G) (H : Subgroup G) [Fintype H] (n : ℕ), ∃ R : groupCohomology A n →ₗ[k] groupCohomology (Rep.res H.subtype A) n, ∃ C : groupCohomology (Rep.res H.subtype A) n →ₗ[k] groupCohomology A n, ∀ x : groupCohomology A n, C (R x) = H.index • x`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
