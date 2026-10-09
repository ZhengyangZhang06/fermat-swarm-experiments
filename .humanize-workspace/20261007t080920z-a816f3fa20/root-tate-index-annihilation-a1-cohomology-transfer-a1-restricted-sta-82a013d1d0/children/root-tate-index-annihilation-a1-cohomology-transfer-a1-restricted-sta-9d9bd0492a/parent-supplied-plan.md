# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tate_index_annihilation-a1.cohomology_transfer-a1.restricted_standard_homotopy-a1.normalized_equivariant_retraction-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/nodes/root-tate-index-annihilation-a1-cohomology-transfer-a1-restricted-sta-9d9bd0492a/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tate_index_annihilation-a1.cohomology_transfer-a1.restricted_standard_homotopy-a1`
- Child key: `normalized_equivariant_retraction`
- Declaration: `Submission.p04_rsh_82a013d1d0_equivariant_retraction`
- Exact Lean type: `∀ {G : Type _} [Group G] (H : Subgroup G), ∃ r : G → H, (∀ (h : H) (g : G), r ((h : G) * g) = h * r g) ∧ ∀ h : H, r (h : G) = h`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
