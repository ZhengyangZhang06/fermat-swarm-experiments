# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tate_index_annihilation-a1.tate_zero_transfer-a1.invariant_restriction_norm_range-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/nodes/root-tate-index-annihilation-a1-tate-zero-transfer-a1-invariant-restr-4fa1637a00/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tate_index_annihilation-a1.tate_zero_transfer-a1`
- Child key: `invariant_restriction_norm_range`
- Declaration: `Submission.p04_tz91_invariant_restriction_norm_range`
- Exact Lean type: `∀ {k G : Type _} [CommRing k] [Group G] [Fintype G] (A : Rep k G) (H : Subgroup G) [Fintype H], ∃ j : A.ρ.invariants →ₗ[k] (Rep.res H.subtype A).ρ.invariants, (∀ a : A.ρ.invariants, (j a : A) = (a : A)) ∧ LinearMap.range A.ρ.normBar ≤ (LinearMap.range (Rep.res H.subtype A).ρ.normBar).comap j`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
