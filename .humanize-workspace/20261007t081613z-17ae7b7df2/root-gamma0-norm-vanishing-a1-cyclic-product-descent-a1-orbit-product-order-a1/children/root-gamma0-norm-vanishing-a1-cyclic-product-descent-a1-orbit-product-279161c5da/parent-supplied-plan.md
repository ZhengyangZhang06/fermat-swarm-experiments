# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.gamma0_norm_vanishing-a1.cyclic_product_descent-a1.orbit_product_order-a1.cyclic_product_invariance-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/nodes/root-gamma0-norm-vanishing-a1-cyclic-product-descent-a1-orbit-product-279161c5da/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.gamma0_norm_vanishing-a1.cyclic_product_descent-a1.orbit_product_order-a1`
- Child key: `cyclic_product_invariance`
- Declaration: `Submission.p10_17ae7b7d_cpo_rotation_invariant`
- Exact Lean type: `∀ (w : ℕ) (ζ : ℂ) (A : ℂ → ℂ), 0 < w → ζ ^ w = 1 → let P : ℂ → ℂ := fun t => ∏ j ∈ Finset.range w, A (ζ ^ j * t); ∀ t : ℂ, P (ζ * t) = P t`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
