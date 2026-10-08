# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.gamma0_norm_vanishing-a1.cyclic_product_descent-a1.rotation_descent-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/nodes/root-gamma0-norm-vanishing-a1-cyclic-product-descent-a1-rotation-descent-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.gamma0_norm_vanishing-a1.cyclic_product_descent-a1`
- Child key: `rotation_descent`
- Declaration: `Submission.p10_17ae7b7d_cpd_rotation_descent`
- Exact Lean type: `∀ (w : ℕ) (P : ℂ → ℂ), 0 < w → AnalyticAt ℂ P 0 → (∃ s : ℝ, 0 < s ∧ ∀ t : ℂ, ‖t‖ < s → P (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (w : ℂ)) * t) = P t) → ∃ C : ℂ → ℂ, AnalyticAt ℂ C 0 ∧ ∃ r : ℝ, 0 < r ∧ ∀ t : ℂ, ‖t‖ < r → P t = C (t ^ w)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
