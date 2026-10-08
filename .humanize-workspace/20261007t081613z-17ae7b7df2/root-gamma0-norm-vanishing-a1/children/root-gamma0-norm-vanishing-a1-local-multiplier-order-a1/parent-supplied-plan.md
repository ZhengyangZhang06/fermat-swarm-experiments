# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.gamma0_norm_vanishing-a1.local_multiplier_order-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/nodes/root-gamma0-norm-vanishing-a1-local-multiplier-order-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.gamma0_norm_vanishing-a1`
- Child key: `local_multiplier_order`
- Declaration: `Submission.p10_17ae7b7d_norm_local_multiplier_order`
- Exact Lean type: `∀ (g ψ J : ℂ → ℂ) (v : ℂ), AnalyticAt ℂ g v → analyticOrderAt g v ≠ ⊤ → AnalyticAt ℂ ψ v → ψ v = v → deriv ψ v ≠ 0 → AnalyticAt ℂ J v → (∃ r : ℝ, 0 < r ∧ ∀ z : ℂ, ‖z - v‖ < r → g (ψ z) = J z * g z) → (deriv ψ v) ^ analyticOrderNatAt g v = J v`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
