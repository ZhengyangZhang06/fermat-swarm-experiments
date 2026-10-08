# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.level_one_valence_inequality-a1.cusp_log_derivative-a1.qexp_finite_order-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/nodes/root-level-one-valence-inequality-a1-cusp-log-derivative-a1-qexp-finite-order-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.level_one_valence_inequality-a1.cusp_log_derivative-a1`
- Child key: `qexp_finite_order`
- Declaration: `Submission.p10_17ae7b7d_cld_qexp_finite_order`
- Exact Lean type: `∀ (F A : ℂ → ℂ), DifferentiableOn ℂ F {z : ℂ | 0 < z.im} → (∃ z : ℂ, 0 < z.im ∧ F z ≠ 0) → AnalyticAt ℂ A 0 → (∃ Y₀ : ℝ, ∀ z : ℂ, 0 < z.im → Y₀ ≤ z.im → F z = A (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * z))) → analyticOrderAt A 0 ≠ ⊤`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
