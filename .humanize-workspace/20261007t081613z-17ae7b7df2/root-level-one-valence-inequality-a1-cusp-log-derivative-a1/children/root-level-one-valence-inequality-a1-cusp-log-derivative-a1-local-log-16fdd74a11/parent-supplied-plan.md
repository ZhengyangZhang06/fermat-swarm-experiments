# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.level_one_valence_inequality-a1.cusp_log_derivative-a1.local_logderiv_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/nodes/root-level-one-valence-inequality-a1-cusp-log-derivative-a1-local-log-16fdd74a11/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.level_one_valence_inequality-a1.cusp_log_derivative-a1`
- Child key: `local_logderiv_bound`
- Declaration: `Submission.p10_17ae7b7d_cld_local_logderiv_bound`
- Exact Lean type: `∀ (A : ℂ → ℂ), AnalyticAt ℂ A 0 → analyticOrderAt A 0 ≠ ⊤ → ∃ r M : ℝ, 0 < r ∧ 0 ≤ M ∧ DifferentiableOn ℂ A (Metric.ball (0 : ℂ) r) ∧ ∀ q : ℂ, q ≠ 0 → ‖q‖ < r → A q ≠ 0 ∧ ‖q * deriv A q / A q - (analyticOrderNatAt A 0 : ℂ)‖ ≤ M * ‖q‖`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
