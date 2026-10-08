# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.level_one_valence_inequality-a1.indentation_limit-a1.local_logderiv_remainder-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/nodes/root-level-one-valence-inequality-a1-indentation-limit-a1-local-logde-07f2fad856/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.level_one_valence_inequality-a1.indentation_limit-a1`
- Child key: `local_logderiv_remainder`
- Declaration: `Submission.p10_17ae7b7d_indent_logderiv_remainder`
- Exact Lean type: `∀ (f : ℂ → ℂ) (v : ℂ), AnalyticAt ℂ f v → analyticOrderAt f v ≠ ⊤ → ∃ (r M : ℝ) (G : ℂ → ℂ), 0 < r ∧ 0 ≤ M ∧ AnalyticOnNhd ℂ G (Metric.closedBall v r) ∧ (∀ z ∈ Metric.closedBall v r, ‖G z‖ ≤ M) ∧ ∀ z ∈ Metric.ball v r, z ≠ v → f z ≠ 0 ∧ deriv f z / f z = (analyticOrderNatAt f v : ℂ) / (z - v) + G z`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
