# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.level_one_valence_inequality-a1.modular_log_derivative-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/nodes/root-level-one-valence-inequality-a1-modular-log-derivative-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.level_one_valence_inequality-a1`
- Child key: `modular_log_derivative`
- Declaration: `Submission.p10_17ae7b7d_valence_modular_log_derivative`
- Exact Lean type: `∀ (k : ℕ) (F : ℂ → ℂ), DifferentiableOn ℂ F {z : ℂ | 0 < z.im} → (∀ z : ℂ, 0 < z.im → F (z + 1) = F z) → (∀ z : ℂ, 0 < z.im → F (-1 / z) = z ^ k * F z) → ∀ z : ℂ, 0 < z.im → analyticOrderNatAt F (z + 1) = analyticOrderNatAt F z ∧ analyticOrderNatAt F (-1 / z) = analyticOrderNatAt F z ∧ (F z ≠ 0 → deriv F (z + 1) / F (z + 1) = deriv F z / F z ∧ (deriv F (-1 / z) / F (-1 / z)) / z ^ 2 = (k : ℂ) / z + deriv F z / F z)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
