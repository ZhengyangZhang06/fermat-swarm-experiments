# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.scalarization_modular-a1.translation_bound-a1.strip_coefficient_limit-a1.scalar_strip_limit-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/nodes/root-scalarization-modular-a1-translation-bound-a1-strip-coefficient-5d730d9900/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.scalarization_modular-a1.translation_bound-a1.strip_coefficient_limit-a1`
- Child key: `scalar_strip_limit`
- Declaration: `Submission.p02_es_177ebb5a_scl_scalar_strip_limit`
- Exact Lean type: `∀ (n : ℕ) (a D L y₀ : ℝ) (F H : ℂ → ℂ), 0 < a → 0 ≤ D → 0 ≤ L → 1 ≤ y₀ → ContinuousOn H {z : ℂ | 0 < z.im} → (∀ z : ℂ, 0 < z.im → HasDerivAt F (H z) z) → (∀ z : ℂ, 0 ≤ z.re → z.re ≤ L → y₀ ≤ z.im → ‖H z‖ ≤ D * (1 + z.im) ^ n * Real.exp (-a * z.im)) → ∃ b : ℂ, ∀ z : ℂ, 0 ≤ z.re → z.re ≤ L → y₀ ≤ z.im → ‖F z - b‖ ≤ (D * (∫ s in Set.Ioi (0 : ℝ), (1 + s) ^ n * Real.exp (-a * s))) * (1 + z.im) ^ n * Real.exp (-a * z.im)`

## Sibling prerequisites

- `root.scalarization_modular-a1.translation_bound-a1.strip_coefficient_limit-a1.polynomial_exponential_tail-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
