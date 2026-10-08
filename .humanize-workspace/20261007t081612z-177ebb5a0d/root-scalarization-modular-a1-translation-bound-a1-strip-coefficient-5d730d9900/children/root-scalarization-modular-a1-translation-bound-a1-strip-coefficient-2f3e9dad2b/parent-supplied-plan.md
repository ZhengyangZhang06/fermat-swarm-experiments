# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.scalarization_modular-a1.translation_bound-a1.strip_coefficient_limit-a1.scalar_strip_limit-a1.ssl_segment_estimates-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/nodes/root-scalarization-modular-a1-translation-bound-a1-strip-coefficient-2f3e9dad2b/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.scalarization_modular-a1.translation_bound-a1.strip_coefficient_limit-a1.scalar_strip_limit-a1`
- Child key: `ssl_segment_estimates`
- Declaration: `Submission.p02_es_177ebb5a_ssl_segment_estimates`
- Exact Lean type: `∀ (F H : ℂ → ℂ) (w : ℝ → ℝ) (L y₀ : ℝ), 0 ≤ L → 0 < y₀ → ContinuousOn H {z : ℂ | 0 < z.im} → (∀ z : ℂ, 0 < z.im → HasDerivAt F (H z) z) → ContinuousOn w (Set.Ici y₀) → (∀ z : ℂ, 0 ≤ z.re → z.re ≤ L → y₀ ≤ z.im → ‖H z‖ ≤ w z.im) → (∀ (x y t : ℝ), 0 ≤ x → x ≤ L → y₀ ≤ y → y ≤ t → ‖F ((x : ℂ) + (t : ℂ) * Complex.I) - F ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤ ∫ s in y..t, w s) ∧ (∀ (x y : ℝ), 0 ≤ x → x ≤ L → y₀ ≤ y → ‖F ((x : ℂ) + (y : ℂ) * Complex.I) - F ((y : ℂ) * Complex.I)‖ ≤ x * w y)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
