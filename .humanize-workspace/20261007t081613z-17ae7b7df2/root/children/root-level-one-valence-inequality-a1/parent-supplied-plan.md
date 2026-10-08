# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.level_one_valence_inequality-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/nodes/root-level-one-valence-inequality-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root`
- Child key: `level_one_valence_inequality`
- Declaration: `Submission.p10_17ae7b7d_level_one_valence_inequality`
- Exact Lean type: `∀ (k : ℕ) (F A : ℂ → ℂ), Even k → DifferentiableOn ℂ F {z : ℂ | 0 < z.im} → (∃ z : ℂ, 0 < z.im ∧ F z ≠ 0) → (∀ z : ℂ, 0 < z.im → F (z + 1) = F z) → (∀ z : ℂ, 0 < z.im → F (-1 / z) = z ^ k * F z) → AnalyticAt ℂ A 0 → (∃ Y : ℝ, ∀ z : ℂ, 0 < z.im → Y ≤ z.im → F z = A (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * z))) → (analyticOrderNatAt A 0 : ℝ) + (analyticOrderNatAt F Complex.I : ℝ) / 2 + (analyticOrderNatAt F ((-1 + (Real.sqrt 3 : ℂ) * Complex.I) / 2) : ℝ) / 3 ≤ (k : ℝ) / 12`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
