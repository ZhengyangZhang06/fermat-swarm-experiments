# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.scalarization_modular-a1.translation_bound-a1.strip_coefficient_limit-a1.polynomial_exponential_tail-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/nodes/root-scalarization-modular-a1-translation-bound-a1-strip-coefficient-8293935c78/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.scalarization_modular-a1.translation_bound-a1.strip_coefficient_limit-a1`
- Child key: `polynomial_exponential_tail`
- Declaration: `Submission.p02_es_177ebb5a_scl_polynomial_exp_tail`
- Exact Lean type: `∀ (n : ℕ) (a : ℝ), 0 < a → MeasureTheory.IntegrableOn (fun s : ℝ => (1 + s) ^ n * Real.exp (-a * s)) (Set.Ioi 0) ∧ 0 ≤ (∫ s in Set.Ioi (0 : ℝ), (1 + s) ^ n * Real.exp (-a * s)) ∧ (∀ (y t : ℝ), 0 ≤ y → y ≤ t → (∫ s in y..t, (1 + s) ^ n * Real.exp (-a * s)) ≤ (∫ s in Set.Ioi (0 : ℝ), (1 + s) ^ n * Real.exp (-a * s)) * (1 + y) ^ n * Real.exp (-a * y)) ∧ Filter.Tendsto (fun y : ℝ => (1 + y) ^ n * Real.exp (-a * y)) Filter.atTop (nhds 0)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
