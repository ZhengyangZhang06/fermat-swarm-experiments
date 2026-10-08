# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.level_one_valence_inequality-a1.indentation_limit-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/nodes/root-level-one-valence-inequality-a1-indentation-limit-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.level_one_valence_inequality-a1`
- Child key: `indentation_limit`
- Declaration: `Submission.p10_17ae7b7d_valence_indentation_limit`
- Exact Lean type: `∀ (f : ℂ → ℂ) (v : ℂ), 0 < v.im → AnalyticAt ℂ f v → analyticOrderAt f v ≠ ⊤ → ∀ (α β : ℝ → ℝ) (a b : ℝ), Filter.Tendsto α (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds a) → Filter.Tendsto β (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds b) → let γ : ℝ → ℝ → ℂ := fun ε t => (v - star v * ((ε : ℂ) * Complex.exp ((t : ℂ) * Complex.I))) / (1 - (ε : ℂ) * Complex.exp ((t : ℂ) * Complex.I)); Filter.Tendsto (fun ε : ℝ => intervalIntegral (fun t : ℝ => (deriv f (γ ε t) / f (γ ε t)) * deriv (γ ε) t) (α ε) (β ε) MeasureTheory.volume) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (Complex.I * (analyticOrderNatAt f v : ℂ) * ((b - a : ℝ) : ℂ)))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
