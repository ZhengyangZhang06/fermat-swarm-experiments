# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.level_one_valence_inequality-a1.indentation_limit-a1.moving_interval_limit-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/nodes/root-level-one-valence-inequality-a1-indentation-limit-a1-moving-inte-3aa02a2634/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.level_one_valence_inequality-a1.indentation_limit-a1`
- Child key: `moving_interval_limit`
- Declaration: `Submission.p10_17ae7b7d_indent_moving_interval_limit`
- Exact Lean type: `∀ (F : ℝ → ℝ → ℂ) (α β δ : ℝ → ℝ) (c : ℂ) (a b : ℝ), Filter.Tendsto α (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds a) → Filter.Tendsto β (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds b) → Filter.Tendsto δ (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (0 : ℝ)) → Filter.Eventually (fun ε : ℝ => IntervalIntegrable (F ε) MeasureTheory.volume (α ε) (β ε) ∧ ∀ t : ℝ, ‖F ε t - c‖ ≤ δ ε) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) → Filter.Tendsto (fun ε : ℝ => intervalIntegral (F ε) (α ε) (β ε) MeasureTheory.volume) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (c * ((b - a : ℝ) : ℂ)))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
