# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.level_one_valence_inequality-a1.indentation_limit-a1.mobius_arc_estimates-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/nodes/root-level-one-valence-inequality-a1-indentation-limit-a1-mobius-arc-5103ece7f7/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.level_one_valence_inequality-a1.indentation_limit-a1`
- Child key: `mobius_arc_estimates`
- Declaration: `Submission.p10_17ae7b7d_indent_mobius_arc_estimates`
- Exact Lean type: `∀ (v : ℂ) (ε : ℝ), 0 < v.im → 0 < ε → ε < 1 → let w : ℝ → ℂ := fun t => (ε : ℂ) * Complex.exp ((t : ℂ) * Complex.I); let γ : ℝ → ℂ := fun t => (v - star v * w t) / (1 - w t); Continuous γ ∧ Continuous (deriv γ) ∧ ∀ t : ℝ, γ t ≠ v ∧ γ t - v = (v - star v) * w t / (1 - w t) ∧ HasDerivAt γ ((v - star v) * Complex.I * w t / (1 - w t) ^ 2) t ∧ deriv γ t / (γ t - v) = Complex.I / (1 - w t) ∧ ‖γ t - v‖ ≤ ‖v - star v‖ * ε / (1 - ε) ∧ ‖deriv γ t‖ ≤ ‖v - star v‖ * ε / (1 - ε) ^ 2 ∧ ‖deriv γ t / (γ t - v) - Complex.I‖ ≤ ε / (1 - ε)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
