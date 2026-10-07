# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.scalarization_derivative-a1.open_derivative_ladder-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/nodes/root-scalarization-derivative-a1-open-derivative-ladder-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.scalarization_derivative-a1`
- Child key: `open_derivative_ladder`
- Declaration: `Submission.p02_es_177ebb5a_sd_open_ladder`
- Exact Lean type: `∀ (U : Set ℂ) (n : ℕ) (Q : ℕ → ℂ → ℂ) (g : ℂ → ℂ), IsOpen U → (∀ (r : ℕ), r < n → ∀ z ∈ U, HasDerivAt (Q r) (-Q (r + 1) z) z) → (∀ z ∈ U, HasDerivAt (Q n) (g z) z) → ∀ z ∈ U, iteratedDeriv (n + 1) (Q 0) z = (-1 : ℂ) ^ n * g z`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
