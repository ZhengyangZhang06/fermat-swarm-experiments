# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tate_uniformization-a1.bilateral_summability-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/nodes/root-tate-uniformization-a1-bilateral-summability-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tate_uniformization-a1`
- Child key: `bilateral_summability`
- Declaration: `Submission.p03_tu_bilateral_summable_68cf3476`
- Exact Lean type: `∀ (F Ω : Type) [NormedField F] [CompleteSpace F] [NormedField Ω] [NormedAlgebra F Ω] [Algebra.IsAlgebraic F Ω], (∀ x y : Ω, ‖x + y‖ ≤ max ‖x‖ ‖y‖) → ∀ q : F, 0 < ‖q‖ → ‖q‖ < 1 → let qΩ : Ω := algebraMap F Ω q; ∀ u : Ωˣ, (¬ ∃ m : ℤ, (u : Ω) = qΩ ^ m) → Summable (fun n : ℤ => qΩ ^ n * (u : Ω) / (1 - qΩ ^ n * (u : Ω)) ^ 2) ∧ Summable (fun n : ℤ => (qΩ ^ n * (u : Ω)) ^ 2 / (1 - qΩ ^ n * (u : Ω)) ^ 3)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
