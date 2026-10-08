# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tate_uniformization-a1.coordinate_symmetries-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/nodes/root-tate-uniformization-a1-coordinate-symmetries-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tate_uniformization-a1`
- Child key: `coordinate_symmetries`
- Declaration: `Submission.p03_tu_coordinate_symmetries_68cf3476`
- Exact Lean type: `∀ (F Ω : Type) [NormedField F] [CompleteSpace F] [NormedField Ω] [NormedAlgebra F Ω] [Algebra.IsAlgebraic F Ω], (∀ x y : Ω, ‖x + y‖ ≤ max ‖x‖ ‖y‖) → ∀ q : F, 0 < ‖q‖ → ‖q‖ < 1 → ∀ c : F, let qΩ : Ω := algebraMap F Ω q; let X : Ω → Ω := fun u => (∑' n : ℤ, qΩ ^ n * u / (1 - qΩ ^ n * u) ^ 2) - 2 * algebraMap F Ω c; let Y : Ω → Ω := fun u => (∑' n : ℤ, (qΩ ^ n * u) ^ 2 / (1 - qΩ ^ n * u) ^ 3) + algebraMap F Ω c; ∀ u : Ωˣ, (¬ ∃ m : ℤ, (u : Ω) = qΩ ^ m) → X (qΩ * (u : Ω)) = X (u : Ω) ∧ Y (qΩ * (u : Ω)) = Y (u : Ω) ∧ X ((u : Ω)⁻¹) = X (u : Ω) ∧ Y ((u : Ω)⁻¹) = -Y (u : Ω) - X (u : Ω) ∧ ∀ σ : Ω ≃ₐ[F] Ω, X (σ (u : Ω)) = σ (X (u : Ω)) ∧ Y (σ (u : Ω)) = σ (Y (u : Ω))`

## Sibling prerequisites

- `root.tate_uniformization-a1.bilateral_summability-a1`
- `root.tate_uniformization-a1.algebraic_aut_isometry-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
