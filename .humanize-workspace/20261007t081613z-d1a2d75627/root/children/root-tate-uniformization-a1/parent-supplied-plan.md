# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tate_uniformization-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/nodes/root-tate-uniformization-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root`
- Child key: `tate_uniformization`
- Declaration: `Submission.p03_tate_uniformization_68cf3476`
- Exact Lean type: `∀ (F Ω : Type) [NormedField F] [CharZero F] [CompleteSpace F] [NormedField Ω] [CharZero Ω] [DecidableEq Ω] [NormedAlgebra F Ω] [IsAlgClosed Ω] [Algebra.IsAlgebraic F Ω], (∀ x y : F, ‖x + y‖ ≤ max ‖x‖ ‖y‖) → (∀ x y : Ω, ‖x + y‖ ≤ max ‖x‖ ‖y‖) → (∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∀ x : F, x ≠ 0 → ∃ n : ℤ, ‖x‖ = r ^ n) → ∀ q : F, 0 < ‖q‖ → ‖q‖ < 1 → let s : ℕ → F := fun k => ∑' d : ℕ, ((d + 1 : ℕ) : F) ^ k * q ^ (d + 1) / (1 - q ^ (d + 1)); let T : WeierstrassCurve F := ⟨1, 0, 0, -5 * s 3, -(5 * s 3 + 7 * s 5) / 12⟩; let qΩ : Ω := algebraMap F Ω q; let X : Ω → Ω := fun u => (∑' n : ℤ, qΩ ^ n * u / (1 - qΩ ^ n * u) ^ 2) - 2 * algebraMap F Ω (s 1); let Y : Ω → Ω := fun u => (∑' n : ℤ, (qΩ ^ n * u) ^ 2 / (1 - qΩ ^ n * u) ^ 3) + algebraMap F Ω (s 1); (∀ k : ℕ, Summable (fun d : ℕ => ((d + 1 : ℕ) : F) ^ k * q ^ (d + 1) / (1 - q ^ (d + 1)))) ∧ Multipliable (fun d : ℕ => (1 - q ^ (d + 1)) ^ 24) ∧ T.c₄ = 1 + 240 * s 3 ∧ T.c₆ = -1 + 504 * s 5 ∧ T.Δ = q * (∏' d : ℕ, (1 - q ^ (d + 1)) ^ 24) ∧ T.Δ ≠ 0 ∧ (∀ u : Ωˣ, (¬ ∃ m : ℤ, (u : Ω) = qΩ ^ m) → Summable (fun n : ℤ => qΩ ^ n * (u : Ω) / (1 - qΩ ^ n * (u : Ω)) ^ 2) ∧ Summable (fun n : ℤ => (qΩ ^ n * (u : Ω)) ^ 2 / (1 - qΩ ^ n * (u : Ω)) ^ 3)) ∧ ∃ θ : Additive Ωˣ →+ (WeierstrassCurve.Affine.baseChange T.toAffine Ω).Point, Function.Surjective θ ∧ (∀ u : Ωˣ, θ (Additive.ofMul u) = 0 ↔ ∃ m : ℤ, (u : Ω) = qΩ ^ m) ∧ (∀ u : Ωˣ, (¬ ∃ m : ℤ, (u : Ω) = qΩ ^ m) → ∃ h : (WeierstrassCurve.Affine.baseChange T.toAffine Ω).Nonsingular (X (u : Ω)) (Y (u : Ω)), θ (Additive.ofMul u) = WeierstrassCurve.Affine.Point.some (X (u : Ω)) (Y (u : Ω)) h) ∧ ∀ (σ : Ω ≃ₐ[F] Ω) (u : Ωˣ), θ (Additive.ofMul (Units.map σ.toMonoidHom u)) = σ • θ (Additive.ofMul u)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
