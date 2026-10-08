# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.petersson_core_good_hecke-a1.hecke_integral_adjointness-a1.rational_slash_transfer-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/nodes/root-petersson-core-good-hecke-a1-hecke-integral-adjointness-a1-ratio-ff0611020d/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.petersson_core_good_hecke-a1.hecke_integral_adjointness-a1`
- Child key: `rational_slash_transfer`
- Declaration: `Submission.f036cc6b1f_pc_hi_rational_slash`
- Exact Lean type: `∀ (Γ Δ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex] [Δ.FiniteIndex] (A : Matrix.GeneralLinearGroup (Fin 2) ℝ), 0 < (A.det : ℝ) → (∀ i j : Fin 2, ∃ q : ℚ, A i j = (q : ℝ)) → (∀ δ : Matrix.SpecialLinearGroup (Fin 2) ℤ, δ ∈ Δ → A * Matrix.SpecialLinearGroup.mapGL ℝ δ * A⁻¹ ∈ (Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ))) → ∀ f : CuspForm Γ 2, ∃ g : CuspForm Δ 2, (g : UpperHalfPlane → ℂ) = SlashAction.map (2 : ℤ) A (f : UpperHalfPlane → ℂ)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
