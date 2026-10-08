# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.petersson_core_good_hecke-a1.hecke_integral_adjointness-a1.effective_domain_lift-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/nodes/root-petersson-core-good-hecke-a1-hecke-integral-adjointness-a1-effec-094fe68ed5/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.petersson_core_good_hecke-a1.hecke_integral_adjointness-a1`
- Child key: `effective_domain_lift`
- Declaration: `Submission.f036cc6b1f_pc_hi_effective_domain_lift`
- Exact Lean type: `∀ (Γ Δ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) (R : Finset (Matrix.SpecialLinearGroup (Fin 2) ℤ)) (F : Set UpperHalfPlane), Δ ≤ Γ → (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) ∈ Δ → (∀ r ∈ R, r ∈ Γ) → (∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, γ ∈ Γ → ∃ r ∈ R, γ * r⁻¹ ∈ Δ) → (∀ r ∈ R, ∀ s ∈ R, s * r⁻¹ ∈ Δ → s = r) → MeasurableSet F → (∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane), ∃ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, γ ∈ Γ ∧ γ • z ∈ F ∧ ∀ δ : Matrix.SpecialLinearGroup (Fin 2) ℤ, δ ∈ Γ → δ • z ∈ F → δ = γ ∨ δ = -γ) → let E : Set UpperHalfPlane := ⋃ r ∈ R, (fun z : UpperHalfPlane => r • z) '' F; MeasurableSet E ∧ (∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane), ∃ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, γ ∈ Δ ∧ γ • z ∈ E ∧ ∀ δ : Matrix.SpecialLinearGroup (Fin 2) ℤ, δ ∈ Δ → δ • z ∈ E → δ = γ ∨ δ = -γ) ∧ (∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane), ∀ r ∈ R, ∀ s ∈ R, z ∈ (fun w : UpperHalfPlane => r • w) '' F → z ∈ (fun w : UpperHalfPlane => s • w) '' F → r = s)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
