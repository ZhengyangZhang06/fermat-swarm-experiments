# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.petersson_core_good_hecke-a1.petersson_integral_core-a1.effective_domain_transfer-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/nodes/root-petersson-core-good-hecke-a1-petersson-integral-core-a1-effectiv-202b24e1b4/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.petersson_core_good_hecke-a1.petersson_integral_core-a1`
- Child key: `effective_domain_transfer`
- Declaration: `Submission.f036cc6b1f_pic_domain_transfer`
- Exact Lean type: `∀ (Δ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) (E F : Set UpperHalfPlane), (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) ∈ Δ → MeasurableSet E → MeasurableSet F → (∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane), ∃ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, γ ∈ Δ ∧ γ • z ∈ E ∧ ∀ δ : Matrix.SpecialLinearGroup (Fin 2) ℤ, δ ∈ Δ → δ • z ∈ E → δ = γ ∨ δ = -γ) → (∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane), ∃ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, γ ∈ Δ ∧ γ • z ∈ F ∧ ∀ δ : Matrix.SpecialLinearGroup (Fin 2) ℤ, δ ∈ Δ → δ • z ∈ F → δ = γ ∨ δ = -γ) → ∀ φ : UpperHalfPlane → ℂ, Continuous φ → (∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, γ ∈ Δ → ∀ z : UpperHalfPlane, φ (γ • z) = φ z) → MeasureTheory.IntegrableOn φ E (MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane) → MeasureTheory.IntegrableOn φ F (MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane) ∧ MeasureTheory.integral ((MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane).restrict E) φ = MeasureTheory.integral ((MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane).restrict F) φ`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
