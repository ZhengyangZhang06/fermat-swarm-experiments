# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.petersson_core_good_hecke-a1.hecke_integral_adjointness-a1.finite_trace_unfolding-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/nodes/root-petersson-core-good-hecke-a1-hecke-integral-adjointness-a1-finit-bd663b5f6d/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.petersson_core_good_hecke-a1.hecke_integral_adjointness-a1`
- Child key: `finite_trace_unfolding`
- Declaration: `Submission.f036cc6b1f_pc_hi_finite_trace_unfolding`
- Exact Lean type: `∀ (Γ Δ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) (R : Finset (Matrix.SpecialLinearGroup (Fin 2) ℤ)) (F : Set UpperHalfPlane), Δ ≤ Γ → (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) ∈ Δ → (∀ r ∈ R, r ∈ Γ) → (∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, γ ∈ Γ → ∃ r ∈ R, γ * r⁻¹ ∈ Δ) → (∀ r ∈ R, ∀ s ∈ R, s * r⁻¹ ∈ Δ → s = r) → MeasurableSet F → (∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane), ∃ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, γ ∈ Γ ∧ γ • z ∈ F ∧ ∀ δ : Matrix.SpecialLinearGroup (Fin 2) ℤ, δ ∈ Γ → δ • z ∈ F → δ = γ ∨ δ = -γ) → ∀ u v : UpperHalfPlane → ℂ, (∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, γ ∈ Γ → SlashAction.map (2 : ℤ) γ v = v) → let E : Set UpperHalfPlane := ⋃ r ∈ R, (fun z : UpperHalfPlane => r • z) '' F; MeasureTheory.IntegrableOn (UpperHalfPlane.petersson 2 u v) E (MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane) → (∀ r ∈ R, MeasureTheory.IntegrableOn (UpperHalfPlane.petersson 2 (SlashAction.map (2 : ℤ) r u) v) F (MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane)) ∧ MeasureTheory.integral ((MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane).restrict F) (UpperHalfPlane.petersson 2 (R.sum (fun r => SlashAction.map (2 : ℤ) r u)) v) = MeasureTheory.integral ((MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane).restrict E) (UpperHalfPlane.petersson 2 u v)`

## Sibling prerequisites

- `root.petersson_core_good_hecke-a1.hecke_integral_adjointness-a1.effective_domain_lift-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
