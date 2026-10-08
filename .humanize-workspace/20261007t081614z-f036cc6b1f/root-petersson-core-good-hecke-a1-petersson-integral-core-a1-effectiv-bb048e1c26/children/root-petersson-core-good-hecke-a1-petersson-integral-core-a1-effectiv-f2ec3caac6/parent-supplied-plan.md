# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.petersson_core_good_hecke-a1.petersson_integral_core-a1.effective_domain_transfer-a1.measurable_equidecomposition-a1.pointwise_sign_partition-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/nodes/root-petersson-core-good-hecke-a1-petersson-integral-core-a1-effectiv-f2ec3caac6/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.petersson_core_good_hecke-a1.petersson_integral_core-a1.effective_domain_transfer-a1.measurable_equidecomposition-a1`
- Child key: `pointwise_sign_partition`
- Declaration: `Submission.f036cc6b1f_pic_mec_pointwise_sign_partition`
- Exact Lean type: `∀ (Δ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) (E F X : Set UpperHalfPlane), (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) ∈ Δ → MeasurableSet E → MeasurableSet F → MeasurableSet X → (∀ (γ : Δ) (z : UpperHalfPlane), (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) • z ∈ X ↔ z ∈ X) → (∀ S : Set UpperHalfPlane, (S = E ∨ S = F) → ∀ z ∈ X, ∃ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, γ ∈ Δ ∧ γ • z ∈ S ∧ ∀ δ : Matrix.SpecialLinearGroup (Fin 2) ℤ, δ ∈ Δ → δ • z ∈ S → δ = γ ∨ δ = -γ) → ∃ A B : Δ → Set UpperHalfPlane, (∀ γ, MeasurableSet (A γ)) ∧ (∀ γ, MeasurableSet (B γ)) ∧ Pairwise (fun γ δ => Disjoint (A γ) (A δ)) ∧ Pairwise (fun γ δ => Disjoint (B γ) (B δ)) ∧ (⋃ γ, A γ) = E ∩ X ∧ (⋃ γ, B γ) = F ∩ X ∧ (∀ γ : Δ, (fun z : UpperHalfPlane => (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ)⁻¹ • z) '' (A γ) = B γ)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
