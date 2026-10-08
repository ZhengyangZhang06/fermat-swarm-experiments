# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.petersson_core_good_hecke-a1.petersson_integral_core-a1.diagonal_integral_definite-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/nodes/root-petersson-core-good-hecke-a1-petersson-integral-core-a1-diagonal-bfb02b2f40/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.petersson_core_good_hecke-a1.petersson_integral_core-a1`
- Child key: `diagonal_integral_definite`
- Declaration: `Submission.f036cc6b1f_pic_diagonal_definite`
- Exact Lean type: `∀ (Δ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) (E : Set UpperHalfPlane), MeasurableSet E → (∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane), ∃ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, γ ∈ Δ ∧ γ • z ∈ E) → ∀ f : CuspForm Δ 2, MeasureTheory.IntegrableOn (UpperHalfPlane.petersson 2 f f) E (MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane) → MeasureTheory.integral ((MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane).restrict E) (UpperHalfPlane.petersson 2 f f) = 0 → f = 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
