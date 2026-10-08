# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.petersson_core_good_hecke-a1.petersson_integral_core-a1.effective_domain_transfer-a1.measurable_equidecomposition-a1.invariant_conull_core-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/nodes/root-petersson-core-good-hecke-a1-petersson-integral-core-a1-effectiv-2dae18e5e8/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.petersson_core_good_hecke-a1.petersson_integral_core-a1.effective_domain_transfer-a1.measurable_equidecomposition-a1`
- Child key: `invariant_conull_core`
- Declaration: `Submission.f036cc6b1f_pic_mec_invariant_conull_core`
- Exact Lean type: `∀ (Δ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) (S : Set UpperHalfPlane), MeasurableSet S → (∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane), z ∈ S) → ∃ X : Set UpperHalfPlane, MeasurableSet X ∧ (∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane), z ∈ X) ∧ X ⊆ S ∧ (∀ (γ : Δ) (z : UpperHalfPlane), (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) • z ∈ X ↔ z ∈ X)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
