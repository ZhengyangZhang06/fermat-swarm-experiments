# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.petersson_core_good_hecke-a1.effective_domain-a1.ae_orbit_interior-a1.measurable_null_orbit_avoidance-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/nodes/root-petersson-core-good-hecke-a1-effective-domain-a1-ae-orbit-interi-9760a4d8a3/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.petersson_core_good_hecke-a1.effective_domain-a1.ae_orbit_interior-a1`
- Child key: `measurable_null_orbit_avoidance`
- Declaration: `Submission.f036cc6b1f_pc_ed_aoi_null_orbit`
- Exact Lean type: `∀ s : Set UpperHalfPlane, MeasurableSet s → (MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane) s = 0 → ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane), ∀ a : Matrix.SpecialLinearGroup (Fin 2) ℤ, a • z ∉ s`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
