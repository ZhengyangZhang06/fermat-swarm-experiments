# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.petersson_core_good_hecke-a1.petersson_integral_core-a1.translated_domain_integrability-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/nodes/root-petersson-core-good-hecke-a1-petersson-integral-core-a1-translat-1a6667ad0f/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.petersson_core_good_hecke-a1.petersson_integral_core-a1`
- Child key: `translated_domain_integrability`
- Declaration: `Submission.f036cc6b1f_pic_translated_integrable`
- Exact Lean type: `∀ (Δ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Δ.FiniteIndex] (r : Matrix.SpecialLinearGroup (Fin 2) ℤ) (f g : CuspForm Δ 2), MeasureTheory.IntegrableOn (UpperHalfPlane.petersson 2 f g) ((fun z : UpperHalfPlane => r • z) '' ModularGroup.fd) (MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
