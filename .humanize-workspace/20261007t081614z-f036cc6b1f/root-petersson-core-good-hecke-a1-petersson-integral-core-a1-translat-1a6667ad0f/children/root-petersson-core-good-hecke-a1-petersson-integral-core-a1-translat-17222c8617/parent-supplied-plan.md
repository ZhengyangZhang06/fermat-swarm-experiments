# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.petersson_core_good_hecke-a1.petersson_integral_core-a1.translated_domain_integrability-a1.planar_exp_integrable_fd-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/nodes/root-petersson-core-good-hecke-a1-petersson-integral-core-a1-translat-17222c8617/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.petersson_core_good_hecke-a1.petersson_integral_core-a1.translated_domain_integrability-a1`
- Child key: `planar_exp_integrable_fd`
- Declaration: `Submission.f036cc6b1f_tdi_planar_exp_integrable_fd`
- Exact Lean type: `∀ (a : ℝ), 0 < a → MeasureTheory.IntegrableOn (fun z : UpperHalfPlane => Real.exp (-a * z.im)) ModularGroup.fd ((MeasureTheory.volume : MeasureTheory.Measure ℂ).comap UpperHalfPlane.coe)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
