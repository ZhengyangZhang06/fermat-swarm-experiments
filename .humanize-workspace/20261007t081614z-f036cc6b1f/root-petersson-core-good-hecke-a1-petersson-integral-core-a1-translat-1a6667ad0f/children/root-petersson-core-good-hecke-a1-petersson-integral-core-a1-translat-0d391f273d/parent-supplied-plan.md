# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.petersson_core_good_hecke-a1.petersson_integral_core-a1.translated_domain_integrability-a1.petersson_integrable_of_exp_product-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/nodes/root-petersson-core-good-hecke-a1-petersson-integral-core-a1-translat-0d391f273d/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.petersson_core_good_hecke-a1.petersson_integral_core-a1.translated_domain_integrability-a1`
- Child key: `petersson_integrable_of_exp_product`
- Declaration: `Submission.f036cc6b1f_tdi_petersson_integrable_of_exp_product_bound`
- Exact Lean type: `∀ (u v : UpperHalfPlane → ℂ) (a C Y : ℝ), Continuous u → Continuous v → 0 < a → 0 ≤ C → (∀ z : UpperHalfPlane, Y ≤ z.im → ‖u z * v z‖ ≤ C * Real.exp (-a * z.im)) → MeasureTheory.IntegrableOn (UpperHalfPlane.petersson 2 u v) ModularGroup.fd (MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane)`

## Sibling prerequisites

- `root.petersson_core_good_hecke-a1.petersson_integral_core-a1.translated_domain_integrability-a1.planar_exp_integrable_fd-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
