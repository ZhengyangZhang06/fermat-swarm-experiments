# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.petersson_core_good_hecke-a1.effective_domain-a1.ae_orbit_interior-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/nodes/root-petersson-core-good-hecke-a1-effective-domain-a1-ae-orbit-interior-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.petersson_core_good_hecke-a1.effective_domain-a1`
- Child key: `ae_orbit_interior`
- Declaration: `Submission.f036cc6b1f_pc_ed_ae_orbit_interior`
- Exact Lean type: `∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane), ∀ a : Matrix.SpecialLinearGroup (Fin 2) ℤ, a • z ∈ ModularGroup.fd → a • z ∈ ModularGroup.fdo`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
