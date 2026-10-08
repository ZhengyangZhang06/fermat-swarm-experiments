# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.gamma0_norm_vanishing-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/nodes/root-gamma0-norm-vanishing-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root`
- Child key: `gamma0_norm_vanishing`
- Declaration: `Submission.p10_17ae7b7d_gamma0_norm_vanishing`
- Exact Lean type: `∀ (N : ℕ) [NeZero N] (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2), f ≠ 0 → ∃ F A : ℂ → ℂ, DifferentiableOn ℂ F {z : ℂ | 0 < z.im} ∧ (∃ z : ℂ, 0 < z.im ∧ F z ≠ 0) ∧ (∀ z : ℂ, 0 < z.im → F (z + 1) = F z) ∧ (∀ z : ℂ, 0 < z.im → F (-1 / z) = z ^ (2 * ModularCurve.dedekindPsi N) * F z) ∧ AnalyticAt ℂ A 0 ∧ (∃ Y : ℝ, ∀ z : ℂ, 0 < z.im → Y ≤ z.im → F z = A (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * z))) ∧ ModularCurve.cuspCount N ≤ analyticOrderNatAt A 0 ∧ ModularCurve.nuTwo N ≤ analyticOrderNatAt F Complex.I ∧ 2 * ModularCurve.nuThree N ≤ analyticOrderNatAt F ((-1 + (Real.sqrt 3 : ℂ) * Complex.I) / 2)`

## Sibling prerequisites

- `root.gamma0_coset_counts-a1`
- `root.periodic_disk_extension-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
