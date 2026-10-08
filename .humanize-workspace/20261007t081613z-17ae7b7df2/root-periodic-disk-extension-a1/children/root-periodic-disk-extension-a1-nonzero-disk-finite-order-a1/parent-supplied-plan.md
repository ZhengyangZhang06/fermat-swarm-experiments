# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.periodic_disk_extension-a1.nonzero_disk_finite_order-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/nodes/root-periodic-disk-extension-a1-nonzero-disk-finite-order-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.periodic_disk_extension-a1`
- Child key: `nonzero_disk_finite_order`
- Declaration: `Submission.p10_17ae7b7d_pde_finite_order`
- Exact Lean type: `∀ A : ℂ → ℂ, DifferentiableOn ℂ A (Metric.ball (0 : ℂ) 1) → (∃ q : ℂ, q ∈ Metric.ball (0 : ℂ) 1 ∧ A q ≠ 0) → analyticOrderAt A 0 ≠ ⊤ ∧ (A 0 = 0 → 1 ≤ analyticOrderNatAt A 0)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
