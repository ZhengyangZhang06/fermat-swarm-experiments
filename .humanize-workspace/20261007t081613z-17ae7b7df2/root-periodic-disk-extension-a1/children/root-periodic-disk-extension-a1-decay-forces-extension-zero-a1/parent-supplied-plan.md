# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.periodic_disk_extension-a1.decay_forces_extension_zero-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/nodes/root-periodic-disk-extension-a1-decay-forces-extension-zero-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.periodic_disk_extension-a1`
- Child key: `decay_forces_extension_zero`
- Declaration: `Submission.p10_17ae7b7d_pde_decay_zero`
- Exact Lean type: `∀ (w : ℝ) (g A : ℂ → ℂ), 0 < w → ContinuousAt A 0 → (∀ z : ℂ, 0 < z.im → g z = A (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * z / (w : ℂ)))) → (∀ ε : ℝ, 0 < ε → ∃ Y : ℝ, ∀ z : ℂ, 0 < z.im → Y ≤ z.im → ‖g z‖ ≤ ε) → A 0 = 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
