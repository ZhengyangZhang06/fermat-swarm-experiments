# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.gamma0_finite_dimensional-a1.coeff_vanishing_iff_decay-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/nodes/root-gamma0-finite-dimensional-a1-coeff-vanishing-iff-decay-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.gamma0_finite_dimensional-a1`
- Child key: `coeff_vanishing_iff_decay`
- Declaration: `Submission.f036cc6b1f_fd_coeff_decay`
- Exact Lean type: `∀ (Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)) (k : ℤ) (f : ModularForm Γ k), (1 : ℝ) ∈ Γ.strictPeriods → ∀ b : ℕ, (∀ n : ℕ, n ≤ b → (UpperHalfPlane.qExpansion 1 f).coeff n = 0) ↔ ∃ C Y : ℝ, 0 ≤ C ∧ ∀ z : UpperHalfPlane, Y ≤ z.im → ‖f z‖ ≤ C * Real.exp (-2 * Real.pi * ((b + 1 : ℕ) : ℝ) * z.im)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
