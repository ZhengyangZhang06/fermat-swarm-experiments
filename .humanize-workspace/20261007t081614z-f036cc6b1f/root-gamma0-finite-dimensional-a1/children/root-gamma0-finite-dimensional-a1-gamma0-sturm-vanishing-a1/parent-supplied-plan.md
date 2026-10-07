# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.gamma0_finite_dimensional-a1.gamma0_sturm_vanishing-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/nodes/root-gamma0-finite-dimensional-a1-gamma0-sturm-vanishing-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.gamma0_finite_dimensional-a1`
- Child key: `gamma0_sturm_vanishing`
- Declaration: `Submission.f036cc6b1f_fd_sturm`
- Exact Lean type: `∀ (M : ℕ) [NeZero M] (f : CuspForm (CongruenceSubgroup.Gamma0 M) 2), (∀ n : ℕ, n ≤ (2 * (CongruenceSubgroup.Gamma0 M).index) / 12 → (UpperHalfPlane.qExpansion 1 f).coeff n = 0) → f = 0`

## Sibling prerequisites

- `root.gamma0_finite_dimensional-a1.coeff_vanishing_iff_decay-a1`
- `root.gamma0_finite_dimensional-a1.coset_norm_bound-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
