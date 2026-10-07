# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.finite_order_support_ascent-a1.polynomial_coefficients_integral_off_fa-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-finite-order-support-ascent-a1-polynomial-coefficients-integral-off-fa-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.finite_order_support_ascent-a1`
- Child key: `polynomial_coefficients_integral_off_fa`
- Declaration: `Submission.p06_9e0f5043ff_fosa_coefficients_integral_off_finite`
- Exact Lean type: `∀ (K E : Type*) [Field K] [Field E] [Algebra K E], (∀ a : E, a ≠ 0 → {v : AlgebraicCurve.Place K E | v.ord a ≠ 0}.Finite) → ∀ P : Polynomial E, ∃ T : Set (AlgebraicCurve.Place K E), T.Finite ∧ ∀ v : AlgebraicCurve.Place K E, v ∉ T → ∀ i : ℕ, P.coeff i ∈ v.toValuationSubring`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
