# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.local_norm_order-a1.integral_fiber_length-a1.local_length_order-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-local-norm-order-a1-integral-fiber-length-a1-local-length-order-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.local_norm_order-a1.integral_fiber_length-a1`
- Child key: `local_length_order`
- Declaration: `Submission.p06_9e0f5043ff_ifl_local_length_order`
- Exact Lean type: `∀ (K E L : Type*) [Field K] [Field E] [Field L] [Algebra K E] [Algebra K L] [Algebra E L] [IsScalarTower K E L] [FiniteDimensional E L] [Algebra.IsSeparable E L] (v : AlgebraicCurve.Place K E) (q : IsDedekindDomain.HeightOneSpectrum (AlgebraicCurve.Place.integralClosureAt L v)) (R : Type*) [CommRing R] [IsDomain R] [Algebra (AlgebraicCurve.Place.integralClosureAt L v) R] [IsLocalization.AtPrime R q.asIdeal] (b : AlgebraicCurve.Place.integralClosureAt L v), b ≠ 0 → ∃ m : ℕ, Module.length R (R ⧸ Ideal.span ({algebraMap (AlgebraicCurve.Place.integralClosureAt L v) R b} : Set R)) = (m : ℕ∞) ∧ (AlgebraicCurve.Place.placeOfPrime q).ord (algebraMap (AlgebraicCurve.Place.integralClosureAt L v) L b) = (m : ℤ)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
