# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.local_norm_order-a1.integral_fiber_length-a1.residue_length_inertia-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-local-norm-order-a1-integral-fiber-length-a1-residue-length-inertia-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.local_norm_order-a1.integral_fiber_length-a1`
- Child key: `residue_length_inertia`
- Declaration: `Submission.p06_9e0f5043ff_ifl_residue_length_inertia`
- Exact Lean type: `∀ (K E L : Type*) [Field K] [Field E] [Field L] [Algebra K E] [Algebra K L] [Algebra E L] [IsScalarTower K E L] [FiniteDimensional E L] [Algebra.IsSeparable E L] (v : AlgebraicCurve.Place K E) (w : AlgebraicCurve.Place K L) (hw : w.restrict E = v), Module.length v.toValuationSubring (AlgebraicCurve.Place.integralClosureAt L v ⧸ (AlgebraicCurve.Place.fiberCenter L v hw).asIdeal) = (w.inertiaDeg E : ℕ∞)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
