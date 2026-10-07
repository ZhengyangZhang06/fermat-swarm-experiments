# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.local_norm_order-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-local-norm-order-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root`
- Child key: `local_norm_order`
- Declaration: `Submission.p06_9e0f5043ff_local_norm_order`
- Exact Lean type: `∀ (K E L : Type*) [Field K] [Field E] [Field L] [Algebra K E] [Algebra K L] [Algebra E L] [IsScalarTower K E L] [FiniteDimensional E L] [Algebra.IsSeparable E L] (v : AlgebraicCurve.Place K E) (f : L), f ≠ 0 → v.ord (Algebra.norm E f) = Finset.sum (v.fiberOver L) (fun w => (w.inertiaDeg E : ℤ) * w.ord f)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
