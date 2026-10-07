# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.local_norm_order-a1.dvr_determinant_length-a1.scalar_quotient_length_order-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-local-norm-order-a1-dvr-determinant-length-a1-scalar-quotient-le-9dc69f4859/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.local_norm_order-a1.dvr_determinant_length-a1`
- Child key: `scalar_quotient_length_order`
- Declaration: `Submission.p06_9e0f5043ff_dlen_scalar_quotient`
- Exact Lean type: `∀ (K E : Type*) [Field K] [Field E] [Algebra K E] (v : AlgebraicCurve.Place K E) (a : v.toValuationSubring), a ≠ 0 → ∃ n : ℕ, Module.length v.toValuationSubring (v.toValuationSubring ⧸ Ideal.span ({a} : Set v.toValuationSubring)) = (n : ℕ∞) ∧ v.ord (algebraMap v.toValuationSubring E a) = (n : ℤ)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
