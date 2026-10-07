# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.local_norm_order-a1.dvr_determinant_length-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-local-norm-order-a1-dvr-determinant-length-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.local_norm_order-a1`
- Child key: `dvr_determinant_length`
- Declaration: `Submission.p06_9e0f5043ff_lno_dvr_determinant_length`
- Exact Lean type: `∀ (K E : Type*) [Field K] [Field E] [Algebra K E] (v : AlgebraicCurve.Place K E) (M : Type*) [AddCommGroup M] [Module v.toValuationSubring M] [Module.Free v.toValuationSubring M] [Module.Finite v.toValuationSubring M] (T : M →ₗ[v.toValuationSubring] M), LinearMap.det T ≠ 0 → ∃ n : ℕ, Module.length v.toValuationSubring (M ⧸ LinearMap.range T) = (n : ℕ∞) ∧ v.ord (algebraMap v.toValuationSubring E (LinearMap.det T)) = (n : ℤ)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
