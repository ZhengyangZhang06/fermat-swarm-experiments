# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.rational_adjoin_principal-a1.principal_alg_equiv-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-rational-adjoin-principal-a1-principal-alg-equiv-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.rational_adjoin_principal-a1`
- Child key: `principal_alg_equiv`
- Declaration: `Submission.p06_9e0f5043ff_principal_alg_equiv`
- Exact Lean type: `∀ (K E L : Type*) [Field K] [Field E] [Field L] [Algebra K E] [Algebra K L], (E ≃ₐ[K] L) → AlgebraicCurve.HasPrincipalDivisors K E → AlgebraicCurve.HasPrincipalDivisors K L`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
