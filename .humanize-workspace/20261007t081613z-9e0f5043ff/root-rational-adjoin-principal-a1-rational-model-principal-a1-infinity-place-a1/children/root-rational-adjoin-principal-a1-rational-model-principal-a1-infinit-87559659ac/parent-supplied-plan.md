# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.rational_adjoin_principal-a1.rational_model_principal-a1.infinity_place-a1.reciprocal_polynomial_order-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-rational-adjoin-principal-a1-rational-model-principal-a1-infinit-87559659ac/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.rational_adjoin_principal-a1.rational_model_principal-a1.infinity_place-a1`
- Child key: `reciprocal_polynomial_order`
- Declaration: `Submission.p06_9e0f5043ff_inf_reciprocal_polynomial_order`
- Exact Lean type: `∀ (K F : Type*) [Field K] [Field F] [Algebra K F] (s : F), Transcendental K s → ∀ v : AlgebraicCurve.Place K F, v.ord s = 1 → (∀ c : Polynomial K, ¬ (Polynomial.X : Polynomial K) ∣ c → v.ord (Polynomial.aeval s c) = 0) → ∀ a : Polynomial K, a ≠ 0 → v.ord (Polynomial.aeval s⁻¹ a) = -(a.natDegree : ℤ)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
