# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.rational_adjoin_principal-a1.rational_model_principal-a1.infinity_place-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-rational-adjoin-principal-a1-rational-model-principal-a1-infinity-place-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.rational_adjoin_principal-a1.rational_model_principal-a1`
- Child key: `infinity_place`
- Declaration: `Submission.p06_9e0f5043ff_rmp_infinity_place`
- Exact Lean type: `∀ (K : Type*) [Field K], ∃ v : AlgebraicCurve.Place K (FractionRing (Polynomial K)), algebraMap (Polynomial K) (FractionRing (Polynomial K)) Polynomial.X ∉ v.toValuationSubring ∧ v.deg = 1 ∧ (∀ a : Polynomial K, a ≠ 0 → v.ord (algebraMap (Polynomial K) (FractionRing (Polynomial K)) a) = -(a.natDegree : ℤ)) ∧ (∀ w : AlgebraicCurve.Place K (FractionRing (Polynomial K)), algebraMap (Polynomial K) (FractionRing (Polynomial K)) Polynomial.X ∉ w.toValuationSubring → w = v)`

## Sibling prerequisites

- `root.rational_adjoin_principal-a1.rational_model_principal-a1.finite_place_model-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
