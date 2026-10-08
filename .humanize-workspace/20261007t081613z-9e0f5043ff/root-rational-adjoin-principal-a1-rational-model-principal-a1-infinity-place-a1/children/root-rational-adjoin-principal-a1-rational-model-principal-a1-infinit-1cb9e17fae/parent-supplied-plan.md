# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.rational_adjoin_principal-a1.rational_model_principal-a1.infinity_place-a1.reciprocal_presentation-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-rational-adjoin-principal-a1-rational-model-principal-a1-infinit-1cb9e17fae/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.rational_adjoin_principal-a1.rational_model_principal-a1.infinity_place-a1`
- Child key: `reciprocal_presentation`
- Declaration: `Submission.p06_9e0f5043ff_inf_reciprocal_presentation`
- Exact Lean type: `∀ (K : Type*) [Field K], Transcendental K ((algebraMap (Polynomial K) (FractionRing (Polynomial K)) Polynomial.X)⁻¹) ∧ (∀ f : FractionRing (Polynomial K), ∃ a b : Polynomial K, b ≠ 0 ∧ f = Polynomial.aeval ((algebraMap (Polynomial K) (FractionRing (Polynomial K)) Polynomial.X)⁻¹) a / Polynomial.aeval ((algebraMap (Polynomial K) (FractionRing (Polynomial K)) Polynomial.X)⁻¹) b)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
