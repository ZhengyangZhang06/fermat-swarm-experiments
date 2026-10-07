# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.rational_adjoin_principal-a1.rational_model_principal-a1.finite_place_model-a1.normalized_orders-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-rational-adjoin-principal-a1-rational-model-principal-a1-finite-654f5e977f/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.rational_adjoin_principal-a1.rational_model_principal-a1.finite_place_model-a1`
- Child key: `normalized_orders`
- Declaration: `Submission.p06_9e0f5043ff_fpm_normalized_orders`
- Exact Lean type: `∀ (K F : Type*) [Field K] [Field F] [Algebra K F] (x : F), Transcendental K x → ∀ q : Polynomial K, q.Monic → Irreducible q → ∀ v : AlgebraicCurve.Place K F, (∀ f : F, f ∈ v.toValuationSubring ↔ ∃ a b : Polynomial K, ¬ q ∣ b ∧ f = Polynomial.aeval x a / Polynomial.aeval x b) → v.ord (Polynomial.aeval x q) = 1 ∧ (∀ a : Polynomial K, ¬ q ∣ a → v.ord (Polynomial.aeval x a) = 0)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
