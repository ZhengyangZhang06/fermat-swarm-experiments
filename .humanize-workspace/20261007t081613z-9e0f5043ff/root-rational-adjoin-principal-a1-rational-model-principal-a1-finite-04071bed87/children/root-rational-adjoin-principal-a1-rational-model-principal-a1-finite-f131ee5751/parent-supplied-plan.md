# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.rational_adjoin_principal-a1.rational_model_principal-a1.finite_place_model-a1.exists_local_place-a1.integer_order-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-rational-adjoin-principal-a1-rational-model-principal-a1-finite-f131ee5751/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.rational_adjoin_principal-a1.rational_model_principal-a1.finite_place_model-a1.exists_local_place-a1`
- Child key: `integer_order`
- Declaration: `Submission.p06_9e0f5043ff_elp_integer_order`
- Exact Lean type: `∀ (K F : Type*) [Field K] [Field F] [Algebra K F] (x : F), Transcendental K x → (∀ f : F, ∃ a b : Polynomial K, b ≠ 0 ∧ f = Polynomial.aeval x a / Polynomial.aeval x b) → ∀ q : Polynomial K, q.Monic → Irreducible q → ∃ ν : F → ℤ, ν 0 = 0 ∧ ν (Polynomial.aeval x q) = 1 ∧ (∀ f g : F, f ≠ 0 → g ≠ 0 → ν (f / g) = ν f - ν g) ∧ (∀ f : F, f ≠ 0 → (0 ≤ ν f ↔ ∃ a b : Polynomial K, ¬ q ∣ b ∧ f = Polynomial.aeval x a / Polynomial.aeval x b))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
