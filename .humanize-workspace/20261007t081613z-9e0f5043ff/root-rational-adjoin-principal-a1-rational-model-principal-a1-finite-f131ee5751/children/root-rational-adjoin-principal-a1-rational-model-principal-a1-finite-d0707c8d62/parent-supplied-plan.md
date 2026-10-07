# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.rational_adjoin_principal-a1.rational_model_principal-a1.finite_place_model-a1.exists_local_place-a1.integer_order-a1.polynomial_exponent-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-rational-adjoin-principal-a1-rational-model-principal-a1-finite-d0707c8d62/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.rational_adjoin_principal-a1.rational_model_principal-a1.finite_place_model-a1.exists_local_place-a1.integer_order-a1`
- Child key: `polynomial_exponent`
- Declaration: `Submission.p06_9e0f5043ff_io_polynomial_exponent`
- Exact Lean type: `∀ (K : Type*) [Field K] (q : Polynomial K), q.Monic → Irreducible q → ∃ μ : Polynomial K → ℕ, μ 1 = 0 ∧ μ q = 1 ∧ (∀ a b : Polynomial K, a ≠ 0 → b ≠ 0 → μ (a * b) = μ a + μ b) ∧ (∀ a : Polynomial K, a ≠ 0 → (μ a = 0 ↔ ¬ q ∣ a)) ∧ (∀ a : Polynomial K, a ≠ 0 → ∃ a₀ : Polynomial K, a₀ ≠ 0 ∧ ¬ q ∣ a₀ ∧ a = q ^ μ a * a₀)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
