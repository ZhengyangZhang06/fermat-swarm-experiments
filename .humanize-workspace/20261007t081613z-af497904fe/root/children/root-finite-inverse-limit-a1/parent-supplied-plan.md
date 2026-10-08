# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.finite_inverse_limit-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/nodes/root-finite-inverse-limit-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root`
- Child key: `finite_inverse_limit`
- Declaration: `Submission.p09_af497904fe_finite_inverse_limit`
- Exact Lean type: `∀ (X : ℕ → Type) [∀ i : ℕ, Finite (X i)] [∀ i : ℕ, Nonempty (X i)] (r : ∀ i j : ℕ, i ≤ j → X j → X i), (∀ (i : ℕ) (x : X i), r i i (Nat.le_refl i) x = x) → (∀ (i j k : ℕ) (hij : i ≤ j) (hjk : j ≤ k) (x : X k), r i k (Nat.le_trans hij hjk) x = r i j hij (r j k hjk x)) → ∃ x : ∀ i : ℕ, X i, ∀ (i j : ℕ) (hij : i ≤ j), r i j hij (x j) = x i`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
