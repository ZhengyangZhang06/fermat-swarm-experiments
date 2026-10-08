# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tate_uniformization-a1.euler_product_powers-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081613Z-d1a2d75627/nodes/root-tate-uniformization-a1-euler-product-powers-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tate_uniformization-a1`
- Child key: `euler_product_powers`
- Declaration: `Submission.p03_tu_euler_product_powers_68cf3476`
- Exact Lean type: `∀ (F : Type) [NormedField F] [CompleteSpace F], (∀ x y : F, ‖x + y‖ ≤ max ‖x‖ ‖y‖) → ∀ q : F, ‖q‖ < 1 → Multipliable (fun d : ℕ => 1 - q ^ (d + 1)) ∧ (∏' d : ℕ, (1 - q ^ (d + 1))) ≠ 0 ∧ ∀ k : ℕ, Multipliable (fun d : ℕ => (1 - q ^ (d + 1)) ^ k) ∧ (∏' d : ℕ, (1 - q ^ (d + 1)) ^ k) = (∏' d : ℕ, (1 - q ^ (d + 1))) ^ k ∧ (∏' d : ℕ, (1 - q ^ (d + 1)) ^ k) ≠ 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
