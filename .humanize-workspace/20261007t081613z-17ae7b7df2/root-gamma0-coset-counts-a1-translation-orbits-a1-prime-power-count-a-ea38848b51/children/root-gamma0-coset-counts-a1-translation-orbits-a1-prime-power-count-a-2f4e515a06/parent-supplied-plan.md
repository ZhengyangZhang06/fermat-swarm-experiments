# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.gamma0_coset_counts-a1.translation_orbits-a1.prime_power_count-a1.fractional_iterates-a1.square_annihilation-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/nodes/root-gamma0-coset-counts-a1-translation-orbits-a1-prime-power-count-a-2f4e515a06/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.gamma0_coset_counts-a1.translation_orbits-a1.prime_power_count-a1.fractional_iterates-a1`
- Child key: `square_annihilation`
- Declaration: `Submission.p10_17ae7b7d_fi_square_annihilation`
- Exact Lean type: `∀ (p a j : ℕ), Nat.Prime p → j < a → ∀ z : ZMod (p ^ a), p ^ j ∣ z.val → ¬ p ^ (j + 1) ∣ z.val → ∀ n : ℕ, ((n : ZMod (p ^ a)) * z ^ 2 = 0 ↔ p ^ (a - 2 * j) ∣ n)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
