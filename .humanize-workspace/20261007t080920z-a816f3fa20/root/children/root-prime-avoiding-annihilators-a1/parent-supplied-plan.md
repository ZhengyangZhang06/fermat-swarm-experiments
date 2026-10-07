# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.prime_avoiding_annihilators-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T080920Z-a816f3fa20/nodes/root-prime-avoiding-annihilators-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root`
- Child key: `prime_avoiding_annihilators`
- Declaration: `Submission.p04_eq_zero_of_prime_avoiding_annihilators`
- Exact Lean type: `∀ {V : Type*} [AddCommGroup V], (∀ p : ℕ, p.Prime → ∃ m : ℕ, 0 < m ∧ ¬ p ∣ m ∧ ∀ v : V, m • v = 0) → ∀ v : V, v = 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
