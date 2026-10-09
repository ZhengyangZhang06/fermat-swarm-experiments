# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.frobenius_approximation-a1.finite_frobenius-a1.cyclotomic_frobenius_supply-a1.cyclic_weighted_infinitude-a1.infinite_diff_of_log_lower_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/nodes/root-frobenius-approximation-a1-finite-frobenius-a1-cyclotomic-froben-2d78b4ea16/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.frobenius_approximation-a1.finite_frobenius-a1.cyclotomic_frobenius_supply-a1.cyclic_weighted_infinitude-a1`
- Child key: `infinite_diff_of_log_lower_bound`
- Declaration: `Submission.p09_af497904fe_cwi_infinite_diff_of_log_lower_bound`
- Exact Lean type: `∀ (ι : Type) (N : ι → ℕ) (E D : Set ι) (c K ε C : ℝ), (∀ i : ι, 2 ≤ N i) → (∀ s : ℝ, 1 < s → Summable (fun i : ι => Real.rpow (N i : ℝ) (-s))) → 0 < c → 0 < ε → ε ≤ 1 → (∀ s : ℝ, 1 < s → s < 1 + ε → c * Real.log (1 / (s - 1)) - K ≤ ∑' i : {i : ι // i ∈ E}, Real.rpow (N i.1 : ℝ) (-s)) → (∀ s : ℝ, 1 < s → s < 2 → (∑' i : {i : ι // i ∈ D}, Real.rpow (N i.1 : ℝ) (-s)) ≤ C) → Set.Infinite (E \ D)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
