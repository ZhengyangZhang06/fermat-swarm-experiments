# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.frobenius_approximation-a1.finite_frobenius-a1.cyclotomic_frobenius_supply-a1.counting_mellin_continuation-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/nodes/root-frobenius-approximation-a1-finite-frobenius-a1-cyclotomic-froben-8abc0f62c4/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.frobenius_approximation-a1.finite_frobenius-a1.cyclotomic_frobenius_supply-a1`
- Child key: `counting_mellin_continuation`
- Declaration: `Submission.p09_af497904fe_cfs_counting_mellin_continuation`
- Exact Lean type: `∀ (a : ℕ → ℝ) (κ α : ℝ), (∀ n : ℕ, 0 ≤ a n) → 0 ≤ α → α < 1 → (∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 1 ≤ n → |(∑ k ∈ Finset.Icc 1 n, a k) - κ * (n : ℝ)| ≤ C * (n : ℝ) ^ α) → ∃ H : ℂ → ℂ, DifferentiableOn ℂ H {s : ℂ | α < s.re} ∧ ∀ s : ℂ, 1 < s.re → LSeries (fun n : ℕ => (a n : ℂ)) s = (κ : ℂ) / (s - 1) + H s`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
