# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.frobenius_approximation-a1.finite_frobenius-a1.cyclotomic_frobenius_supply-a1.counting_mellin_continuation-a1.floor_remainder_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/nodes/root-frobenius-approximation-a1-finite-frobenius-a1-cyclotomic-froben-770f2306a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.frobenius_approximation-a1.finite_frobenius-a1.cyclotomic_frobenius_supply-a1.counting_mellin_continuation-a1`
- Child key: `floor_remainder_bound`
- Declaration: `Submission.p09_af497904fe_cmc_40fde013_floor_remainder`
- Exact Lean type: `∀ (a : ℕ → ℝ) (κ α C : ℝ), 0 ≤ α → 0 ≤ C → (∀ n : ℕ, 1 ≤ n → |(∑ k ∈ Finset.Icc 1 n, a k) - κ * (n : ℝ)| ≤ C * (n : ℝ) ^ α) → Measurable (fun t : ℝ => (∑ k ∈ Finset.Icc 1 (Nat.floor t), a k) - κ * t) ∧ ∀ t : ℝ, 1 ≤ t → |(∑ k ∈ Finset.Icc 1 (Nat.floor t), a k) - κ * t| ≤ (C + |κ|) * t ^ α`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
