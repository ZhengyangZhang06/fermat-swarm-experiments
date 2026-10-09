# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.frobenius_approximation-a1.finite_frobenius-a1.cyclotomic_frobenius_supply-a1.cyclic_weighted_infinitude-a1.fiber_log_estimate-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/nodes/root-frobenius-approximation-a1-finite-frobenius-a1-cyclotomic-froben-23ecfb33e8/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.frobenius_approximation-a1.finite_frobenius-a1.cyclotomic_frobenius_supply-a1.cyclic_weighted_infinitude-a1`
- Child key: `fiber_log_estimate`
- Declaration: `Submission.p09_af497904fe_cwi_fiber_log_estimate`
- Exact Lean type: `∀ (ι : Type) (m : ℕ) (ω : ℂ) (N : ι → ℕ) (g : ι → ZMod m), 0 < m → IsPrimitiveRoot ω m → (∀ i : ι, 2 ≤ N i) → (∀ s : ℝ, 1 < s → Summable (fun i : ι => Real.rpow (N i : ℝ) (-s))) → (∀ k : Fin m, ∃ C : ℝ, 0 ≤ C ∧ ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, 1 < s → s < 1 + ε → ‖(∑' i : ι, ω ^ (k.val * (g i).val) * Complex.ofReal (Real.rpow (N i : ℝ) (-s))) - (if k.val = 0 then (Real.log (1 / (s - 1)) : ℂ) else 0)‖ ≤ C) → ∃ K : ℝ, 0 ≤ K ∧ ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∀ (a : ZMod m) (s : ℝ), 1 < s → s < 1 + ε → |(∑' i : {i : ι // g i = a}, Real.rpow (N i.1 : ℝ) (-s)) - Real.log (1 / (s - 1)) / (m : ℝ)| ≤ K`

## Sibling prerequisites

- `root.frobenius_approximation-a1.finite_frobenius-a1.cyclotomic_frobenius_supply-a1.cyclic_weighted_infinitude-a1.character_orthogonality-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
