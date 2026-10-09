# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.frobenius_approximation-a1.finite_frobenius-a1.cyclotomic_frobenius_supply-a1.counting_mellin_continuation-a1.mellin_tail_holomorphic-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/nodes/root-frobenius-approximation-a1-finite-frobenius-a1-cyclotomic-froben-2b914784f7/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.frobenius_approximation-a1.finite_frobenius-a1.cyclotomic_frobenius_supply-a1.counting_mellin_continuation-a1`
- Child key: `mellin_tail_holomorphic`
- Declaration: `Submission.p09_af497904fe_cmc_40fde013_mellin_tail_holomorphic`
- Exact Lean type: `∀ (R : ℝ → ℝ) (α M : ℝ), Measurable R → 0 ≤ M → (∀ t : ℝ, 1 ≤ t → |R t| ≤ M * t ^ α) → (∀ s : ℂ, α < s.re → MeasureTheory.IntegrableOn (fun t : ℝ => (R t : ℂ) * (t : ℂ) ^ (-(s + 1))) (Set.Ioi (1 : ℝ))) ∧ DifferentiableOn ℂ (fun s : ℂ => MeasureTheory.integral (μ := MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ))) (fun t : ℝ => (R t : ℂ) * (t : ℂ) ^ (-(s + 1)))) {s : ℂ | α < s.re}`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
