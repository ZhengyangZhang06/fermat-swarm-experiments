# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.petersson_core_good_hecke-a1.hecke_integral_adjointness-a1.good_prime_transversal-a1.unique_projective_index-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081614Z-f036cc6b1f/nodes/root-petersson-core-good-hecke-a1-hecke-integral-adjointness-a1-good-4a18d4f43e/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.petersson_core_good_hecke-a1.hecke_integral_adjointness-a1.good_prime_transversal-a1`
- Child key: `unique_projective_index`
- Declaration: `Submission.f036cc6b1f_pc_hi_gpt_unique_projective_index`
- Exact Lean type: `∀ (p : ℕ), p.Prime → ∀ (a b v : ℤ), (¬ (p : ℤ) ∣ a ∨ ¬ (p : ℤ) ∣ b) → ¬ (p : ℤ) ∣ v → ∃! i : Fin (p + 1), (p : ℤ) ∣ (if i.val < p then b - a * (i.val : ℤ) else a * v + b * (p : ℤ))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
