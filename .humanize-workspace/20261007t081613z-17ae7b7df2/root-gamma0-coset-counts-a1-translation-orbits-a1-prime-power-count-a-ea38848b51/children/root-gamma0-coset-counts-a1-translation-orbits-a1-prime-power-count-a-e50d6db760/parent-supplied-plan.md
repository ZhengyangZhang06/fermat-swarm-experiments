# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.gamma0_coset_counts-a1.translation_orbits-a1.prime_power_count-a1.fractional_iterates-a1.unit_iterate_formula-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/nodes/root-gamma0-coset-counts-a1-translation-orbits-a1-prime-power-count-a-e50d6db760/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.gamma0_coset_counts-a1.translation_orbits-a1.prime_power_count-a1.fractional_iterates-a1`
- Child key: `unit_iterate_formula`
- Declaration: `Submission.p10_17ae7b7d_fi_unit_iterate_formula`
- Exact Lean type: `∀ (p a : ℕ), Nat.Prime p → 1 ≤ a → ∀ z : ZMod (p ^ a), p ∣ z.val → let F : ZMod (p ^ a) → ZMod (p ^ a) := fun w => w * (1 + w)⁻¹; ∀ n : ℕ, IsUnit (1 + (n : ZMod (p ^ a)) * z) ∧ (F^[n]) z = z * (1 + (n : ZMod (p ^ a)) * z)⁻¹`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
