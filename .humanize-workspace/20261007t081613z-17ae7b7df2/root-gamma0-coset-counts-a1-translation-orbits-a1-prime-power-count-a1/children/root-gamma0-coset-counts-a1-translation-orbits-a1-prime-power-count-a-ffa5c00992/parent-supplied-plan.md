# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.gamma0_coset_counts-a1.translation_orbits-a1.prime_power_count-a1.translation_charts-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/nodes/root-gamma0-coset-counts-a1-translation-orbits-a1-prime-power-count-a-ffa5c00992/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.gamma0_coset_counts-a1.translation_orbits-a1.prime_power_count-a1`
- Child key: `translation_charts`
- Declaration: `Submission.p10_17ae7b7d_pp_translation_charts`
- Exact Lean type: `∀ (p a : ℕ), Nat.Prime p → 1 ≤ a → let R := ZMod (p ^ a); let Q := (Matrix.SpecialLinearGroup (Fin 2) ℤ) ⧸ CongruenceSubgroup.Gamma0 (p ^ a); ∃ e : Q ≃ (R ⊕ {z : R // p ∣ z.val}), (∀ t : R, e (ModularGroup.T⁻¹ • e.symm (Sum.inl t)) = Sum.inl (t + 1)) ∧ (∀ z : {z : R // p ∣ z.val}, ∃ w : {z : R // p ∣ z.val}, e (ModularGroup.T⁻¹ • e.symm (Sum.inr z)) = Sum.inr w ∧ w.1 = z.1 * (1 + z.1)⁻¹)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
