# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.gamma0_coset_counts-a1.translation_orbits-a1.coprime_count_mul-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081613Z-17ae7b7df2/nodes/root-gamma0-coset-counts-a1-translation-orbits-a1-coprime-count-mul-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.gamma0_coset_counts-a1.translation_orbits-a1`
- Child key: `coprime_count_mul`
- Declaration: `Submission.p10_17ae7b7d_to_coprime_count_mul`
- Exact Lean type: `∀ (m n : ℕ) [NeZero m] [NeZero n], Nat.Coprime m n → Nat.card (Quotient (MulAction.orbitRel (Subgroup.zpowers ModularGroup.T) ((Matrix.SpecialLinearGroup (Fin 2) ℤ) ⧸ CongruenceSubgroup.Gamma0 (m * n)))) = Nat.card (Quotient (MulAction.orbitRel (Subgroup.zpowers ModularGroup.T) ((Matrix.SpecialLinearGroup (Fin 2) ℤ) ⧸ CongruenceSubgroup.Gamma0 m))) * Nat.card (Quotient (MulAction.orbitRel (Subgroup.zpowers ModularGroup.T) ((Matrix.SpecialLinearGroup (Fin 2) ℤ) ⧸ CongruenceSubgroup.Gamma0 n)))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
