# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.frobenius_approximation-a1.finite_frobenius-a1.cyclotomic_frobenius_supply-a1.cyclic_weighted_infinitude-a1.character_orthogonality-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/nodes/root-frobenius-approximation-a1-finite-frobenius-a1-cyclotomic-froben-b7ef89564d/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.frobenius_approximation-a1.finite_frobenius-a1.cyclotomic_frobenius_supply-a1.cyclic_weighted_infinitude-a1`
- Child key: `character_orthogonality`
- Declaration: `Submission.p09_af497904fe_cwi_character_orthogonality`
- Exact Lean type: `∀ (m : ℕ) (ω : ℂ), 0 < m → IsPrimitiveRoot ω m → ∀ a b : ZMod m, (∑ k : Fin m, star (ω ^ (k.val * a.val)) * ω ^ (k.val * b.val)) = (if b = a then (m : ℂ) else 0)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
