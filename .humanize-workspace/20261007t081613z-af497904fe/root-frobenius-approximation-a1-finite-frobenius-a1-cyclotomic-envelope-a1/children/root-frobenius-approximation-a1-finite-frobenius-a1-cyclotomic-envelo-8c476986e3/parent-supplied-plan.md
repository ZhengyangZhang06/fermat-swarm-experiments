# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.frobenius_approximation-a1.finite_frobenius-a1.cyclotomic_envelope-a1.compositum_pair-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/nodes/root-frobenius-approximation-a1-finite-frobenius-a1-cyclotomic-envelo-8c476986e3/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.frobenius_approximation-a1.finite_frobenius-a1.cyclotomic_envelope-a1`
- Child key: `compositum_pair`
- Declaration: `Submission.p09_af497904fe_ce_compositum_pair`
- Exact Lean type: `∀ (E C : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ E] [IsGalois ℚ E] [FiniteDimensional ℚ C] [IsGalois ℚ C], E ⊓ C = ⊥ → ∀ (g : E ≃ₐ[ℚ] E) (a : C ≃ₐ[ℚ] C), ∃! h : ↥(E ⊔ C) ≃ₐ[ℚ] ↥(E ⊔ C), (∀ x : E, h (IntermediateField.inclusion (show E ≤ E ⊔ C from le_sup_left) x) = IntermediateField.inclusion (show E ≤ E ⊔ C from le_sup_left) (g x)) ∧ (∀ y : C, h (IntermediateField.inclusion (show C ≤ E ⊔ C from le_sup_right) y) = IntermediateField.inclusion (show C ≤ E ⊔ C from le_sup_right) (a y))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
