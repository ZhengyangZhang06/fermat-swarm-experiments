# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.frobenius_approximation-a1.finite_frobenius-a1.cyclotomic_envelope-a1.fixed_field_generator-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/nodes/root-frobenius-approximation-a1-finite-frobenius-a1-cyclotomic-envelo-30ceb26819/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.frobenius_approximation-a1.finite_frobenius-a1.cyclotomic_envelope-a1`
- Child key: `fixed_field_generator`
- Declaration: `Submission.p09_af497904fe_ce_fixed_field_generator`
- Exact Lean type: `∀ (M : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ M] [IsGalois ℚ M] (u : M ≃ₐ[ℚ] M) (ζ : M), (∀ n : ℕ, (u ^ n) ζ = ζ → u ^ n = 1) → ∃ (F : IntermediateField ℚ M) (h : M ≃ₐ[F] M), IntermediateField.adjoin F ({ζ} : Set M) = ⊤ ∧ ∀ x : M, h x = u x`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
