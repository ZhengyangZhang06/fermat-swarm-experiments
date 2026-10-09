# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.frobenius_approximation-a1.finite_frobenius-a1.finite_inertia_exclusion-a1.conjugate_separation-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/nodes/root-frobenius-approximation-a1-finite-frobenius-a1-finite-inertia-ex-bbbc8f8ea4/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.frobenius_approximation-a1.finite_frobenius-a1.finite_inertia_exclusion-a1`
- Child key: `conjugate_separation`
- Declaration: `Submission.p09_af497904fe_fie_conjugate_separation`
- Exact Lean type: `∀ (E : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ E] [IsGalois ℚ E] (α : E), IsIntegral ℤ α → ∃ D : ℤ, D ≠ 0 ∧ ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ D.natAbs → ∀ V : ValuationSubring E, V.LiesOverPrime ℓ → (∀ σ : E ≃ₐ[ℚ] E, σ α ∈ V) ∧ ∀ σ τ : E ≃ₐ[ℚ] E, σ α - τ α ∈ V.nonunits → σ α = τ α`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
