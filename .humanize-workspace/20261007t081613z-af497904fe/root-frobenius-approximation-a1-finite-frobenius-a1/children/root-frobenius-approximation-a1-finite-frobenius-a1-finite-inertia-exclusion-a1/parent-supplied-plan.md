# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.frobenius_approximation-a1.finite_frobenius-a1.finite_inertia_exclusion-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/nodes/root-frobenius-approximation-a1-finite-frobenius-a1-finite-inertia-exclusion-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.frobenius_approximation-a1.finite_frobenius-a1`
- Child key: `finite_inertia_exclusion`
- Declaration: `Submission.p09_af497904fe_ff_finite_inertia_exclusion`
- Exact Lean type: `∀ (E : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ E] [IsGalois ℚ E], ∃ S : Finset ℕ, ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S → ∀ V : ValuationSubring E, V.LiesOverPrime ℓ → ∀ τ : E ≃ₐ[ℚ] E, τ ∈ V.inertiaSubgroupIn ℚ → τ = 1`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
