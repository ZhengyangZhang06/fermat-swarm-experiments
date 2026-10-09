# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.frobenius_approximation-a1.finite_frobenius-a1.cyclotomic_envelope-a1.cyclotomic_intersection-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/nodes/root-frobenius-approximation-a1-finite-frobenius-a1-cyclotomic-envelo-27a1cb7017/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.frobenius_approximation-a1.finite_frobenius-a1.cyclotomic_envelope-a1`
- Child key: `cyclotomic_intersection`
- Declaration: `Submission.p09_af497904fe_ce_cyclotomic_intersection`
- Exact Lean type: `∀ (E : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ E] [IsGalois ℚ E] (q : ℕ) (ζ : AlgebraicClosure ℚ), q.Prime → IsPrimitiveRoot ζ q → (∀ V : ValuationSubring E, V.LiesOverPrime q → ∀ τ : E ≃ₐ[ℚ] E, τ ∈ V.inertiaSubgroupIn ℚ → τ = 1) → E ⊓ IntermediateField.adjoin ℚ ({ζ} : Set (AlgebraicClosure ℚ)) = ⊥`

## Sibling prerequisites

- `root.frobenius_approximation-a1.finite_frobenius-a1.cyclotomic_envelope-a1.inertia_ramification-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
