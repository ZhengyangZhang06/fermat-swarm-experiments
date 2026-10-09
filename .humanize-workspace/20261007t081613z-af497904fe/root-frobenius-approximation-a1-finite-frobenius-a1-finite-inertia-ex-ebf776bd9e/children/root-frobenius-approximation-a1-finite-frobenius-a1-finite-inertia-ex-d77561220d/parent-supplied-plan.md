# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.frobenius_approximation-a1.finite_frobenius-a1.finite_inertia_exclusion-a1.conjugate_separation-a1.integer_root_product-a1.minpoly_roots-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/nodes/root-frobenius-approximation-a1-finite-frobenius-a1-finite-inertia-ex-d77561220d/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.frobenius_approximation-a1.finite_frobenius-a1.finite_inertia_exclusion-a1.conjugate_separation-a1.integer_root_product-a1`
- Child key: `minpoly_roots`
- Declaration: `Submission.p09_af497904fe_irp_minpoly_roots`
- Exact Lean type: `∀ (E : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ E] [IsGalois ℚ E] (α : E), IsIntegral ℤ α → ∃ (n : ℕ) (β : Fin n → E), Function.Injective β ∧ (∀ i : Fin n, IsIntegral ℤ (β i)) ∧ (∀ σ : E ≃ₐ[ℚ] E, ∃ i : Fin n, β i = σ α) ∧ (minpoly ℤ α).map (Int.castRingHom E) = Finset.univ.prod (fun i : Fin n => Polynomial.X - Polynomial.C (β i))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
