# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.frobenius_approximation-a1.finite_frobenius-a1.finite_inertia_exclusion-a1.conjugate_separation-a1.valuation_product_separation-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/nodes/root-frobenius-approximation-a1-finite-frobenius-a1-finite-inertia-ex-92c23e72d0/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.frobenius_approximation-a1.finite_frobenius-a1.finite_inertia_exclusion-a1.conjugate_separation-a1`
- Child key: `valuation_product_separation`
- Declaration: `Submission.p09_af497904fe_cs_valuation_product_separation`
- Exact Lean type: `∀ {K : Type} [Field K] (n : ℕ) (β : Fin n → K) (D : ℤ), (∀ i : Fin n, IsIntegral ℤ (β i)) → (D : K) = (Finset.univ.filter (fun ij : Fin n × Fin n => ij.1 < ij.2)).prod (fun ij => (β ij.1 - β ij.2) ^ 2) → ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ D.natAbs → ∀ V : ValuationSubring K, V.LiesOverPrime ℓ → (∀ i : Fin n, β i ∈ V) ∧ ∀ i j : Fin n, β i - β j ∈ V.nonunits → β i = β j`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
