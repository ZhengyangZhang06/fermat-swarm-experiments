# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.frobenius_approximation-a1.finite_frobenius-a1.finite_inertia_exclusion-a1.conjugate_separation-a1.integer_root_product-a1.squared_vandermonde_symmetric-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/nodes/root-frobenius-approximation-a1-finite-frobenius-a1-finite-inertia-ex-d841158b2d/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.frobenius_approximation-a1.finite_frobenius-a1.finite_inertia_exclusion-a1.conjugate_separation-a1.integer_root_product-a1`
- Child key: `squared_vandermonde_symmetric`
- Declaration: `Submission.p09_af497904fe_irp_squared_vandermonde_symmetric`
- Exact Lean type: `∀ n : ℕ, MvPolynomial.IsSymmetric ((Finset.univ.filter (fun ij : Fin n × Fin n => ij.1 < ij.2)).prod (fun ij => ((MvPolynomial.X ij.1 : MvPolynomial (Fin n) ℤ) - MvPolynomial.X ij.2) ^ 2))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
