# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.frobenius_approximation-a1.finite_frobenius-a1.cyclotomic_envelope-a1.cyclotomic_intersection-a1.unramified_subfield-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/nodes/root-frobenius-approximation-a1-finite-frobenius-a1-cyclotomic-envelo-828e01d221/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.frobenius_approximation-a1.finite_frobenius-a1.cyclotomic_envelope-a1.cyclotomic_intersection-a1`
- Child key: `unramified_subfield`
- Declaration: `Submission.p09_af497904fe_ci_unramified_subfield`
- Exact Lean type: `∀ (E D : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ E] [FiniteDimensional ℚ D] (q : ℕ), q.Prime → D ≤ E → (∀ P : Ideal (NumberField.RingOfIntegers E), P.IsPrime → P.LiesOver (Ideal.span {(q : ℤ)}) → Ideal.ramificationIdx P ℤ = 1) → ∀ R : Ideal (NumberField.RingOfIntegers D), R.IsPrime → R.LiesOver (Ideal.span {(q : ℤ)}) → Ideal.ramificationIdx R ℤ = 1`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
