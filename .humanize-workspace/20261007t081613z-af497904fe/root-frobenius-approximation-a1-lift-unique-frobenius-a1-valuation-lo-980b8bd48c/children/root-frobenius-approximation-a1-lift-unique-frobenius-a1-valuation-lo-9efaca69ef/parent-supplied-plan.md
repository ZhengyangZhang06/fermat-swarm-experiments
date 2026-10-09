# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.frobenius_approximation-a1.lift_unique_frobenius-a1.valuation_localization-a1.integral_center-a1.integer_mem_valuation-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/nodes/root-frobenius-approximation-a1-lift-unique-frobenius-a1-valuation-lo-9efaca69ef/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.frobenius_approximation-a1.lift_unique_frobenius-a1.valuation_localization-a1.integral_center-a1`
- Child key: `integer_mem_valuation`
- Declaration: `Submission.p09_af497904fe_ic_integer_mem_valuation`
- Exact Lean type: `∀ (E : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ E] (V : ValuationSubring E), ∀ a : NumberField.RingOfIntegers E, (a : E) ∈ V`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
