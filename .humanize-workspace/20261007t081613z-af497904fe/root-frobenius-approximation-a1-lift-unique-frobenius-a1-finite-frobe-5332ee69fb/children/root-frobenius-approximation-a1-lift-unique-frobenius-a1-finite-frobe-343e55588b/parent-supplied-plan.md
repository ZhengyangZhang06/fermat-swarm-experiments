# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.frobenius_approximation-a1.lift_unique_frobenius-a1.finite_frobenius_exists-a1.localized_frobenius-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/nodes/root-frobenius-approximation-a1-lift-unique-frobenius-a1-finite-frobe-343e55588b/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.frobenius_approximation-a1.lift_unique_frobenius-a1.finite_frobenius_exists-a1`
- Child key: `localized_frobenius`
- Declaration: `Submission.p09_af497904fe_ffe_localized_frobenius`
- Exact Lean type: `∀ (E : IntermediateField ℚ (AlgebraicClosure ℚ)) (ℓ : ℕ), ℓ.Prime → ∀ (V : ValuationSubring E) (q : Ideal (NumberField.RingOfIntegers E)), q.IsPrime → (∀ x : E, x ∈ V ↔ ∃ a b : NumberField.RingOfIntegers E, b ∉ q ∧ x = (a : E) / (b : E)) → (∀ a : NumberField.RingOfIntegers E, (a : E) ∈ V.nonunits ↔ a ∈ q) → ∀ g : E ≃ₐ[ℚ] E, (∀ a : NumberField.RingOfIntegers E, NumberField.RingOfIntegers.mapRingEquiv g.toRingEquiv a - a ^ ℓ ∈ q) → V.IsFrobeniusAt g ℓ`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
