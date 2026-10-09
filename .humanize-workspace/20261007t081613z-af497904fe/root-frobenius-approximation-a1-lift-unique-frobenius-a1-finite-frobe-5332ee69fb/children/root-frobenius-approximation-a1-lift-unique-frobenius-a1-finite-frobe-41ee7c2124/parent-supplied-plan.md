# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.frobenius_approximation-a1.lift_unique_frobenius-a1.finite_frobenius_exists-a1.prime_frobenius_congruence-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/nodes/root-frobenius-approximation-a1-lift-unique-frobenius-a1-finite-frobe-41ee7c2124/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.frobenius_approximation-a1.lift_unique_frobenius-a1.finite_frobenius_exists-a1`
- Child key: `prime_frobenius_congruence`
- Declaration: `Submission.p09_af497904fe_ffe_prime_frobenius_congruence`
- Exact Lean type: `∀ (E : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ E] [IsGalois ℚ E] (ℓ : ℕ), ℓ.Prime → ∀ q : Ideal (NumberField.RingOfIntegers E), q.IsPrime → (ℓ : NumberField.RingOfIntegers E) ∈ q → Finite (NumberField.RingOfIntegers E ⧸ q) → ∃ g : E ≃ₐ[ℚ] E, ∀ a : NumberField.RingOfIntegers E, NumberField.RingOfIntegers.mapRingEquiv g.toRingEquiv a - a ^ ℓ ∈ q`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
