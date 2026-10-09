# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.frobenius_approximation-a1.lift_unique_frobenius-a1.frobenius_tower_limit-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/nodes/root-frobenius-approximation-a1-lift-unique-frobenius-a1-frobenius-to-004900c5e3/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.frobenius_approximation-a1.lift_unique_frobenius-a1`
- Child key: `frobenius_tower_limit`
- Declaration: `Submission.p09_af497904fe_luf_frobenius_tower_limit`
- Exact Lean type: `∀ (F : ℕ → IntermediateField ℚ (AlgebraicClosure ℚ)) (hmono : Monotone F), (∀ i : ℕ, FiniteDimensional ℚ (F i)) → (∀ i : ℕ, IsGalois ℚ (F i)) → (∀ x : AlgebraicClosure ℚ, ∃ i : ℕ, x ∈ F i) → ∀ (V : (i : ℕ) → ValuationSubring (F i)) (ℓ : ℕ), (∀ i : ℕ, (V i).LiesOverPrime ℓ) → (∀ (i j : ℕ) (hij : i ≤ j) (x : F i), IntermediateField.inclusion (hmono hij) x ∈ V j ↔ x ∈ V i) → (∀ i : ℕ, ∃ g : F i ≃ₐ[ℚ] F i, (V i).IsFrobeniusAt g ℓ) → ∃ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ ∧ (∀ (i : ℕ) (x : F i), (x : AlgebraicClosure ℚ) ∈ P ↔ x ∈ V i) ∧ ∃ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt τ ℓ ∧ ∀ i : ℕ, ∃ g : F i ≃ₐ[ℚ] F i, (V i).IsFrobeniusAt g ℓ ∧ ∀ x : F i, τ (x : AlgebraicClosure ℚ) = ((g x : F i) : AlgebraicClosure ℚ)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
