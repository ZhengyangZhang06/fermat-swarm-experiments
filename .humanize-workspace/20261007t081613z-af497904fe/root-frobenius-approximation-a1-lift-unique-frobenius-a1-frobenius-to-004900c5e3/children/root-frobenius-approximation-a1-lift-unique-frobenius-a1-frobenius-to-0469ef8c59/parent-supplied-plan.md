# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.frobenius_approximation-a1.lift_unique_frobenius-a1.frobenius_tower_limit-a1.normal_frobenius_restriction-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/nodes/root-frobenius-approximation-a1-lift-unique-frobenius-a1-frobenius-to-0469ef8c59/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.frobenius_approximation-a1.lift_unique_frobenius-a1.frobenius_tower_limit-a1`
- Child key: `normal_frobenius_restriction`
- Declaration: `Submission.p09_af497904fe_ftl_normal_frobenius_restriction`
- Exact Lean type: `∀ (E F : IntermediateField ℚ (AlgebraicClosure ℚ)) [IsGalois ℚ E] (hEF : E ≤ F) (V : ValuationSubring E) (W : ValuationSubring F) (ℓ : ℕ), (∀ x : E, IntermediateField.inclusion hEF x ∈ W ↔ x ∈ V) → ∀ g : F ≃ₐ[ℚ] F, W.IsFrobeniusAt g ℓ → ∃! e : E ≃ₐ[ℚ] E, V.IsFrobeniusAt e ℓ ∧ ∀ x : E, IntermediateField.inclusion hEF (e x) = g (IntermediateField.inclusion hEF x)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
