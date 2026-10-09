# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.frobenius_approximation-a1.lift_unique_frobenius-a1.frobenius_tower_limit-a1.compatible_automorphisms_glue-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/nodes/root-frobenius-approximation-a1-lift-unique-frobenius-a1-frobenius-to-ca1f9132b3/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.frobenius_approximation-a1.lift_unique_frobenius-a1.frobenius_tower_limit-a1`
- Child key: `compatible_automorphisms_glue`
- Declaration: `Submission.p09_af497904fe_ftl_compatible_automorphisms_glue`
- Exact Lean type: `∀ (F : ℕ → IntermediateField ℚ (AlgebraicClosure ℚ)) (hmono : Monotone F), (∀ x : AlgebraicClosure ℚ, ∃ i : ℕ, x ∈ F i) → ∀ g : (i : ℕ) → F i ≃ₐ[ℚ] F i, (∀ (i j : ℕ) (hij : i ≤ j) (x : F i), IntermediateField.inclusion (hmono hij) (g i x) = g j (IntermediateField.inclusion (hmono hij) x)) → ∃ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ (i : ℕ) (x : F i), τ (x : AlgebraicClosure ℚ) = ((g i x : F i) : AlgebraicClosure ℚ)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
