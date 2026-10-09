# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.finite_cyclotomic_character-a1.character_finite_action-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/nodes/root-finite-cyclotomic-character-a1-character-finite-action-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.finite_cyclotomic_character-a1`
- Child key: `character_finite_action`
- Declaration: `Submission.p09_af497904fe_fcc_character_finite_action`
- Exact Lean type: `∀ (N : ℕ) [NeZero N], ∃ (χ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (ZMod N)ˣ) (F : IntermediateField ℚ (AlgebraicClosure ℚ)), FiniteDimensional ℚ F ∧ (∀ σ τ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), (∀ x ∈ F, σ x = τ x) → χ σ = χ τ) ∧ (∀ (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (ζ : AlgebraicClosure ℚ), ζ ^ N = 1 → σ ζ = ζ ^ ((χ σ : ZMod N).val))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
