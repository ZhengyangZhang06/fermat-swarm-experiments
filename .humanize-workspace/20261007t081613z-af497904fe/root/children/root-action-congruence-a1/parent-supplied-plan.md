# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.action_congruence-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081613Z-af497904fe/nodes/root-action-congruence-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root`
- Child key: `action_congruence`
- Declaration: `Submission.p09_af497904fe_action_congruence`
- Exact Lean type: `∀ {C M : Type} [CommRing C] [AddCommGroup M] [Module C M] (J : Ideal C) (U : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Module.End C M) (F : IntermediateField ℚ (AlgebraicClosure ℚ)), (∀ δ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ F, δ x = x) → ∀ y : M, U δ y - y ∈ J • (⊤ : Submodule C M)) → ∀ σ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ F, σ x = τ x) → ∀ y : M, (U σ - U τ) y ∈ J • (⊤ : Submodule C M)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
