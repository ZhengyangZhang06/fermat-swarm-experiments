# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.primitive_parabolic-a1.integral_parabolic_normal_form-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/nodes/root-primitive-parabolic-a1-integral-parabolic-normal-form-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.primitive_parabolic-a1`
- Child key: `integral_parabolic_normal_form`
- Declaration: `Submission.p02_es_177ebb5a_pp_integral_parabolic_normal_form`
- Exact Lean type: `∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, (γ : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4 → ∃ (σ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (m : ℤ), σ⁻¹ * γ * σ = ModularGroup.T ^ m ∨ σ⁻¹ * γ * σ = -(ModularGroup.T ^ m)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
