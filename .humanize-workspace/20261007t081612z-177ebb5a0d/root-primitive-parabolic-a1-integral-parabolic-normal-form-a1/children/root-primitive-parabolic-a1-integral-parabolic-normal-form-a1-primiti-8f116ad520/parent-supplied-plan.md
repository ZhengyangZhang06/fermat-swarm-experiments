# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.primitive_parabolic-a1.integral_parabolic_normal_form-a1.primitive_eigenvector_triangular-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/nodes/root-primitive-parabolic-a1-integral-parabolic-normal-form-a1-primiti-8f116ad520/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.primitive_parabolic-a1.integral_parabolic_normal_form-a1`
- Child key: `primitive_eigenvector_triangular`
- Declaration: `Submission.p02_es_177ebb5a_pnf_primitive_eigenvector_triangular`
- Exact Lean type: `∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (ε p q : ℤ), ε ^ 2 = 1 → IsCoprime p q → (γ : Matrix (Fin 2) (Fin 2) ℤ).mulVec ![p, q] = ![ε * p, ε * q] → ∃ (σ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (b : ℤ), (σ⁻¹ * γ * σ : Matrix.SpecialLinearGroup (Fin 2) ℤ).val = Matrix.of ![![ε, b], ![0, ε]]`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
