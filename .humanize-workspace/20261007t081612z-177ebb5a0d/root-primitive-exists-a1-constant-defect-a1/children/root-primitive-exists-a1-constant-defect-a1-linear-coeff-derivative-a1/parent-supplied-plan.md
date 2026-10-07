# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.primitive_exists-a1.constant_defect-a1.linear_coeff_derivative-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/nodes/root-primitive-exists-a1-constant-defect-a1-linear-coeff-derivative-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.primitive_exists-a1.constant_defect-a1`
- Child key: `linear_coeff_derivative`
- Declaration: `Submission.p02_es_177ebb5a_cd_linear_coeff_derivative`
- Exact Lean type: `∀ (n : ℕ) (A : ↥(HeckeEis.BinaryForm ℂ n) →ₗ[ℂ] ↥(HeckeEis.BinaryForm ℂ n)) (F : ℂ → ↥(HeckeEis.BinaryForm ℂ n)) (P : ↥(HeckeEis.BinaryForm ℂ n)) (z : ℂ), (∀ e : Fin 2 →₀ ℕ, HasDerivAt (fun w : ℂ => MvPolynomial.coeff e (F w).val) (MvPolynomial.coeff e P.val) z) → ∀ e : Fin 2 →₀ ℕ, HasDerivAt (fun w : ℂ => MvPolynomial.coeff e (A (F w)).val) (MvPolynomial.coeff e (A P).val) z`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
