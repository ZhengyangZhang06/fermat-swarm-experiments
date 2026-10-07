# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.primitive_exists-a1.constant_defect-a1.linear_coeff_derivative-a1.linear_map_coefficient_expansion-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/nodes/root-primitive-exists-a1-constant-defect-a1-linear-coeff-derivative-a-b4460b2342/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.primitive_exists-a1.constant_defect-a1.linear_coeff_derivative-a1`
- Child key: `linear_map_coefficient_expansion`
- Declaration: `Submission.p02_es_177ebb5a_lcd_coeff_linear_combination`
- Exact Lean type: `∀ (n : ℕ) (A : ↥(HeckeEis.BinaryForm ℂ n) →ₗ[ℂ] ↥(HeckeEis.BinaryForm ℂ n)) (e : Fin 2 →₀ ℕ), ∃ c : Fin (n + 1) → ℂ, ∀ Q : ↥(HeckeEis.BinaryForm ℂ n), MvPolynomial.coeff e (A Q).val = ∑ r : Fin (n + 1), c r * MvPolynomial.coeff (Finsupp.single (0 : Fin 2) r.val + Finsupp.single (1 : Fin 2) (n - r.val)) Q.val`

## Sibling prerequisites

- `root.primitive_exists-a1.constant_defect-a1.linear_coeff_derivative-a1.binary_form_monomial_expansion-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
