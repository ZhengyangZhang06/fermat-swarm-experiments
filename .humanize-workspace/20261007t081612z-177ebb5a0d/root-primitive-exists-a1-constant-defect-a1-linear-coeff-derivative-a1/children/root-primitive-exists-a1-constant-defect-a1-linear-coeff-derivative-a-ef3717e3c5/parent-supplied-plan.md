# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.primitive_exists-a1.constant_defect-a1.linear_coeff_derivative-a1.binary_form_monomial_expansion-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/nodes/root-primitive-exists-a1-constant-defect-a1-linear-coeff-derivative-a-ef3717e3c5/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.primitive_exists-a1.constant_defect-a1.linear_coeff_derivative-a1`
- Child key: `binary_form_monomial_expansion`
- Declaration: `Submission.p02_es_177ebb5a_lcd_monomial_expansion`
- Exact Lean type: `∀ (n : ℕ) (Q : ↥(HeckeEis.BinaryForm ℂ n)), Q.val = ∑ r : Fin (n + 1), MvPolynomial.coeff (Finsupp.single (0 : Fin 2) r.val + Finsupp.single (1 : Fin 2) (n - r.val)) Q.val • MvPolynomial.monomial (Finsupp.single (0 : Fin 2) r.val + Finsupp.single (1 : Fin 2) (n - r.val)) (1 : ℂ)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
