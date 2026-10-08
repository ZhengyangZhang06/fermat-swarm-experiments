# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.primitive_exists-a1.holomorphic_integral-a1.linepow_coefficient_formula-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/nodes/root-primitive-exists-a1-holomorphic-integral-a1-linepow-coefficient-formula-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.primitive_exists-a1.holomorphic_integral-a1`
- Child key: `linepow_coefficient_formula`
- Declaration: `Submission.p02_es_177ebb5a_hi_linepow_coefficients`
- Exact Lean type: `∀ (n : ℕ) (z : ℂ) (d : Fin 2 →₀ ℕ), MvPolynomial.coeff d (HeckeEis.linePow n z).val = if d 0 + d 1 = n then (Nat.choose n (d 0) : ℂ) * z ^ (d 0) else 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
