# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.scalarization_modular-a1.translation_bound-a1.strip_coefficient_limit-a1.linepow_coefficient_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/nodes/root-scalarization-modular-a1-translation-bound-a1-strip-coefficient-7c79526935/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.scalarization_modular-a1.translation_bound-a1.strip_coefficient_limit-a1`
- Child key: `linepow_coefficient_bound`
- Declaration: `Submission.p02_es_177ebb5a_scl_linepow_coeff_bound`
- Exact Lean type: `∀ (n : ℕ) (z : ℂ) (d : Fin 2 →₀ ℕ), ‖MvPolynomial.coeff d (HeckeEis.linePow n z).val‖ ≤ (2 : ℝ) ^ n * (max 1 ‖z‖) ^ n`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
