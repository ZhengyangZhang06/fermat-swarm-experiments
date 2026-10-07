# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.primitive_parabolic-a1.primitive_cusp_limit-a1.pcl_linear_linepow_growth-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/nodes/root-primitive-parabolic-a1-primitive-cusp-limit-a1-pcl-linear-linepow-growth-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.primitive_parabolic-a1.primitive_cusp_limit-a1`
- Child key: `pcl_linear_linepow_growth`
- Declaration: `Submission.p02_es_177ebb5a_pcl_linear_linepow_growth`
- Exact Lean type: `∀ (n : ℕ) (T : ↥(HeckeEis.BinaryForm ℂ n) →ₗ[ℂ] ↥(HeckeEis.BinaryForm ℂ n)), ∃ K : ℝ, 0 ≤ K ∧ ∀ (z : ℂ) (d : Fin 2 →₀ ℕ), ‖MvPolynomial.coeff d (T (HeckeEis.linePow n z)).val‖ ≤ K * (1 + ‖z‖) ^ n`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
