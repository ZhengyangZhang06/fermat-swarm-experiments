# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.scalarization_modular-a1.integral_covariance-a1.inverse_linepow_transport-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/nodes/root-scalarization-modular-a1-integral-covariance-a1-inverse-linepow-298f49be71/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.scalarization_modular-a1.integral_covariance-a1`
- Child key: `inverse_linepow_transport`
- Declaration: `Submission.p02_es_177ebb5a_ic_inverse_linepow`
- Exact Lean type: `∀ (n : ℕ) (σ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (τ : UpperHalfPlane), (HeckeEis.binaryFormRepSL ℂ n) σ⁻¹ (HeckeEis.linePow n ((σ • τ : UpperHalfPlane) : ℂ)) = ((HeckeEis.jFactor σ τ) ^ n)⁻¹ • HeckeEis.linePow n (τ : ℂ)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
