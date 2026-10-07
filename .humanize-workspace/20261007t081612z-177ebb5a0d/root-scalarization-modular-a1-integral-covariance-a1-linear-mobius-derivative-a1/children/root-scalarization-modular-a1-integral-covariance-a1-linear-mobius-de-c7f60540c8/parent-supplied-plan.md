# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.scalarization_modular-a1.integral_covariance-a1.linear_mobius_derivative-a1.scalar_mobius_pullback-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/nodes/root-scalarization-modular-a1-integral-covariance-a1-linear-mobius-de-c7f60540c8/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.scalarization_modular-a1.integral_covariance-a1.linear_mobius_derivative-a1`
- Child key: `scalar_mobius_pullback`
- Declaration: `Submission.p02_es_177ebb5a_ic_lmd_scalar_pullback`
- Exact Lean type: `∀ (h : UpperHalfPlane → ℂ) (v : ℂ) (σ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (τ : UpperHalfPlane), HasDerivAt (fun z : ℂ => h (UpperHalfPlane.ofComplex z)) v ((σ • τ : UpperHalfPlane) : ℂ) → HasDerivAt (fun z : ℂ => h (σ • UpperHalfPlane.ofComplex z)) (v / (HeckeEis.jFactor σ τ) ^ 2) (τ : ℂ)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
