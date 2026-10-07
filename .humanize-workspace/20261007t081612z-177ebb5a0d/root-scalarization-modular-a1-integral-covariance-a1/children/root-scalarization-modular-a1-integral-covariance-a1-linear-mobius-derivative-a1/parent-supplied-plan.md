# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.scalarization_modular-a1.integral_covariance-a1.linear_mobius_derivative-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/nodes/root-scalarization-modular-a1-integral-covariance-a1-linear-mobius-derivative-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.scalarization_modular-a1.integral_covariance-a1`
- Child key: `linear_mobius_derivative`
- Declaration: `Submission.p02_es_177ebb5a_ic_linear_mobius_derivative`
- Exact Lean type: `∀ (n : ℕ) (A : ↥(HeckeEis.BinaryForm ℂ n) →ₗ[ℂ] ↥(HeckeEis.BinaryForm ℂ n)) (F : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n)) (P : ↥(HeckeEis.BinaryForm ℂ n)) (σ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (τ : UpperHalfPlane), (∀ d : Fin 2 →₀ ℕ, HasDerivAt (fun z : ℂ => MvPolynomial.coeff d (F (UpperHalfPlane.ofComplex z)).val) (MvPolynomial.coeff d P.val) ((σ • τ : UpperHalfPlane) : ℂ)) → ∀ e : Fin 2 →₀ ℕ, HasDerivAt (fun z : ℂ => MvPolynomial.coeff e (A (F (σ • UpperHalfPlane.ofComplex z))).val) (MvPolynomial.coeff e (A P).val / (HeckeEis.jFactor σ τ) ^ 2) (τ : ℂ)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
