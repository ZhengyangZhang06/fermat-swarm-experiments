# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.primitive_parabolic-a1.primitive_cusp_limit-a1.pcl_scaled_pullback_derivative-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/nodes/root-primitive-parabolic-a1-primitive-cusp-limit-a1-pcl-scaled-pullba-58ee9bb0b0/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.primitive_parabolic-a1.primitive_cusp_limit-a1`
- Child key: `pcl_scaled_pullback_derivative`
- Declaration: `Submission.p02_es_177ebb5a_pcl_scaled_pullback_derivative`
- Exact Lean type: `∀ (n : ℕ) (f : UpperHalfPlane → ℂ) (F : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n)), HeckeEis.IsEichlerIntegral n f F → ∀ (σ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (d : Fin 2 →₀ ℕ) (τ : UpperHalfPlane), HasDerivAt (fun z : ℂ => MvPolynomial.coeff d (F (σ • UpperHalfPlane.ofComplex z)).val) ((HeckeEis.jFactor σ τ) ^ (-((n : ℤ) + 2)) * f (σ • τ) * MvPolynomial.coeff d ((HeckeEis.binaryFormRepSL ℂ n σ) (HeckeEis.linePow n (τ : ℂ))).val) (τ : ℂ)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
