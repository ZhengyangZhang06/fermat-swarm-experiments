# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.primitive_exists-a1.constant_defect-a1.modular_pullback_derivative-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/nodes/root-primitive-exists-a1-constant-defect-a1-modular-pullback-derivative-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.primitive_exists-a1.constant_defect-a1`
- Child key: `modular_pullback_derivative`
- Declaration: `Submission.p02_es_177ebb5a_cd_modular_pullback_derivative`
- Exact Lean type: `∀ (N : ℕ) [NeZero N] (n : ℕ) (f : CuspForm (CongruenceSubgroup.Gamma0 N) ((n : ℤ) + 2)) (F : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n)), HeckeEis.IsEichlerIntegral n (fun τ => f τ) F → ∀ (γ : CongruenceSubgroup.Gamma0 N) (e : Fin 2 →₀ ℕ) (τ : UpperHalfPlane), HasDerivAt (fun z : ℂ => MvPolynomial.coeff e (F ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) • UpperHalfPlane.ofComplex z)).val) (f τ * MvPolynomial.coeff e ((((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype) γ) (HeckeEis.linePow n (τ : ℂ))).val) (τ : ℂ)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
