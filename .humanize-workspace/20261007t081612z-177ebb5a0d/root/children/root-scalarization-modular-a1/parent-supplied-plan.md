# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.scalarization_modular-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/nodes/root-scalarization-modular-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root`
- Child key: `scalarization_modular`
- Declaration: `Submission.p02_es_177ebb5a_scalarization_modular`
- Exact Lean type: `∀ (N : ℕ) [NeZero N] (n : ℕ) (f : CuspForm (CongruenceSubgroup.Gamma0 N) ((n : ℤ) + 2)) (E : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n)), HeckeEis.IsEichlerIntegral n (fun τ => f τ) E → (∀ (γ : CongruenceSubgroup.Gamma0 N) (τ : UpperHalfPlane), E ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) • τ) = ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype) γ (E τ)) → ∃ p : ModularForm (CongruenceSubgroup.Gamma0 N) (-(n : ℤ)), ∀ τ : UpperHalfPlane, p τ = MvPolynomial.eval (fun j : Fin 2 => if j = 0 then 1 else -(τ : ℂ)) (E τ).val`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
