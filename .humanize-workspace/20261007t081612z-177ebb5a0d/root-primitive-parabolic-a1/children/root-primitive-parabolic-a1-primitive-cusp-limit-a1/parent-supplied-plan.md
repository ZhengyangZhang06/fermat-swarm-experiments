# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.primitive_parabolic-a1.primitive_cusp_limit-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/nodes/root-primitive-parabolic-a1-primitive-cusp-limit-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.primitive_parabolic-a1`
- Child key: `primitive_cusp_limit`
- Declaration: `Submission.p02_es_177ebb5a_pp_primitive_cusp_limit`
- Exact Lean type: `∀ (N : ℕ) [NeZero N] (n : ℕ) (f : CuspForm (CongruenceSubgroup.Gamma0 N) ((n : ℤ) + 2)) (F : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n)), HeckeEis.IsEichlerIntegral n (fun τ => f τ) F → ∀ σ : Matrix.SpecialLinearGroup (Fin 2) ℤ, ∃ A : ↥(HeckeEis.BinaryForm ℂ n), ∀ (x : ℝ) (d : Fin 2 →₀ ℕ), Filter.Tendsto (fun y : ℝ => MvPolynomial.coeff d (F (σ • UpperHalfPlane.ofComplex ((x : ℂ) + (y : ℂ) * Complex.I))).val) Filter.atTop (nhds (MvPolynomial.coeff d A.val))`

## Sibling prerequisites

- `root.primitive_parabolic-a1.scaled_cusp_decay-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
