# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.scalarization_derivative-a1.jet_recurrence-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/nodes/root-scalarization-derivative-a1-jet-recurrence-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.scalarization_derivative-a1`
- Child key: `jet_recurrence`
- Declaration: `Submission.p02_es_177ebb5a_sd_jet_recurrence`
- Exact Lean type: `∀ (n : ℕ) (h : UpperHalfPlane → ℂ) (E : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n)), HeckeEis.IsEichlerIntegral n h E → ∀ (r : ℕ), r ≤ n → ∀ τ : UpperHalfPlane, HasDerivAt (fun z : ℂ => MvPolynomial.eval (fun j : Fin 2 => if j = 0 then 1 else -z) ((fun p : MvPolynomial (Fin 2) ℂ => MvPolynomial.pderiv (1 : Fin 2) p)^[r] (E (UpperHalfPlane.ofComplex z)).val)) (if r = n then (Nat.factorial n : ℂ) * h τ else -MvPolynomial.eval (fun j : Fin 2 => if j = 0 then 1 else -(τ : ℂ)) ((fun p : MvPolynomial (Fin 2) ℂ => MvPolynomial.pderiv (1 : Fin 2) p)^[r + 1] (E τ).val)) (τ : ℂ)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
