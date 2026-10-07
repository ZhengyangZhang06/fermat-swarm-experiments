# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.scalarization_derivative-a1.jet_recurrence-a1.moving_eval_derivative-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/nodes/root-scalarization-derivative-a1-jet-recurrence-a1-moving-eval-derivative-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.scalarization_derivative-a1.jet_recurrence-a1`
- Child key: `moving_eval_derivative`
- Declaration: `Submission.p02_es_177ebb5a_sd_jr_moving_eval_derivative`
- Exact Lean type: `∀ (n : ℕ) (F : ℂ → ↥(HeckeEis.BinaryForm ℂ n)) (G : ↥(HeckeEis.BinaryForm ℂ n)) (c t : ℂ), (∀ d : Fin 2 →₀ ℕ, HasDerivAt (fun z : ℂ => MvPolynomial.coeff d (F z).val) (c * MvPolynomial.coeff d G.val) t) → ∀ r : ℕ, r ≤ n → HasDerivAt (fun z : ℂ => MvPolynomial.eval (fun j : Fin 2 => if j = 0 then 1 else -z) ((fun p : MvPolynomial (Fin 2) ℂ => MvPolynomial.pderiv (1 : Fin 2) p)^[r] (F z).val)) (c * MvPolynomial.eval (fun j : Fin 2 => if j = 0 then 1 else -t) ((fun p : MvPolynomial (Fin 2) ℂ => MvPolynomial.pderiv (1 : Fin 2) p)^[r] G.val) - MvPolynomial.eval (fun j : Fin 2 => if j = 0 then 1 else -t) ((fun p : MvPolynomial (Fin 2) ℂ => MvPolynomial.pderiv (1 : Fin 2) p)^[r + 1] (F t).val)) t`

## Sibling prerequisites

- `root.scalarization_derivative-a1.jet_recurrence-a1.homogeneous_nilpotence-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
