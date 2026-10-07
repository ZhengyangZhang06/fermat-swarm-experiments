# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.scalarization_derivative-a1.jet_recurrence-a1.linepow_jet_evaluation-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/nodes/root-scalarization-derivative-a1-jet-recurrence-a1-linepow-jet-evaluation-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.scalarization_derivative-a1.jet_recurrence-a1`
- Child key: `linepow_jet_evaluation`
- Declaration: `Submission.p02_es_177ebb5a_sd_jr_linepow_eval`
- Exact Lean type: `∀ (n r : ℕ), r ≤ n → ∀ t : ℂ, MvPolynomial.eval (fun j : Fin 2 => if j = 0 then 1 else -t) ((fun p : MvPolynomial (Fin 2) ℂ => MvPolynomial.pderiv (1 : Fin 2) p)^[r] (HeckeEis.linePow n t).val) = (if r = n then (Nat.factorial n : ℂ) else 0)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
