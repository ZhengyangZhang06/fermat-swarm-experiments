# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.scalarization_derivative-a1.jet_recurrence-a1.moving_eval_derivative-a1.binary_form_jet_expansion-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/nodes/root-scalarization-derivative-a1-jet-recurrence-a1-moving-eval-deriva-0e3aa19dea/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.scalarization_derivative-a1.jet_recurrence-a1.moving_eval_derivative-a1`
- Child key: `binary_form_jet_expansion`
- Declaration: `Submission.p02_es_177ebb5a_med_jet_sum`
- Exact Lean type: `∀ (n : ℕ) (P : ↥(HeckeEis.BinaryForm ℂ n)) (r : ℕ) (z : ℂ), MvPolynomial.eval (fun j : Fin 2 => if j = 0 then 1 else -z) ((fun p : MvPolynomial (Fin 2) ℂ => MvPolynomial.pderiv (1 : Fin 2) p)^[r] P.val) = ∑ k : Fin (n + 1), MvPolynomial.coeff (Finsupp.single (0 : Fin 2) (n - k.val) + Finsupp.single (1 : Fin 2) k.val) P.val * (Nat.descFactorial k.val r : ℂ) * (-z) ^ (k.val - r)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
