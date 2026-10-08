# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.scalarization_derivative-a1.jet_recurrence-a1.moving_eval_derivative-a1.binary_form_jet_expansion-a1.iterated_binary_monomial_pderiv-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/nodes/root-scalarization-derivative-a1-jet-recurrence-a1-moving-eval-deriva-c6f7b88845/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.scalarization_derivative-a1.jet_recurrence-a1.moving_eval_derivative-a1.binary_form_jet_expansion-a1`
- Child key: `iterated_binary_monomial_pderiv`
- Declaration: `Submission.p02_es_177ebb5a_med_js_iterated_monomial`
- Exact Lean type: `∀ (d : Fin 2 →₀ ℕ) (a : ℂ) (r : ℕ), ((fun p : MvPolynomial (Fin 2) ℂ => MvPolynomial.pderiv (1 : Fin 2) p)^[r] (MvPolynomial.monomial d a)) = MvPolynomial.monomial (d - Finsupp.single (1 : Fin 2) r) (a * (Nat.descFactorial (d 1) r : ℂ))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
