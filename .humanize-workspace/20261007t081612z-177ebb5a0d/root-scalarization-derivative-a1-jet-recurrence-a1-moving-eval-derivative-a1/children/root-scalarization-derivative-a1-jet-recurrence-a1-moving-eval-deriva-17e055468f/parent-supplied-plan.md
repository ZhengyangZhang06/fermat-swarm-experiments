# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.scalarization_derivative-a1.jet_recurrence-a1.moving_eval_derivative-a1.finite_jet_sum_derivative-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/nodes/root-scalarization-derivative-a1-jet-recurrence-a1-moving-eval-deriva-17e055468f/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.scalarization_derivative-a1.jet_recurrence-a1.moving_eval_derivative-a1`
- Child key: `finite_jet_sum_derivative`
- Declaration: `Submission.p02_es_177ebb5a_med_sum_derivative`
- Exact Lean type: `∀ (n r : ℕ) (a : Fin (n + 1) → ℂ → ℂ) (b : Fin (n + 1) → ℂ) (c t : ℂ), (∀ k : Fin (n + 1), HasDerivAt (a k) (c * b k) t) → HasDerivAt (fun z : ℂ => ∑ k : Fin (n + 1), a k z * (Nat.descFactorial k.val r : ℂ) * (-z) ^ (k.val - r)) (c * (∑ k : Fin (n + 1), b k * (Nat.descFactorial k.val r : ℂ) * (-t) ^ (k.val - r)) - (∑ k : Fin (n + 1), a k t * (Nat.descFactorial k.val (r + 1) : ℂ) * (-t) ^ (k.val - (r + 1)))) t`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
