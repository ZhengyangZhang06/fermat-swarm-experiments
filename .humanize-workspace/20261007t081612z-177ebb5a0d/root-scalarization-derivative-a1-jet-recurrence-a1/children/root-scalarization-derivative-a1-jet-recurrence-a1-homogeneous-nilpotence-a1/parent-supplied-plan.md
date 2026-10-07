# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.scalarization_derivative-a1.jet_recurrence-a1.homogeneous_nilpotence-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/nodes/root-scalarization-derivative-a1-jet-recurrence-a1-homogeneous-nilpotence-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.scalarization_derivative-a1.jet_recurrence-a1`
- Child key: `homogeneous_nilpotence`
- Declaration: `Submission.p02_es_177ebb5a_sd_jr_homogeneous_nilpotence`
- Exact Lean type: `∀ (n : ℕ) (P : ↥(HeckeEis.BinaryForm ℂ n)), ((fun p : MvPolynomial (Fin 2) ℂ => MvPolynomial.pderiv (1 : Fin 2) p)^[n + 1] P.val) = 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
