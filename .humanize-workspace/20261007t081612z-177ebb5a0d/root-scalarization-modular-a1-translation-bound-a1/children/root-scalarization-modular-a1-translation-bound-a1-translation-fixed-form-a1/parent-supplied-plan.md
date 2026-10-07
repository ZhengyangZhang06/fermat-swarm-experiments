# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.scalarization_modular-a1.translation_bound-a1.translation_fixed_form-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/nodes/root-scalarization-modular-a1-translation-bound-a1-translation-fixed-form-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.scalarization_modular-a1.translation_bound-a1`
- Child key: `translation_fixed_form`
- Declaration: `Submission.p02_es_177ebb5a_tb_fixed_form`
- Exact Lean type: `∀ (N : ℕ) [NeZero N] (n : ℕ) (A : ↥(HeckeEis.BinaryForm ℂ n)), HeckeEis.binaryFormRepSL ℂ n (ModularGroup.T ^ N) A = A → ∃ α : ℂ, A.val = MvPolynomial.C α * MvPolynomial.X (0 : Fin 2) ^ n`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
