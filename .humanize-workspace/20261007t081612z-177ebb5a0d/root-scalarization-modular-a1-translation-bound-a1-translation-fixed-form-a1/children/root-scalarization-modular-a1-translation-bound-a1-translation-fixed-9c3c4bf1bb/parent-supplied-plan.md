# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.scalarization_modular-a1.translation_bound-a1.translation_fixed_form-a1.constant_dehomogenization-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081612Z-177ebb5a0d/nodes/root-scalarization-modular-a1-translation-bound-a1-translation-fixed-9c3c4bf1bb/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.scalarization_modular-a1.translation_bound-a1.translation_fixed_form-a1`
- Child key: `constant_dehomogenization`
- Declaration: `Submission.p02_es_177ebb5a_tff_constant_dehomogenization`
- Exact Lean type: `∀ (n : ℕ) (A : ↥(HeckeEis.BinaryForm ℂ n)) (α : ℂ), MvPolynomial.eval₂ Polynomial.C (fun j : Fin 2 => if j = 0 then 1 else Polynomial.X) A.val = Polynomial.C α → A.val = MvPolynomial.C α * MvPolynomial.X (0 : Fin 2) ^ n`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
