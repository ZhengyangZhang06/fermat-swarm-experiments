# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.finite_retraction-a1.finite_relative_hopf_module_projective-a1.presentation_ideals_eq-a1.successive_minor_containment-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/nodes/root-finite-retraction-a1-finite-relative-hopf-module-projective-a1-p-be701d4166/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.finite_retraction-a1.finite_relative_hopf_module_projective-a1.presentation_ideals_eq-a1`
- Child key: `successive_minor_containment`
- Declaration: `Submission.p05_pie_successive_minor_containment_a5b449214a`
- Exact Lean type: `∀ {R : Type*} [CommRing R] {ι κ : Type*} [Fintype ι] [Fintype κ] (P : Matrix ι κ R) (d : ℕ), (Ideal.span {x : R | ∃ (rows : Fin (d + 1) ↪ ι) (cols : Fin (d + 1) ↪ κ), x = Matrix.det (P.submatrix rows cols)}) ≤ Ideal.span {x : R | ∃ (rows : Fin d ↪ ι) (cols : Fin d ↪ κ), x = Matrix.det (P.submatrix rows cols)}`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
