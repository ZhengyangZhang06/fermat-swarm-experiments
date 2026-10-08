# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.finite_retraction-a1.finite_relative_hopf_module_projective-a1.presentation_ideals_eq-a1.minor_product_containment-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/nodes/root-finite-retraction-a1-finite-relative-hopf-module-projective-a1-p-2a28d2748b/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.finite_retraction-a1.finite_relative_hopf_module_projective-a1.presentation_ideals_eq-a1`
- Child key: `minor_product_containment`
- Declaration: `Submission.p05_pie_minor_product_containment_a5b449214a`
- Exact Lean type: `∀ {R : Type*} [CommRing R] {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν] (A : Matrix ι κ R) (B : Matrix κ ν R) (d : ℕ), (Ideal.span {x : R | ∃ (rows : Fin d ↪ ι) (cols : Fin d ↪ ν), x = Matrix.det ((A * B).submatrix rows cols)}) ≤ (Ideal.span {x : R | ∃ (rows : Fin d ↪ ι) (cols : Fin d ↪ κ), x = Matrix.det (A.submatrix rows cols)}) ⊓ (Ideal.span {x : R | ∃ (rows : Fin d ↪ κ) (cols : Fin d ↪ ν), x = Matrix.det (B.submatrix rows cols)})`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
