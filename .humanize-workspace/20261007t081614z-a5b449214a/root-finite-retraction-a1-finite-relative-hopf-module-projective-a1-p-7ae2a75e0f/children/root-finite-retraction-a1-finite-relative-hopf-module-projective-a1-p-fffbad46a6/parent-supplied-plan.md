# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.finite_retraction-a1.finite_relative_hopf_module_projective-a1.presentation_ideals_eq-a1.identity_block_stabilization-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/nodes/root-finite-retraction-a1-finite-relative-hopf-module-projective-a1-p-fffbad46a6/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.finite_retraction-a1.finite_relative_hopf_module_projective-a1.presentation_ideals_eq-a1`
- Child key: `identity_block_stabilization`
- Declaration: `Submission.p05_pie_identity_block_stabilization_a5b449214a`
- Exact Lean type: `∀ {R : Type*} [CommRing R] (n p t r : ℕ) (P : Matrix (Fin n) (Fin p) R), (Ideal.span {x : R | ∃ (rows : Fin (n + t - r) ↪ (Fin n ⊕ Fin t)) (cols : Fin (n + t - r) ↪ (Fin p ⊕ Fin t)), x = Matrix.det ((Matrix.fromBlocks P 0 0 (1 : Matrix (Fin t) (Fin t) R)).submatrix rows cols)}) = Ideal.span {x : R | ∃ (rows : Fin (n - r) ↪ Fin n) (cols : Fin (n - r) ↪ Fin p), x = Matrix.det (P.submatrix rows cols)}`

## Sibling prerequisites

- `root.finite_retraction-a1.finite_relative_hopf_module_projective-a1.presentation_ideals_eq-a1.successive_minor_containment-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
