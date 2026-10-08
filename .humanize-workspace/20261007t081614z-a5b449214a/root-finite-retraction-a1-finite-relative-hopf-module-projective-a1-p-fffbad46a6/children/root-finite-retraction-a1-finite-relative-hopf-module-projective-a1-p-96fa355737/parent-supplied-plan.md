# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.finite_retraction-a1.finite_relative_hopf_module_projective-a1.presentation_ideals_eq-a1.identity_block_stabilization-a1.extend_minor-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/nodes/root-finite-retraction-a1-finite-relative-hopf-module-projective-a1-p-96fa355737/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.finite_retraction-a1.finite_relative_hopf_module_projective-a1.presentation_ideals_eq-a1.identity_block_stabilization-a1`
- Child key: `extend_minor`
- Declaration: `Submission.p05_ibs_extend_minor_a5b449214a`
- Exact Lean type: `∀ {R : Type*} [CommRing R] (n p t s : ℕ) (P : Matrix (Fin n) (Fin p) R) (rows : Fin s ↪ Fin n) (cols : Fin s ↪ Fin p), ∃ (rows' : Fin (s + t) ↪ (Fin n ⊕ Fin t)) (cols' : Fin (s + t) ↪ (Fin p ⊕ Fin t)), Matrix.det ((Matrix.fromBlocks P 0 0 (1 : Matrix (Fin t) (Fin t) R)).submatrix rows' cols') = Matrix.det (P.submatrix rows cols)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
