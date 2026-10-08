# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.finite_retraction-a1.finite_relative_hopf_module_projective-a1.presentation_ideals_eq-a1.identity_block_stabilization-a1.reduce_minor-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/nodes/root-finite-retraction-a1-finite-relative-hopf-module-projective-a1-p-41a8d177ae/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.finite_retraction-a1.finite_relative_hopf_module_projective-a1.presentation_ideals_eq-a1.identity_block_stabilization-a1`
- Child key: `reduce_minor`
- Declaration: `Submission.p05_ibs_reduce_minor_a5b449214a`
- Exact Lean type: `∀ {R : Type*} [CommRing R] (n p t d : ℕ) (P : Matrix (Fin n) (Fin p) R) (rows : Fin d ↪ (Fin n ⊕ Fin t)) (cols : Fin d ↪ (Fin p ⊕ Fin t)), let E : Matrix (Fin n ⊕ Fin t) (Fin p ⊕ Fin t) R := Matrix.fromBlocks P 0 0 (1 : Matrix (Fin t) (Fin t) R); Matrix.det (E.submatrix rows cols) = 0 ∨ ∃ l : ℕ, l ≤ t ∧ l ≤ d ∧ ∃ (rows' : Fin (d - l) ↪ Fin n) (cols' : Fin (d - l) ↪ Fin p), Matrix.det (E.submatrix rows cols) = Matrix.det (P.submatrix rows' cols') ∨ Matrix.det (E.submatrix rows cols) = -Matrix.det (P.submatrix rows' cols')`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
