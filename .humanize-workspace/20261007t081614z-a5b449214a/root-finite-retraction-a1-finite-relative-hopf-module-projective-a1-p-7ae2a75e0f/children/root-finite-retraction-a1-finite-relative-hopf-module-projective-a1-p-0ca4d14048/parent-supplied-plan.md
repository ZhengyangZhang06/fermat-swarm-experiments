# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.finite_retraction-a1.finite_relative_hopf_module_projective-a1.presentation_ideals_eq-a1.redundant_generator_relations-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081614Z-a5b449214a/nodes/root-finite-retraction-a1-finite-relative-hopf-module-projective-a1-p-0ca4d14048/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.finite_retraction-a1.finite_relative_hopf_module_projective-a1.presentation_ideals_eq-a1`
- Child key: `redundant_generator_relations`
- Declaration: `Submission.p05_pie_redundant_generator_relations_a5b449214a`
- Exact Lean type: `∀ {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] (n p t : ℕ) (P : Matrix (Fin n) (Fin p) R) (A : Matrix (Fin n) (Fin t) R) (π : (Fin n → R) →ₗ[R] M) (ψ : (Fin t → R) →ₗ[R] M) (_hker : LinearMap.ker π = LinearMap.range P.mulVecLin) (_hA : ∀ y : Fin t → R, π (A.mulVecLin y) = ψ y), let T : Matrix (Fin n ⊕ Fin t) (Fin p ⊕ Fin t) R := Matrix.fromBlocks P (-A) 0 (1 : Matrix (Fin t) (Fin t) R); ∀ z : (Fin n ⊕ Fin t) → R, (π (fun i => z (Sum.inl i)) + ψ (fun j => z (Sum.inr j)) = 0) ↔ ∃ w : (Fin p ⊕ Fin t) → R, T.mulVecLin w = z`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
