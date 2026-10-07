# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.curve_ring_equiv-a1.finite_flat_rank_rebase-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/nodes/root-curve-ring-equiv-a1-finite-flat-rank-rebase-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.curve_ring_equiv-a1`
- Child key: `finite_flat_rank_rebase`
- Declaration: `Submission.p07_cre_finite_flat_rank_857cd4d38c`
- Exact Lean type: `∀ (T U : Type) [CommRing T] [CommRing U] (k : T ≃+* U) (C : AlgebraicGeometry.Scheme.{0}) (q : Quiver.Hom C (AlgebraicGeometry.Spec (CommRingCat.of U))), AlgebraicGeometry.IsFinite q → AlgebraicGeometry.Flat q → AlgebraicGeometry.LocallyOfFinitePresentation q → let ε := AlgebraicGeometry.Spec.map (CommRingCat.ofHom k.symm.toRingHom); let qT := CategoryTheory.CategoryStruct.comp q (AlgebraicGeometry.Spec.map (CommRingCat.ofHom k.toRingHom)); AlgebraicGeometry.IsFinite qT ∧ AlgebraicGeometry.Flat qT ∧ AlgebraicGeometry.LocallyOfFinitePresentation qT ∧ (∀ s : ↥(AlgebraicGeometry.Spec (CommRingCat.of T)), AlgebraicGeometry.Scheme.Hom.finrank qT s = AlgebraicGeometry.Scheme.Hom.finrank q (ε s))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
