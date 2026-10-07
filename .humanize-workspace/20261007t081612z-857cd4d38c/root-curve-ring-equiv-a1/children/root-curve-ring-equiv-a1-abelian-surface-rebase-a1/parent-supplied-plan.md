# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.curve_ring_equiv-a1.abelian_surface_rebase-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/nodes/root-curve-ring-equiv-a1-abelian-surface-rebase-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.curve_ring_equiv-a1`
- Child key: `abelian_surface_rebase`
- Declaration: `Submission.p07_cre_abelian_surface_857cd4d38c`
- Exact Lean type: `∀ (T U : Type) [CommRing T] [CommRing U] (k : T ≃+* U) (A : AlgebraicGeometry.Scheme.{0}) (f : Quiver.Hom A (AlgebraicGeometry.Spec (CommRingCat.of U))), GoodReductionJacobian.AbelianSchemePropertyBundle U f → (∀ s : ↥(AlgebraicGeometry.Spec (CommRingCat.of U)), topologicalKrullDim ↥(f.base ⁻¹' {s}) = 2) → let fT := CategoryTheory.CategoryStruct.comp f (AlgebraicGeometry.Spec.map (CommRingCat.ofHom k.toRingHom)); GoodReductionJacobian.AbelianSchemePropertyBundle T fT ∧ (∀ s : ↥(AlgebraicGeometry.Spec (CommRingCat.of T)), topologicalKrullDim ↥(fT.base ⁻¹' {s}) = 2)`

## Sibling prerequisites

- `root.curve_ring_equiv-a1.group_law_rebase-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
