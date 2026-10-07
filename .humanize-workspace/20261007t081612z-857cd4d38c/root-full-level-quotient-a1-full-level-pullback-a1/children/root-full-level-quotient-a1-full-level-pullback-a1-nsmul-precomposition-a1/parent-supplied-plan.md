# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.full_level_quotient-a1.full_level_pullback-a1.nsmul_precomposition-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/nodes/root-full-level-quotient-a1-full-level-pullback-a1-nsmul-precomposition-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.full_level_quotient-a1.full_level_pullback-a1`
- Child key: `nsmul_precomposition`
- Declaration: `Submission.p07_flp_nsmul_precomp_857cd4d38c`
- Exact Lean type: `∀ (R : Type) [CommRing R] (A W W' : AlgebraicGeometry.Scheme.{0}) (f : Quiver.Hom A (AlgebraicGeometry.Spec (CommRingCat.of R))) (L : GoodReductionJacobian.RelativeGroupLaw R f) (t : Quiver.Hom W (AlgebraicGeometry.Spec (CommRingCat.of R))) (t' : Quiver.Hom W' (AlgebraicGeometry.Spec (CommRingCat.of R))) (ψ : Quiver.Hom W' W) (hψ : CategoryTheory.CategoryStruct.comp ψ t = t') (k : ℕ) (P : NeronModelInfra.SchemeHomOver t f), GoodReductionJacobian.schemeHomOverComp ψ hψ (CerednikDrinfeld.QM.nsmulPt L t k P) = CerednikDrinfeld.QM.nsmulPt L t' k (GoodReductionJacobian.schemeHomOverComp ψ hψ P)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
