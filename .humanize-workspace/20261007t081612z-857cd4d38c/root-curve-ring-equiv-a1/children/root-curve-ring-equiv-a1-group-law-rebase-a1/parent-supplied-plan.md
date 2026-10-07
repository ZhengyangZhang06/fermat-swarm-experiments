# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.curve_ring_equiv-a1.group_law_rebase-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/nodes/root-curve-ring-equiv-a1-group-law-rebase-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.curve_ring_equiv-a1`
- Child key: `group_law_rebase`
- Declaration: `Submission.p07_cre_group_law_857cd4d38c`
- Exact Lean type: `∀ (T U : Type) [CommRing T] [CommRing U] (k : T ≃+* U) (A : AlgebraicGeometry.Scheme.{0}) (f : Quiver.Hom A (AlgebraicGeometry.Spec (CommRingCat.of U))) (G : GoodReductionJacobian.RelativeGroupLaw U f), let κ := AlgebraicGeometry.Spec.map (CommRingCat.ofHom k.toRingHom); let ε := AlgebraicGeometry.Spec.map (CommRingCat.ofHom k.symm.toRingHom); let fT := CategoryTheory.CategoryStruct.comp f κ; ∃ (H : GoodReductionJacobian.RelativeGroupLaw T fT) (B : ∀ (W : AlgebraicGeometry.Scheme.{0}) (t : Quiver.Hom W (AlgebraicGeometry.Spec (CommRingCat.of T))), NeronModelInfra.SchemeHomOver t fT ≃ NeronModelInfra.SchemeHomOver (CategoryTheory.CategoryStruct.comp t ε) f), (G.IsCommutative → H.IsCommutative) ∧ (∀ (W : AlgebraicGeometry.Scheme.{0}) (t : Quiver.Hom W (AlgebraicGeometry.Spec (CommRingCat.of T))) (P : NeronModelInfra.SchemeHomOver t fT), (B W t P).1 = P.1) ∧ (∀ (W : AlgebraicGeometry.Scheme.{0}) (t : Quiver.Hom W (AlgebraicGeometry.Spec (CommRingCat.of T))) (P Q : NeronModelInfra.SchemeHomOver t fT), B W t (H.mul t P Q) = G.mul (CategoryTheory.CategoryStruct.comp t ε) (B W t P) (B W t Q)) ∧ (∀ (W : AlgebraicGeometry.Scheme.{0}) (t : Quiver.Hom W (AlgebraicGeometry.Spec (CommRingCat.of T))), B W t (H.one t) = G.one (CategoryTheory.CategoryStruct.comp t ε)) ∧ (∀ (W : AlgebraicGeometry.Scheme.{0}) (t : Quiver.Hom W (AlgebraicGeometry.Spec (CommRingCat.of T))) (P : NeronModelInfra.SchemeHomOver t fT), B W t (H.inv t P) = G.inv (CategoryTheory.CategoryStruct.comp t ε) (B W t P))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
