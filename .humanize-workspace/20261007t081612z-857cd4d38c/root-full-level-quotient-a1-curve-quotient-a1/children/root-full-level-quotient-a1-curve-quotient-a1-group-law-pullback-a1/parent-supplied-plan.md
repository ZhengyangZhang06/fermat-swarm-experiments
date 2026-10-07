# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.full_level_quotient-a1.curve_quotient-a1.group_law_pullback-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/nodes/root-full-level-quotient-a1-curve-quotient-a1-group-law-pullback-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.full_level_quotient-a1.curve_quotient-a1`
- Child key: `group_law_pullback`
- Declaration: `Submission.p07_cq_group_law_pullback_857cd4d38c`
- Exact Lean type: `∀ (S T : Type) [CommRing S] [CommRing T] (φ : S →+* T) (A : AlgebraicGeometry.Scheme.{0}) (f : Quiver.Hom A (AlgebraicGeometry.Spec (CommRingCat.of S))) (G : GoodReductionJacobian.RelativeGroupLaw S f), let β := AlgebraicGeometry.Spec.map (CommRingCat.ofHom φ); let p := CategoryTheory.Limits.pullback.snd f β; let g := CategoryTheory.Limits.pullback.fst f β; ∃ (H : GoodReductionJacobian.RelativeGroupLaw T p) (B : ∀ (W : AlgebraicGeometry.Scheme.{0}) (t : Quiver.Hom W (AlgebraicGeometry.Spec (CommRingCat.of T))), NeronModelInfra.SchemeHomOver t p ≃ NeronModelInfra.SchemeHomOver (CategoryTheory.CategoryStruct.comp t β) f), (G.IsCommutative → H.IsCommutative) ∧ (∀ (W : AlgebraicGeometry.Scheme.{0}) (t : Quiver.Hom W (AlgebraicGeometry.Spec (CommRingCat.of T))) (P : NeronModelInfra.SchemeHomOver t p), (B W t P).1 = CategoryTheory.CategoryStruct.comp P.1 g) ∧ (∀ (W : AlgebraicGeometry.Scheme.{0}) (t : Quiver.Hom W (AlgebraicGeometry.Spec (CommRingCat.of T))) (P Q : NeronModelInfra.SchemeHomOver t p), B W t (H.mul t P Q) = G.mul (CategoryTheory.CategoryStruct.comp t β) (B W t P) (B W t Q)) ∧ (∀ (W : AlgebraicGeometry.Scheme.{0}) (t : Quiver.Hom W (AlgebraicGeometry.Spec (CommRingCat.of T))), B W t (H.one t) = G.one (CategoryTheory.CategoryStruct.comp t β)) ∧ (∀ (W : AlgebraicGeometry.Scheme.{0}) (t : Quiver.Hom W (AlgebraicGeometry.Spec (CommRingCat.of T))) (P : NeronModelInfra.SchemeHomOver t p), B W t (H.inv t P) = G.inv (CategoryTheory.CategoryStruct.comp t β) (B W t P))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
