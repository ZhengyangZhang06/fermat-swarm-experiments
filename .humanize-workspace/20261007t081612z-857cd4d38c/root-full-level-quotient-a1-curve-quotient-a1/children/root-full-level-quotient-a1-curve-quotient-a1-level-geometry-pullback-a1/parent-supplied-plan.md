# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.full_level_quotient-a1.curve_quotient-a1.level_geometry_pullback-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/nodes/root-full-level-quotient-a1-curve-quotient-a1-level-geometry-pullback-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.full_level_quotient-a1.curve_quotient-a1`
- Child key: `level_geometry_pullback`
- Declaration: `Submission.p07_cq_level_geometry_pullback_857cd4d38c`
- Exact Lean type: `∀ (S T : Type) [CommRing S] [CommRing T] (φ : S →+* T) (A C : AlgebraicGeometry.Scheme.{0}) (f : Quiver.Hom A (AlgebraicGeometry.Spec (CommRingCat.of S))) (ℓ : Quiver.Hom C A), AlgebraicGeometry.IsClosedImmersion ℓ → AlgebraicGeometry.IsFinite (CategoryTheory.CategoryStruct.comp ℓ f) → AlgebraicGeometry.Flat (CategoryTheory.CategoryStruct.comp ℓ f) → AlgebraicGeometry.LocallyOfFinitePresentation (CategoryTheory.CategoryStruct.comp ℓ f) → let β := AlgebraicGeometry.Spec.map (CommRingCat.ofHom φ); let c := CategoryTheory.CategoryStruct.comp ℓ f; let p := CategoryTheory.Limits.pullback.snd f β; let g := CategoryTheory.Limits.pullback.fst f β; let r := CategoryTheory.Limits.pullback.fst c β; let d := CategoryTheory.Limits.pullback.snd c β; ∃ ℓT : Quiver.Hom (CategoryTheory.Limits.pullback c β) (CategoryTheory.Limits.pullback f β), CategoryTheory.IsPullback r ℓT ℓ g ∧ CategoryTheory.CategoryStruct.comp ℓT p = d ∧ AlgebraicGeometry.IsClosedImmersion ℓT ∧ AlgebraicGeometry.IsFinite d ∧ AlgebraicGeometry.Flat d ∧ AlgebraicGeometry.LocallyOfFinitePresentation d ∧ (∀ t : ↥(AlgebraicGeometry.Spec (CommRingCat.of T)), AlgebraicGeometry.Scheme.Hom.finrank d t = AlgebraicGeometry.Scheme.Hom.finrank c (β t)) ∧ (∀ (W : AlgebraicGeometry.Scheme.{0}) (Q : Quiver.Hom W (CategoryTheory.Limits.pullback f β)), (∃ R : Quiver.Hom W (CategoryTheory.Limits.pullback c β), CategoryTheory.CategoryStruct.comp R ℓT = Q) ↔ (∃ R : Quiver.Hom W C, CategoryTheory.CategoryStruct.comp R ℓ = CategoryTheory.CategoryStruct.comp Q g))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
