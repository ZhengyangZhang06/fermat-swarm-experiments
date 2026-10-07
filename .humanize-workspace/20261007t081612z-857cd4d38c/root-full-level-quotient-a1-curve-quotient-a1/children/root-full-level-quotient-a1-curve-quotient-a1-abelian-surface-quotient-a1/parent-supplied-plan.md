# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.full_level_quotient-a1.curve_quotient-a1.abelian_surface_quotient-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/nodes/root-full-level-quotient-a1-curve-quotient-a1-abelian-surface-quotient-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.full_level_quotient-a1.curve_quotient-a1`
- Child key: `abelian_surface_quotient`
- Declaration: `Submission.p07_cq_abelian_surface_quotient_857cd4d38c`
- Exact Lean type: `∀ (S : Type) [CommRing S] (J : Ideal S) (A : AlgebraicGeometry.Scheme.{0}) (f : Quiver.Hom A (AlgebraicGeometry.Spec (CommRingCat.of S))), GoodReductionJacobian.AbelianSchemePropertyBundle S f → (∀ s : ↥(AlgebraicGeometry.Spec (CommRingCat.of S)), topologicalKrullDim ↥(f.base ⁻¹' {s}) = 2) → let β := AlgebraicGeometry.Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)); let p := CategoryTheory.Limits.pullback.snd f β; GoodReductionJacobian.AbelianSchemePropertyBundle (S ⧸ J) p ∧ (∀ t : ↥(AlgebraicGeometry.Spec (CommRingCat.of (S ⧸ J))), topologicalKrullDim ↥(p.base ⁻¹' {t}) = 2)`

## Sibling prerequisites

- `root.full_level_quotient-a1.curve_quotient-a1.group_law_pullback-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
