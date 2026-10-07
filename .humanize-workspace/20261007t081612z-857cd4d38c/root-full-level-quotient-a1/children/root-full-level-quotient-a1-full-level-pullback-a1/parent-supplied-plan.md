# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.full_level_quotient-a1.full_level_pullback-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/nodes/root-full-level-quotient-a1-full-level-pullback-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.full_level_quotient-a1`
- Child key: `full_level_pullback`
- Declaration: `Submission.p07_flq_full_level_pullback_857cd4d38c`
- Exact Lean type: `∀ {a b : ℚ} (Λ : Submodule ℤ (QuaternionAlgebra ℚ a 0 b)) (N n : ℕ) (S T : Type) [CommRing S] [CommRing T] (φ : S →+* T) (E : CerednikDrinfeld.QM.FakeEllipticCurve Λ N S) (ET : CerednikDrinfeld.QM.FakeEllipticCurve Λ N T) (g : Quiver.Hom ET.A E.A), CerednikDrinfeld.QM.FakeEllipticCurve.IsPullbackVia φ E ET g → ∀ (L : CerednikDrinfeld.QM.FakeEllipticCurve.FullLevel E n), ∃ LT : CerednikDrinfeld.QM.FakeEllipticCurve.FullLevel ET n, CategoryTheory.CategoryStruct.comp LT.P.1 g = CategoryTheory.CategoryStruct.comp (AlgebraicGeometry.Spec.map (CommRingCat.ofHom φ)) L.P.1`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
