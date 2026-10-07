# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.full_level_quotient-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/nodes/root-full-level-quotient-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root`
- Child key: `full_level_quotient`
- Declaration: `Submission.p07_full_level_quotient_857cd4d38c`
- Exact Lean type: `∀ {a b : ℚ} (Λ : Submodule ℤ (QuaternionAlgebra ℚ a 0 b)) (N n : ℕ) (S : Type) [CommRing S] (J : Ideal S) (u : CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel Λ N n S), ∃ (v : CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel Λ N n (S ⧸ J)) (g : Quiver.Hom v.1.A u.1.A), CerednikDrinfeld.QM.FakeEllipticCurve.IsPullbackVia (Ideal.Quotient.mk J) u.1 v.1 g ∧ CategoryTheory.CategoryStruct.comp v.2.P.1 g = CategoryTheory.CategoryStruct.comp (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) u.2.P.1`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
