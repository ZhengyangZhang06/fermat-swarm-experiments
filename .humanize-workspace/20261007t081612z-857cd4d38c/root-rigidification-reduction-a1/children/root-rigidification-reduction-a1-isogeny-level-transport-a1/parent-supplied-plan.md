# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.rigidification_reduction-a1.isogeny_level_transport-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/nodes/root-rigidification-reduction-a1-isogeny-level-transport-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.rigidification_reduction-a1`
- Child key: `isogeny_level_transport`
- Declaration: `Submission.p07_rr_isogeny_transport_857cd4d38c`
- Exact Lean type: `∀ {a b : ℚ} (Λ : Submodule ℤ (QuaternionAlgebra ℚ a 0 b)) (N d : ℕ) (T U : Type) [CommRing T] [CommRing U] (k : T ≃+* U) (E F : CerednikDrinfeld.QM.FakeEllipticCurve Λ N T) (D H : CerednikDrinfeld.QM.FakeEllipticCurve Λ N U) (i : CategoryTheory.Iso D.A E.A) (j : CategoryTheory.Iso H.A F.A), CerednikDrinfeld.QM.FakeEllipticCurve.IsPullbackVia k.toRingHom E D i.hom → CerednikDrinfeld.QM.FakeEllipticCurve.IsPullbackVia k.symm.toRingHom D E i.inv → CerednikDrinfeld.QM.FakeEllipticCurve.IsPullbackVia k.toRingHom F H j.hom → CerednikDrinfeld.QM.FakeEllipticCurve.IsPullbackVia k.symm.toRingHom H F j.inv → ∀ (φ : Quiver.Hom D.A H.A) (ψ : Quiver.Hom H.A D.A) (hφ : CategoryTheory.CategoryStruct.comp φ H.f = D.f), CerednikDrinfeld.QM.FakeEllipticCurve.IsIsogenyPair d D H φ ψ → CerednikDrinfeld.QM.FakeEllipticCurve.PreservesLevel D H φ hφ → CerednikDrinfeld.QM.FakeEllipticCurve.IsIsogenyPair d E F (CategoryTheory.CategoryStruct.comp i.inv (CategoryTheory.CategoryStruct.comp φ j.hom)) (CategoryTheory.CategoryStruct.comp j.inv (CategoryTheory.CategoryStruct.comp ψ i.hom)) ∧ ∃ hΦ : CategoryTheory.CategoryStruct.comp (CategoryTheory.CategoryStruct.comp i.inv (CategoryTheory.CategoryStruct.comp φ j.hom)) F.f = E.f, CerednikDrinfeld.QM.FakeEllipticCurve.PreservesLevel E F (CategoryTheory.CategoryStruct.comp i.inv (CategoryTheory.CategoryStruct.comp φ j.hom)) hΦ`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
