import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

namespace Submission

/-- Transport finiteness, flatness, local finite presentation, and fibre rank along
an isomorphism of the base rings. -/
theorem p07_cre_finite_flat_rank_857cd4d38c
    (T U : Type) [CommRing T] [CommRing U] (k : T ≃+* U)
    (C : Scheme.{0}) (q : C ⟶ Spec (CommRingCat.of U)) :
    IsFinite q → Flat q → LocallyOfFinitePresentation q →
    let ε := Spec.map (CommRingCat.ofHom k.symm.toRingHom)
    let qT := q ≫ Spec.map (CommRingCat.ofHom k.toRingHom)
    IsFinite qT ∧ Flat qT ∧ LocallyOfFinitePresentation qT ∧
      (∀ s : Spec (CommRingCat.of T), qT.finrank s = q.finrank (ε s)) := by
  intro hfinite hflat hpresentation
  -- Contravariance gives `e.hom = Spec(k⁻¹)` and `e.inv = Spec(k)`.
  let e := Scheme.Spec.mapIso k.symm.toCommRingCatIso.op
  -- The identity on C identifies qT with the base change of q along e.hom.
  have hpb : IsPullback (𝟙 C) (q ≫ e.inv) q e.hom :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  let : IsFinite q := hfinite
  let : Flat q := hflat
  exact ⟨MorphismProperty.of_isPullback hpb hfinite,
    MorphismProperty.of_isPullback hpb hflat,
    MorphismProperty.of_isPullback hpb hpresentation,
    fun s => Scheme.Hom.finrank_of_isPullback (𝟙 C) (q ≫ e.inv) q e.hom hpb s⟩

end Submission
