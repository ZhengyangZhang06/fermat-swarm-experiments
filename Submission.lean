import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

namespace Submission

/-- Transport finite flat rank along an isomorphism of the base rings. -/
theorem p07_cre_finite_flat_rank_857cd4d38c
    (T U : Type) [CommRing T] [CommRing U] (k : T ≃+* U)
    (C : Scheme.{0}) (q : C ⟶ Spec (CommRingCat.of U)) :
    IsFinite q → Flat q → LocallyOfFinitePresentation q →
    let ε := Spec.map (CommRingCat.ofHom k.symm.toRingHom)
    let qT := q ≫ Spec.map (CommRingCat.ofHom k.toRingHom)
    IsFinite qT ∧ Flat qT ∧ LocallyOfFinitePresentation qT ∧
      (∀ s : Spec (CommRingCat.of T), qT.finrank s = q.finrank (ε s)) := by
  intro hfinite hflat hpresentation
  let κ := Spec.map (CommRingCat.ofHom k.toRingHom)
  let ε := Spec.map (CommRingCat.ofHom k.symm.toRingHom)
  have hκε : κ ≫ ε = 𝟙 _ := by
    dsimp [κ, ε]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    change Spec.map (CommRingCat.ofHom (k.toRingHom.comp k.symm.toRingHom)) = _
    rw [k.toRingHom_comp_symm_toRingHom, CommRingCat.ofHom_id, Spec.map_id]
  have hεκ : ε ≫ κ = 𝟙 _ := by
    dsimp [κ, ε]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    change Spec.map (CommRingCat.ofHom (k.symm.toRingHom.comp k.toRingHom)) = _
    rw [k.symm_toRingHom_comp_toRingHom, CommRingCat.ofHom_id, Spec.map_id]
  let : IsIso ε := ⟨⟨κ, hεκ, hκε⟩⟩
  have hpb : IsPullback (𝟙 C) (q ≫ κ) q ε :=
    IsPullback.of_horiz_isIso ⟨by simp [Category.assoc, hκε]⟩
  let : IsFinite q := hfinite
  let : Flat q := hflat
  exact ⟨MorphismProperty.of_isPullback hpb hfinite,
    MorphismProperty.of_isPullback hpb hflat,
    MorphismProperty.of_isPullback hpb hpresentation,
    fun s => Scheme.Hom.finrank_of_isPullback (𝟙 C) (q ≫ κ) q ε hpb s⟩

end Submission
