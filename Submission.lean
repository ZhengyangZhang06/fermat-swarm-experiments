/-
Copyright 2026 Anthropic, PBC. Licensed under Apache-2.0; see LICENSE.
Source: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_CerednikDrinfeld_QM_RigidifiedPairClass_exists_ptR_eq.lean
Modified: isolated the selected precomposition naturality child theorem.
Requires the upstream Definitions modules and their dependencies.
-/

import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMFineModuliT
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneCharts
import Definitions.Def_CerednikDrinfeld_RigidifiedPairClassModel

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian

theorem CerednikDrinfeld.QM.RigidifiedPairClass.exists_ptR_eq
    {r N : ℕ} [Fact r.Prime] [NeZero N] (hrN : ¬ r ∣ N) {rbar : ℕ} [Fact rbar.Prime] (hrr : rbar ≠ r)

    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π}) (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr]
    {a b : ℚ} (hBq : IsIndefiniteRamifiedExactlyAt a b r rbar)
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)

    (coord : ↥Λ → Zp2 r × Zp2 r) (hcoord : IsOrderCoord Λ r coord)
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))

    (n : ℕ) (hn : 3 ≤ n) (hrn : ¬ r ∣ n) (M : Scheme.{0}) (fM : M ⟶ Spec (CommRingCat.of 𝒪))
    (ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N n S → SchemeHomOver s fM)
    (hM : IsFineModuli Λ N n M fM ptF)

    (C : Type) [CommRing C] [IsNoetherianRing C] [Algebra 𝒪 C] (hC : IsNilpotent (algebraMap 𝒪 C π)) (ψ : Onr →ₐ[𝒪] C)

    (X : ℕ → Scheme.{0}) (ξ : ∀ d, X d ⟶ Limits.pullback fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))))
    (tM : ∀ (T : Type) [CommRing T] [Algebra C T],
      FakeEllipticCurve.WithFullLevel Λ N n T → SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C T))) (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))))
    (xOf : ∀ (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
      (ψT : Onr →ₐ[𝒪] T) (_ : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
      (u : FakeEllipticCurve.WithFullLevel Λ N n T) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1),
      { x : Spec (CommRingCat.of (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)})) ⟶ X ρ.d //
        x ≫ ξ ρ.d = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}))) ≫ (tM T u).1 })
    (hmap : RigidifiedPairClass.MapCompat 𝒪 π Onr Λ hΛℤ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ tM xOf)

    (htM : ∀ (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
        (u : FakeEllipticCurve.WithFullLevel Λ N n T),
        (tM T u).1 ≫ Limits.pullback.fst fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))) = (ptF T (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 T))) u).1)

    (hx3 : (∀ (d : ℕ) (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
                (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
                (h0 : algebraMap C T (algebraMap 𝒪 C π) = 0) (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C T))) (ξ d ≫ Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))))),
                ∃ (u : FakeEllipticCurve.WithFullLevel Λ N n T) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1) (hd : ρ.d = d),
                  (RigidifiedPairClass.ptX 𝒪 π Onr Λ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ tM xOf) d T ψT hψT u ρ hd h0 = x))

    (hxOf : ∀ (S S' : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
        [CommRing S'] [Algebra C S'] [Algebra 𝒪 S'] [IsScalarTower 𝒪 C S'] (φ : S →ₐ[C] S')
        (ψS : Onr →ₐ[𝒪] S) (hψS : ψS = (IsScalarTower.toAlgHom 𝒪 C S).comp ψ)
        (hψS' : (φ.restrictScalars 𝒪).comp ψS = (IsScalarTower.toAlgHom 𝒪 C S').comp ψ)
        (u : FakeEllipticCurve.WithFullLevel Λ N n S) (u' : FakeEllipticCurve.WithFullLevel Λ N n S')
        (ρ : FakeEllipticCurve.Rigidification r π A₀ ψS u.1)
        (ρ' : FakeEllipticCurve.Rigidification r π A₀ ((φ.restrictScalars 𝒪).comp ψS) u'.1)
        (g : u'.1.A ⟶ u.1.A) (hg : FakeEllipticCurve.IsPullbackVia (φ : S →+* S') u.1 u'.1 g),
        (u'.2.P).1 ≫ g = Spec.map (CommRingCat.ofHom (φ : S →+* S')) ≫ (u.2.P).1 →
        FakeEllipticCurve.Rigidification.IsPullbackVia (φ.restrictScalars 𝒪) g hg ρ ρ' →
          ∃ hd : ρ'.d = ρ.d, (xOf S' ((φ.restrictScalars 𝒪).comp ψS) hψS' u' ρ').1 ≫ eqToHom (congrArg X hd) =
            Spec.map (CommRingCat.ofHom (RigidifiedPairClass.qmap (algebraMap 𝒪 C π) φ)) ≫ (xOf S ψS hψS u ρ).1) :
    (∀ (S : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
          (ψS : Onr →ₐ[𝒪] S) (hψS : ψS = (IsScalarTower.toAlgHom 𝒪 C S).comp ψ) (z : (RigidifiedPairClass.PR 𝒪 π Onr Λ hΛℤ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ tM xOf hmap).obj S),
          ∃ (u : FakeEllipticCurve.WithFullLevel Λ N n S) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψS u.1), (RigidifiedPairClass.ptR 𝒪 π Onr Λ hΛℤ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ tM xOf hmap) S ψS hψS u ρ = z) := by
  sorry

namespace Submission

/-- A relative group law pulls back along a ring homomorphism, with its point operations
identified by the pullback projection. -/
theorem p07_cq_group_law_pullback_857cd4d38c :
    ∀ (S T : Type) [CommRing S] [CommRing T] (φ : S →+* T)
      (A : Scheme.{0}) (f : A ⟶ Spec (CommRingCat.of S))
      (G : RelativeGroupLaw S f),
      let β := Spec.map (CommRingCat.ofHom φ)
      let p := Limits.pullback.snd f β
      let g := Limits.pullback.fst f β
      ∃ (H : RelativeGroupLaw T p)
        (B : ∀ (W : Scheme.{0}) (t : W ⟶ Spec (CommRingCat.of T)),
          SchemeHomOver t p ≃ SchemeHomOver (t ≫ β) f),
        (G.IsCommutative → H.IsCommutative) ∧
        (∀ (W : Scheme.{0}) (t : W ⟶ Spec (CommRingCat.of T))
          (P : SchemeHomOver t p), (B W t P).1 = P.1 ≫ g) ∧
        (∀ (W : Scheme.{0}) (t : W ⟶ Spec (CommRingCat.of T))
          (P Q : SchemeHomOver t p),
          B W t (H.mul t P Q) = G.mul (t ≫ β) (B W t P) (B W t Q)) ∧
        (∀ (W : Scheme.{0}) (t : W ⟶ Spec (CommRingCat.of T)),
          B W t (H.one t) = G.one (t ≫ β)) ∧
        (∀ (W : Scheme.{0}) (t : W ⟶ Spec (CommRingCat.of T))
          (P : SchemeHomOver t p),
          B W t (H.inv t P) = G.inv (t ≫ β) (B W t P)) := by
  intro S T _ _ φ A f G β p g
  -- The projection and universal lift identify points over the two bases.
  let B : ∀ (W : Scheme.{0}) (t : W ⟶ Spec (CommRingCat.of T)),
      SchemeHomOver t p ≃ SchemeHomOver (t ≫ β) f := fun W t =>
    { toFun := fun P => ⟨P.1 ≫ g, by
        change (P.1 ≫ Limits.pullback.fst f β) ≫ f = t ≫ β
        rw [Category.assoc, Limits.pullback.condition, ← Category.assoc, P.2]⟩
      invFun := fun R =>
        ⟨Limits.pullback.lift R.1 t R.2, Limits.pullback.lift_snd _ _ _⟩
      left_inv := fun P => Subtype.ext (Limits.pullback.hom_ext
        (Limits.pullback.lift_fst _ _ _)
        ((Limits.pullback.lift_snd _ _ _).trans P.2.symm))
      right_inv := fun R => Subtype.ext (Limits.pullback.lift_fst _ _ _) }
  have B_natural {W W' : Scheme.{0}}
      (t : W ⟶ Spec (CommRingCat.of T)) (t' : W' ⟶ Spec (CommRingCat.of T))
      (h : W' ⟶ W) (hh : h ≫ t = t') (P : SchemeHomOver t p) :
      B W' t' (GoodReductionJacobian.schemeHomOverComp h hh P) =
        GoodReductionJacobian.schemeHomOverComp h
          (by rw [← Category.assoc, hh]) (B W t P) :=
    Subtype.ext (Category.assoc h P.1 g)
  -- Transport the operations; injectivity reduces their laws to those of G.
  let H : RelativeGroupLaw T p :=
    { mul := fun {W} t P Q =>
        (B W t).symm (G.mul (t ≫ β) (B W t P) (B W t Q))
      one := fun {W} t => (B W t).symm (G.one (t ≫ β))
      inv := fun {W} t P => (B W t).symm (G.inv (t ≫ β) (B W t P))
      mul_assoc := by
        intro W t P Q R
        apply (B W t).injective
        simp only [Equiv.apply_symm_apply, G.mul_assoc]
      one_mul := by
        intro W t P
        apply (B W t).injective
        simp only [Equiv.apply_symm_apply, G.one_mul]
      mul_one := by
        intro W t P
        apply (B W t).injective
        simp only [Equiv.apply_symm_apply, G.mul_one]
      inv_mul_cancel := by
        intro W t P
        apply (B W t).injective
        simp only [Equiv.apply_symm_apply, G.inv_mul_cancel]
      mul_natural := by
        intro W W' t t' h hh P Q
        apply (B W' t').injective
        rw [B_natural]
        simp only [Equiv.apply_symm_apply]
        rw [G.mul_natural, B_natural, B_natural] }
  refine ⟨H, B, ?_, ?_, ?_, ?_, ?_⟩
  · intro hG W t P Q
    apply (B W t).injective
    change B W t ((B W t).symm _) = B W t ((B W t).symm _)
    simpa only [Equiv.apply_symm_apply] using hG (t ≫ β) (B W t P) (B W t Q)
  · intro W t P
    rfl
  · intro W t P Q
    exact (B W t).apply_symm_apply _
  · intro W t
    exact (B W t).apply_symm_apply _
  · intro W t P
    exact (B W t).apply_symm_apply _

end Submission


namespace Submission

/-- Quotient base change preserves the abelian-scheme bundle and two-dimensional fibres. -/
theorem p07_cq_abelian_surface_quotient_857cd4d38c
    (S : Type) [CommRing S] (J : Ideal S) (A : Scheme.{0})
    (f : A ⟶ Spec (CommRingCat.of S))
    (h : AbelianSchemePropertyBundle S f)
    (hdim : ∀ s : Spec (CommRingCat.of S), topologicalKrullDim ↥(f.base ⁻¹' {s}) = 2) :
    let β := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))
    let p := Limits.pullback.snd f β
    AbelianSchemePropertyBundle (S ⧸ J) p ∧
      (∀ t : Spec (CommRingCat.of (S ⧸ J)), topologicalKrullDim ↥(p.base ⁻¹' {t}) = 2) := by
  let β := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))
  let p := Limits.pullback.snd f β
  let g := Limits.pullback.fst f β
  change AbelianSchemePropertyBundle (S ⧸ J) p ∧ _
  have : IsProper f := h.proper
  have : IsClosedImmersion β :=
    IsClosedImmersion.spec_of_quotient_mk (R := CommRingCat.of S) J
  have : IsClosedImmersion g := inferInstanceAs (IsClosedImmersion (Limits.pullback.fst f β))
  have hcomm (y : ↥(Limits.pullback f β)) : f (g y) = β (p y) :=
    congrArg (fun k : Limits.pullback f β ⟶ Spec (CommRingCat.of S) => k y)
      (Limits.pullback.condition (f := f) (g := β))
  have hfibres (t : Spec (CommRingCat.of (S ⧸ J))) :
      _root_.IsConnected (p.base ⁻¹' {t}) ∧ topologicalKrullDim ↥(p.base ⁻¹' {t}) = 2 := by
    have hmaps : Set.MapsTo g (p.base ⁻¹' {t}) (f.base ⁻¹' {β t}) := by
      intro y hy
      change f (g y) = β t
      change p y = t at hy
      rw [hcomm, hy]
    let F : ↥(p.base ⁻¹' {t}) → ↥(f.base ⁻¹' {β t}) := hmaps.restrict
    have hemb : Topology.IsEmbedding F := g.isClosedEmbedding.isEmbedding.restrict hmaps
    have hsurj : Function.Surjective F := by
      intro x
      have hx : (x : A) ∈ Set.range g := by
        change (x : A) ∈ Set.range (Limits.pullback.fst f β)
        rw [Scheme.Pullback.range_fst]
        exact ⟨t, x.property.symm⟩
      obtain ⟨y, hy⟩ := hx
      have hyt : p y = t := by
        apply β.isClosedEmbedding.injective
        rw [← hcomm, hy]
        exact x.property
      refine ⟨⟨y, hyt⟩, ?_⟩
      exact Subtype.ext hy
    have hhomeo : IsHomeomorph F := isHomeomorph_iff_isEmbedding_surjective.mpr ⟨hemb, hsurj⟩
    constructor
    · apply isConnected_iff_connectedSpace.mpr
      exact (hhomeo.homeomorph F).connectedSpace_iff.mpr
        (isConnected_iff_connectedSpace.mp (h.connectedFibres (β t)))
    · exact (hhomeo.topologicalKrullDim_eq F).trans (hdim (β t))
  obtain ⟨G⟩ := h.hasGroupLaw
  obtain ⟨H, _⟩ := Submission.p07_cq_group_law_pullback_857cd4d38c
    S (S ⧸ J) (Ideal.Quotient.mk J) A f G
  refine ⟨⟨?_, ?_, fun t => (hfibres t).1, ⟨H⟩⟩, fun t => (hfibres t).2⟩
  · exact MorphismProperty.pullback_snd _ _ h.smooth
  · infer_instance
open CategoryTheory.Limits

/-- The level immersion and its finite flat structure morphism commute with base change.

The cartesian square follows from `IsPullback.of_bot`
(`Mathlib/CategoryTheory/Limits/Shapes/Pullback/IsPullback/Basic.lean`), which packages
the existence and uniqueness argument in steps 3–4 of the accepted natural proof.
The rank formula is `Scheme.Hom.finrank_pullback_snd`
(`Mathlib/AlgebraicGeometry/Morphisms/FlatRank.lean`). Closed immersion transfers via
`MorphismProperty.of_isPullback` (`Mathlib/CategoryTheory/MorphismProperty/Limits.lean`)
and `IsClosedImmersion.isStableUnderBaseChange`
(`Mathlib/AlgebraicGeometry/Morphisms/ClosedImmersion.lean`). The three structure-map
instances are in `Mathlib/AlgebraicGeometry/Morphisms/{Finite,Flat,FinitePresentation}.lean`.
All these results are from the pinned mathlib revision
`db584cd6d46c92f209a44c0f1c829460d327499d`. -/
theorem p07_cq_level_geometry_pullback_857cd4d38c :
    ∀ (S T : Type) [CommRing S] [CommRing T] (φ : S →+* T)
      (A C : AlgebraicGeometry.Scheme.{0})
      (f : A ⟶ AlgebraicGeometry.Spec (CommRingCat.of S)) (ℓ : C ⟶ A),
      AlgebraicGeometry.IsClosedImmersion ℓ →
      AlgebraicGeometry.IsFinite (ℓ ≫ f) →
      AlgebraicGeometry.Flat (ℓ ≫ f) →
      AlgebraicGeometry.LocallyOfFinitePresentation (ℓ ≫ f) →
      let β := AlgebraicGeometry.Spec.map (CommRingCat.ofHom φ)
      let c := ℓ ≫ f
      let p := pullback.snd f β
      let g := pullback.fst f β
      let r := pullback.fst c β
      let d := pullback.snd c β
      ∃ ℓT : pullback c β ⟶ pullback f β,
        CategoryTheory.IsPullback r ℓT ℓ g ∧ ℓT ≫ p = d ∧
        AlgebraicGeometry.IsClosedImmersion ℓT ∧ AlgebraicGeometry.IsFinite d ∧
        AlgebraicGeometry.Flat d ∧ AlgebraicGeometry.LocallyOfFinitePresentation d ∧
        (∀ t : AlgebraicGeometry.Spec (CommRingCat.of T),
          AlgebraicGeometry.Scheme.Hom.finrank d t =
            AlgebraicGeometry.Scheme.Hom.finrank c (β t)) ∧
        (∀ (W : AlgebraicGeometry.Scheme.{0}) (Q : W ⟶ pullback f β),
          (∃ R : W ⟶ pullback c β, R ≫ ℓT = Q) ↔
            (∃ R : W ⟶ C, R ≫ ℓ = Q ≫ g)) := by
  intro S T _ _ φ A C f ℓ hℓ hfinite hflat hfp
  dsimp only
  let β := AlgebraicGeometry.Spec.map (CommRingCat.ofHom φ)
  let c := ℓ ≫ f
  let ℓT : pullback c β ⟶ pullback f β :=
    pullback.lift (pullback.fst c β ≫ ℓ) (pullback.snd c β) (by
      rw [Category.assoc]
      exact pullback.condition)
  have hfst : ℓT ≫ pullback.fst f β = pullback.fst c β ≫ ℓ :=
    pullback.lift_fst _ _ _
  have hsnd : ℓT ≫ pullback.snd f β = pullback.snd c β :=
    pullback.lift_snd _ _ _
  -- Cancel the lower pullback square from the outer square for c = ℓ ≫ f.
  have hpb : IsPullback (pullback.fst c β) ℓT ℓ (pullback.fst f β) := by
    apply IsPullback.of_bot (s := ?_) hfst.symm (IsPullback.of_hasPullback f β)
    rw [hsnd]
    exact IsPullback.of_hasPullback c β
  -- The structure morphism is the canonical base change of the finite flat c.
  refine ⟨ℓT, hpb, hsnd, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact MorphismProperty.of_isPullback hpb hℓ
  · exact MorphismProperty.pullback_snd c β hfinite
  · exact MorphismProperty.pullback_snd c β hflat
  · exact MorphismProperty.pullback_snd c β hfp
  · exact Scheme.Hom.finrank_pullback_snd c β
  · intro W Q
    constructor
    · rintro ⟨U, hU⟩
      refine ⟨U ≫ pullback.fst c β, ?_⟩
      rw [Category.assoc, hpb.w, ← Category.assoc, hU]
    · rintro ⟨R, hR⟩
      -- A factorization through ℓ supplies exactly the compatibility for this lift.
      exact ⟨hpb.lift R Q hR, hpb.lift_snd R Q hR⟩

end Submission


namespace Submission

/-- Quotient base change of a fake elliptic curve, using the three curve-quotient
DAG prerequisites for the group law, surface geometry, and level geometry. -/
theorem p07_flq_curve_quotient_857cd4d38c
    {a b : ℚ} (Λ : Submodule ℤ (QuaternionAlgebra ℚ a 0 b)) (N : ℕ)
    (S : Type) [CommRing S] (J : Ideal S) (E : FakeEllipticCurve Λ N S) :
    ∃ (EJ : FakeEllipticCurve Λ N (S ⧸ J)) (g : EJ.A ⟶ E.A),
      FakeEllipticCurve.IsPullbackVia (Ideal.Quotient.mk J) E EJ g := by
  classical
  let q := Ideal.Quotient.mk J
  let β := Spec.map (CommRingCat.ofHom q)
  let A := Limits.pullback E.f β
  let p : A ⟶ Spec (CommRingCat.of (S ⧸ J)) := Limits.pullback.snd E.f β
  let g : A ⟶ E.A := Limits.pullback.fst E.f β
  have hg : CategoryTheory.IsPullback g p E.f β := CategoryTheory.IsPullback.of_hasPullback _ _
  obtain ⟨H, B, hcomm, hcoe, hmul, hone, hinv⟩ :=
    p07_cq_group_law_pullback_857cd4d38c S (S ⧸ J) q E.A E.f E.L
  obtain ⟨hbundle, hdim⟩ :=
    p07_cq_abelian_surface_quotient_857cd4d38c S J E.A E.f E.bundle E.dim_fibre
  obtain ⟨ℓ, _, hℓp, hclosed, hfinite, hflat, hfp, hrank, hfactor⟩ :=
    p07_cq_level_geometry_pullback_857cd4d38c S (S ⧸ J) q E.A E.C E.f E.lev
      E.lev_closed E.lev_finite E.lev_flat E.lev_finitePresentation
  -- The action is the unique lift with the prescribed two projections.
  let act (x : ↥Λ) : A ⟶ A := Limits.pullback.lift (g ≫ E.act x) p
    (by rw [Category.assoc, E.act_over]; exact hg.w)
  have act_g (x : ↥Λ) : act x ≫ g = g ≫ E.act x := Limits.pullback.lift_fst _ _ _
  have act_p (x : ↥Λ) : act x ≫ p = p := Limits.pullback.lift_snd _ _ _
  have b_act (W : Scheme.{0}) (t : W ⟶ Spec (CommRingCat.of (S ⧸ J)))
      (x : ↥Λ) (P : SchemeHomOver t p) :
      B W t (pushPt (act x) (act_p x) P) =
        pushPt (E.act x) (E.act_over x) (B W t P) := by
    apply Subtype.ext
    simp only [hcoe, pushPt, mapPt_coe]
    change (P.1 ≫ act x) ≫ g = (P.1 ≫ g) ≫ E.act x
    rw [Category.assoc, act_g, Category.assoc]
  have factors (W : Scheme.{0}) (t : W ⟶ Spec (CommRingCat.of (S ⧸ J)))
      (P : SchemeHomOver t p) : FactorsThrough ℓ P ↔ FactorsThrough E.lev (B W t P) := by
    change (∃ R, R ≫ ℓ = P.1) ↔ ∃ R, R ≫ E.lev = (B W t P).1
    rw [hcoe]
    exact hfactor W P.1
  -- Allow the target base morphism to be written as an equal Spec-composite.
  let B' (W : Scheme.{0}) (t : W ⟶ Spec (CommRingCat.of (S ⧸ J)))
      (s : W ⟶ Spec (CommRingCat.of S)) (h : t ≫ β = s) :
      SchemeHomOver t p ≃ SchemeHomOver s E.f :=
    (B W t).trans
      { toFun := fun P => ⟨P.1, P.2.trans h⟩
        invFun := fun P => ⟨P.1, P.2.trans h.symm⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have b'_coe (W) (t) (s) (h) (P : SchemeHomOver t p) :
      (B' W t s h P).1 = P.1 ≫ g := hcoe W t P
  have b'_mul (W) (t) (s) (h) (P Q : SchemeHomOver t p) :
      B' W t s h (H.mul t P Q) = E.L.mul s (B' W t s h P) (B' W t s h Q) := by
    subst s
    exact hmul W t P Q
  have b'_one (W) (t) (s) (h) : B' W t s h (H.one t) = E.L.one s := by
    subst s
    exact hone W t
  have b'_act (W) (t) (s) (h) (x : ↥Λ) (P : SchemeHomOver t p) :
      B' W t s h (pushPt (act x) (act_p x) P) =
        pushPt (E.act x) (E.act_over x) (B' W t s h P) := by
    subst s
    exact b_act W t x P
  have geom_comp (k : Type) [Field k] (sk : (S ⧸ J) →+* k) :
      geomPoint k sk ≫ β = geomPoint k (sk.comp q) := by
    simp only [geomPoint, β, CommRingCat.ofHom_comp, Spec.map_comp]
  have tangent_comp (k : Type) [Field k] (sk : (S ⧸ J) →+* k) :
      tangentBase k sk ≫ β = tangentBase k (sk.comp q) := by
    simp only [tangentBase, β, CommRingCat.ofHom_comp,
      Spec.map_comp, Category.assoc]
  let EJ : FakeEllipticCurve Λ N (S ⧸ J) := {
    A := A
    f := p
    L := H
    comm := hcomm E.comm
    bundle := hbundle
    dim_fibre := hdim
    act := act
    act_over := act_p
    act_hom := by
      intro x W t P Q
      apply (B W t).injective
      simp only [b_act, hmul, E.act_hom]
    act_one := by
      intro h
      apply Limits.pullback.hom_ext
      · change act ⟨1, h⟩ ≫ g = (𝟙 A) ≫ g
        rw [act_g, E.act_one, Category.comp_id, Category.id_comp]
      · change act ⟨1, h⟩ ≫ p = (𝟙 A) ≫ p
        rw [act_p, Category.id_comp]
    act_mul := by
      intro x y h
      apply Limits.pullback.hom_ext
      · change act ⟨_, h⟩ ≫ g = (act y ≫ act x) ≫ g
        rw [act_g, E.act_mul, Category.assoc, act_g]
        rw [← Category.assoc (act y) g (E.act x), act_g, Category.assoc]
      · change act ⟨_, h⟩ ≫ p = (act y ≫ act x) ≫ p
        rw [act_p, Category.assoc, act_p, act_p]
    act_add := by
      intro x y W t P
      apply (B W t).injective
      rw [b_act, hmul, b_act, b_act, E.act_add]
    act_trace := by
      intro k _ _ sk V _ _ _ τ hτ hτrange hτadd hτscale m Φ hΦ n hn
      let D := B' _ (tangentBase k sk) (tangentBase k (sk.comp q)) (tangent_comp k sk)
      have dcoe (P) : (D P).1 = P.1 ≫ g :=
        b'_coe _ _ _ (tangent_comp k sk) P
      have done : (H.one (geomPoint k sk)).1 ≫ g =
          (E.L.one (geomPoint k (sk.comp q))).1 := by
        rw [← b'_coe _ _ _ (geom_comp k sk), b'_one _ _ _ (geom_comp k sk)]
      have tangent_iff (P : SchemeHomOver (tangentBase k sk) p) :
          IsTangentVector H k sk P ↔ IsTangentVector E.L k (sk.comp q) (D P) := by
        change tangentZero k ≫ P.1 = (H.one (geomPoint k sk)).1 ↔
          tangentZero k ≫ (D P).1 = (E.L.one (geomPoint k (sk.comp q))).1
        rw [dcoe, ← done, ← Category.assoc]
        constructor
        · intro h
          rw [h]
        · intro h
          apply Limits.pullback.hom_ext
          · exact h
          · change (tangentZero k ≫ P.1) ≫ p = (H.one (geomPoint k sk)).1 ≫ p
            rw [Category.assoc, P.2, (H.one (geomPoint k sk)).2]
            simp only [tangentZero, tangentBase, geomPoint, ← Spec.map_comp,
              ← CommRingCat.ofHom_comp]
            congr 1
      apply E.act_trace k (sk.comp q) V (fun v => D (τ v))
        (D.injective.comp hτ) _ _ _ m Φ _ n hn
      · intro P
        constructor
        · rintro ⟨v, rfl⟩
          exact (tangent_iff (τ v)).mp ((hτrange _).mp ⟨v, rfl⟩)
        · intro h
          have ht : IsTangentVector H k sk (D.symm P) :=
            (tangent_iff _).mpr (by simpa only [D.apply_symm_apply] using h)
          obtain ⟨v, hv⟩ := (hτrange _).mpr ht
          exact ⟨v, (congrArg D hv).trans (D.apply_symm_apply P)⟩
      · intro v w
        rw [hτadd]
        exact b'_mul _ _ _ (tangent_comp k sk) _ _
      · intro c v
        rw [dcoe, dcoe, hτscale, Category.assoc]
      · intro v
        rw [hΦ]
        exact b'_act _ _ _ (tangent_comp k sk) _ _
    C := Limits.pullback (E.lev ≫ E.f) β
    lev := ℓ
    lev_closed := hclosed
    lev_sub := by
      intro W t P Q hP hQ
      obtain ⟨hm, hi⟩ := E.lev_sub (t ≫ β) (B W t P) (B W t Q)
        ((factors W t P).mp hP) ((factors W t Q).mp hQ)
      constructor
      · apply (factors W t _).mpr
        rw [hmul]
        exact hm
      · apply (factors W t _).mpr
        rw [hinv]
        exact hi
    lev_one := by
      intro W t
      apply (factors W t _).mpr
      rw [hone]
      exact E.lev_one _
    lev_torsion := by
      intro W t P hP
      have hnsmul (k : ℕ) : B W t (nsmulPt H t k P) =
          nsmulPt E.L (t ≫ β) k (B W t P) := by
        induction k with
        | zero => exact hone W t
        | succ k ih =>
          simp only [nsmulPt, hmul, ih, β]
      apply (B W t).injective
      rw [hnsmul, hone]
      exact E.lev_torsion _ _ ((factors W t P).mp hP)
    lev_stable := by
      intro x W t P hP
      apply (factors W t _).mpr
      rw [b_act]
      exact E.lev_stable x _ _ ((factors W t P).mp hP)
    lev_finite := by rw [hℓp]; exact hfinite
    lev_flat := by rw [hℓp]; exact hflat
    lev_finitePresentation := by rw [hℓp]; exact hfp
    lev_rank := by intro t; rw [hℓp, hrank, E.lev_rank]
    lev_fibre := by
      intro k _ _ sk hN
      let D := B' _ (geomPoint k sk) (geomPoint k (sk.comp q)) (geom_comp k sk)
      have dfactor (P : SchemeHomOver (geomPoint k sk) p) :
          FactorsThrough ℓ P ↔ FactorsThrough E.lev (D P) := by
        change (∃ R, R ≫ ℓ = P.1) ↔ ∃ R, R ≫ E.lev = (D P).1
        rw [b'_coe _ _ _ (geom_comp k sk)]
        exact hfactor _ P.1
      let F : {P : SchemeHomOver (geomPoint k sk) p // FactorsThrough ℓ P} ≃
          {P : SchemeHomOver (geomPoint k (sk.comp q)) E.f // FactorsThrough E.lev P} := {
        toFun := fun P => ⟨D P.1, (dfactor P.1).mp P.2⟩
        invFun := fun P => ⟨D.symm P.1, (dfactor _).mpr
          (by simpa only [D.apply_symm_apply] using P.2)⟩
        left_inv := fun P => Subtype.ext (D.symm_apply_apply P.1)
        right_inv := fun P => Subtype.ext (D.apply_symm_apply P.1) }
      obtain ⟨e, he⟩ := E.lev_fibre k (sk.comp q) hN
      refine ⟨e.trans F.symm, ?_⟩
      intro x y
      apply D.injective
      change D (D.symm (e (x + y)).1) =
        D (H.mul (geomPoint k sk) (D.symm (e x).1) (D.symm (e y).1))
      rw [D.apply_symm_apply, b'_mul _ _ _ (geom_comp k sk),
        D.apply_symm_apply, D.apply_symm_apply]
      exact he x y }
  refine ⟨EJ, g, hg, ?_, act_g, ?_⟩
  · intro W t P Q
    have hP : B W t P = ⟨P.1 ≫ g, by
      rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩ := Subtype.ext (hcoe W t P)
    have hQ : B W t Q = ⟨Q.1 ≫ g, by
      rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩ := Subtype.ext (hcoe W t Q)
    change (H.mul t P Q).1 ≫ g = _
    rw [← hcoe W t, hmul, hP, hQ]
  · intro W t P hP
    exact (hfactor W P.1).mp hP
/-- A pullback of fake elliptic curves induces an equivalence on points that
preserves multiplication, identity, repeated sums, and the order action. -/
theorem p07_flp_point_equiv_857cd4d38c
    {a b : ℚ} (Λ : Submodule ℤ (QuaternionAlgebra ℚ a 0 b)) (N : ℕ)
    (S T : Type) [CommRing S] [CommRing T] (φ : S →+* T)
    (E : FakeEllipticCurve Λ N S) (ET : FakeEllipticCurve Λ N T)
    (g : ET.A ⟶ E.A) (hg : FakeEllipticCurve.IsPullbackVia φ E ET g)
    (W : Scheme.{0}) (t : W ⟶ Spec (CommRingCat.of T)) :
    let tS := t ≫ Spec.map (CommRingCat.ofHom φ)
    ∃ B : SchemeHomOver t ET.f ≃ SchemeHomOver tS E.f,
      (∀ P : SchemeHomOver t ET.f, (B P).1 = P.1 ≫ g) ∧
      (∀ P Q : SchemeHomOver t ET.f,
        B (ET.L.mul t P Q) = E.L.mul tS (B P) (B Q)) ∧
      B (ET.L.one t) = E.L.one tS ∧
      (∀ (k : ℕ) (P : SchemeHomOver t ET.f),
        B (nsmulPt ET.L t k P) = nsmulPt E.L tS k (B P)) ∧
      (∀ (x : ↥Λ) (P : SchemeHomOver t ET.f),
        B (pushPt (ET.act x) (ET.act_over x) P) =
          pushPt (E.act x) (E.act_over x) (B P)) := by
  classical
  dsimp only
  rcases hg with ⟨h, hmul, hact, _⟩
  let tS := t ≫ Spec.map (CommRingCat.ofHom φ)
  let F : SchemeHomOver t ET.f → SchemeHomOver tS E.f := fun P =>
    ⟨P.1 ≫ g, by rw [Category.assoc, h.w, ← Category.assoc, P.2]⟩
  let I : SchemeHomOver tS E.f → SchemeHomOver t ET.f := fun R =>
    ⟨h.lift R.1 t R.2, h.lift_snd R.1 t R.2⟩
  let B : SchemeHomOver t ET.f ≃ SchemeHomOver tS E.f :=
    { toFun := F
      invFun := I
      left_inv := by
        intro P
        apply Subtype.ext
        apply h.hom_ext
        · exact h.lift_fst (F P).1 t (F P).2
        · exact (h.lift_snd (F P).1 t (F P).2).trans P.2.symm
      right_inv := by
        intro R
        apply Subtype.ext
        exact h.lift_fst R.1 t R.2 }
  have map_mul (P Q : SchemeHomOver t ET.f) :
      B (ET.L.mul t P Q) = E.L.mul tS (B P) (B Q) :=
    Subtype.ext (hmul t P Q)
  have map_one : B (ET.L.one t) = E.L.one tS := by
    let H := B (ET.L.one t)
    have hH : E.L.mul tS H H = H := by
      rw [← map_mul, ET.L.one_mul]
    calc
      H = E.L.mul tS (E.L.one tS) H := (E.L.one_mul tS H).symm
      _ = E.L.mul tS (E.L.mul tS (E.L.inv tS H) H) H := by
        rw [E.L.inv_mul_cancel]
      _ = E.L.mul tS (E.L.inv tS H) (E.L.mul tS H H) :=
        E.L.mul_assoc tS _ _ _
      _ = E.L.mul tS (E.L.inv tS H) H := by rw [hH]
      _ = E.L.one tS := E.L.inv_mul_cancel tS H
  refine ⟨B, fun _ => rfl, map_mul, map_one, ?_, ?_⟩
  · intro k P
    induction k with
    | zero => exact map_one
    | succ k ih =>
      change B (ET.L.mul t (nsmulPt ET.L t k P) P) =
        E.L.mul tS (nsmulPt E.L tS k (B P)) (B P)
      rw [map_mul, ih]
  · intro x P
    apply Subtype.ext
    change (P.1 ≫ ET.act x) ≫ g = (P.1 ≫ g) ≫ E.act x
    rw [Category.assoc, hact, Category.assoc]
namespace Submission

/-- Repeated addition commutes with compatible precomposition of points.
The induction uses the existing `RelativeGroupLaw.one_natural` theorem and `mul_natural`
field from `Definitions.Def_AlgebraicGeometry_RelativeGroupLaw`, with the recursion in
`Definitions.Def_CerednikDrinfeld_QMModuli`. -/
theorem p07_flp_nsmul_precomp_857cd4d38c :
    ∀ (R : Type) [CommRing R] (A W W' : AlgebraicGeometry.Scheme.{0})
      (f : Quiver.Hom A (AlgebraicGeometry.Spec (CommRingCat.of R)))
      (L : GoodReductionJacobian.RelativeGroupLaw R f)
      (t : Quiver.Hom W (AlgebraicGeometry.Spec (CommRingCat.of R)))
      (t' : Quiver.Hom W' (AlgebraicGeometry.Spec (CommRingCat.of R)))
      (ψ : Quiver.Hom W' W) (hψ : CategoryTheory.CategoryStruct.comp ψ t = t')
      (k : ℕ) (P : NeronModelInfra.SchemeHomOver t f),
      GoodReductionJacobian.schemeHomOverComp ψ hψ (CerednikDrinfeld.QM.nsmulPt L t k P) =
        CerednikDrinfeld.QM.nsmulPt L t' k (GoodReductionJacobian.schemeHomOverComp ψ hψ P) := by
  intro R _ A W W' f L t t' ψ hψ k P
  induction k with
  -- At zero, precomposition preserves the identity point.
  | zero => exact L.one_natural t t' ψ hψ
  | succ k ih =>
      -- The recursive step commutes with precomposition by multiplication naturality.
      rw [CerednikDrinfeld.QM.nsmulPt, CerednikDrinfeld.QM.nsmulPt, L.mul_natural, ih]

end Submission
