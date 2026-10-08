/-
Copyright 2026 Anthropic, PBC. Licensed under Apache-2.0; see LICENSE.
Source: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_CerednikDrinfeld_QM_RigidifiedPairClass_exists_ptR_eq.lean
Modified: replaced the proof with sorry and removed P2M proof imports.
Requires the upstream Definitions modules and their dependencies.
-/

import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMFineModuliT
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneCharts
import Definitions.Def_CerednikDrinfeld_RigidifiedPairClassModel
attribute [-instance] AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory
attribute [-simp] GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst
attribute [-simp] RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.PolarisedAbelianScheme.mk.injEq AlgebraicGeometry.PolarisedAbelianScheme.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq

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

end Submission
