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

namespace Submission

theorem p07_curve_ring_equiv_857cd4d38c
    {a b : ℚ} (Λ : Submodule ℤ (QuaternionAlgebra ℚ a 0 b)) (N : ℕ)
    (T U : Type) [CommRing T] [CommRing U] (k : T ≃+* U)
    (D : FakeEllipticCurve Λ N U) :
    ∃ (E : FakeEllipticCurve Λ N T) (i : CategoryTheory.Iso D.A E.A),
      FakeEllipticCurve.IsPullbackVia k.toRingHom E D i.hom ∧
      FakeEllipticCurve.IsPullbackVia k.symm.toRingHom D E i.inv := by
  classical
  let κ := Spec.map (CommRingCat.ofHom k.toRingHom)
  let ε := Spec.map (CommRingCat.ofHom k.symm.toRingHom)
  let fT := D.f ≫ κ
  have hκε : κ ≫ ε = 𝟙 _ := by
    simp only [κ, ε, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      k.toRingHom_comp_symm_toRingHom, CommRingCat.ofHom_id, Spec.map_id]
  have hεκ : ε ≫ κ = 𝟙 _ := by
    simp only [κ, ε, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      k.symm_toRingHom_comp_toRingHom, CommRingCat.ofHom_id, Spec.map_id]
  let : IsIso κ := ⟨⟨ε, hκε, hεκ⟩⟩
  let : IsIso ε := ⟨⟨κ, hεκ, hκε⟩⟩
  obtain ⟨H, B, hcomm, hB, hmul, hone, hinv⟩ :=
    p07_cre_group_law_857cd4d38c T U k D.A D.f D.L
  obtain ⟨hbundle, hdim⟩ :=
    p07_cre_abelian_surface_857cd4d38c T U k D.A D.f D.bundle D.dim_fibre
  obtain ⟨hfinite, hflat, hfp, hrank⟩ :=
    p07_cre_finite_flat_rank_857cd4d38c T U k D.C (D.lev ≫ D.f)
      D.lev_finite D.lev_flat D.lev_finitePresentation
  -- The supplied point equivalence also applies after identifying its base map.
  have transport (W : Scheme.{0}) (t : W ⟶ Spec (CommRingCat.of T))
      (u : W ⟶ Spec (CommRingCat.of U)) (hu : t ≫ ε = u) :
      ∃ J : SchemeHomOver t fT ≃ SchemeHomOver u D.f,
        (∀ P, (J P).1 = P.1) ∧
        (∀ P Q, J (H.mul t P Q) = D.L.mul u (J P) (J Q)) ∧
        J (H.one t) = D.L.one u := by
    subst u
    exact ⟨B W t, hB W t, hmul W t, hone W t⟩
  have hact (x : ↥Λ) : D.act x ≫ fT = fT := by
    dsimp [fT]
    rw [← Category.assoc, D.act_over]
  have hpush (W : Scheme.{0}) (t : W ⟶ Spec (CommRingCat.of T))
      (x : ↥Λ) (P : SchemeHomOver t fT) :
      B W t (pushPt (D.act x) (hact x) P) =
        pushPt (D.act x) (D.act_over x) (B W t P) := by
    apply Subtype.ext
    simp only [hB, pushPt, mapPt_coe]
  have hfactor (W : Scheme.{0}) (t : W ⟶ Spec (CommRingCat.of T))
      (P : SchemeHomOver t fT) :
      FactorsThrough D.lev (B W t P) ↔ FactorsThrough D.lev P := by
    unfold FactorsThrough
    rw [hB]
  have hnsmul (W : Scheme.{0}) (t : W ⟶ Spec (CommRingCat.of T))
      (n : ℕ) (P : SchemeHomOver t fT) :
      B W t (nsmulPt H t n P) = nsmulPt D.L (t ≫ ε) n (B W t P) := by
    induction n with
    | zero => exact hone W t
    | succ n ih => simp only [nsmulPt, hmul, ih, ε]
  let E : FakeEllipticCurve Λ N T := {
    A := D.A
    f := fT
    L := H
    comm := hcomm D.comm
    bundle := hbundle
    dim_fibre := hdim
    act := D.act
    act_over := hact
    act_hom := by
      intro x W t P Q
      apply (B W t).injective
      rw [hpush, hmul, hmul, hpush, hpush]
      exact D.act_hom x (t ≫ ε) _ _
    act_one := D.act_one
    act_mul := D.act_mul
    act_add := by
      intro x y W t P
      apply (B W t).injective
      rw [hpush, hmul, hpush, hpush]
      exact D.act_add x y (t ≫ ε) _
    act_trace := by
      intro K _ _ α V _ _ _ τ hτ hrτ hτadd hτscale m Φ hΦ n hn
      let αU := α.comp k.symm.toRingHom
      have hgeom : geomPoint K α ≫ ε = geomPoint K αU := by
        simp only [geomPoint, αU, ε, CommRingCat.ofHom_comp, Spec.map_comp]
      have htan : tangentBase K α ≫ ε = tangentBase K αU := by
        simp only [tangentBase, αU, ε, ← RingHom.comp_assoc,
          CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
      obtain ⟨J, hJ, hJmul, _⟩ := transport _ _ _ htan
      obtain ⟨J₀, hJ₀, _, hJone⟩ := transport _ _ _ hgeom
      have hOne : (H.one (geomPoint K α)).1 = (D.L.one (geomPoint K αU)).1 :=
        (hJ₀ _).symm.trans (congrArg Subtype.val hJone)
      let τU : V → SchemeHomOver (tangentBase K αU) D.f := fun v => J (τ v)
      apply D.act_trace K αU V τU (J.injective.comp hτ) ?_ ?_ ?_ m Φ ?_ n hn
      · intro P
        obtain ⟨Q, rfl⟩ := J.surjective P
        have hrange : J Q ∈ Set.range τU ↔ Q ∈ Set.range τ := by
          constructor
          · rintro ⟨v, hv⟩
            exact ⟨v, J.injective hv⟩
          · rintro ⟨v, rfl⟩
            exact ⟨v, rfl⟩
        rw [hrange, hrτ]
        simp only [IsTangentVector, hJ, hOne]
      · intro v w
        exact (congrArg J (hτadd v w)).trans (hJmul _ _)
      · intro c v
        simpa only [τU, hJ] using hτscale c v
      · intro v
        apply Subtype.ext
        simpa only [τU, hJ, pushPt, mapPt_coe] using
          congrArg Subtype.val (hΦ v)
    C := D.C
    lev := D.lev
    lev_closed := D.lev_closed
    lev_sub := by
      intro W t P Q hP hQ
      obtain ⟨hPQ, hPi⟩ := D.lev_sub (t ≫ ε) (B W t P) (B W t Q)
        ((hfactor W t P).mpr hP) ((hfactor W t Q).mpr hQ)
      constructor
      · apply (hfactor W t _).mp
        rwa [hmul]
      · apply (hfactor W t _).mp
        rwa [hinv]
    lev_one := by
      intro W t
      apply (hfactor W t _).mp
      rw [hone]
      exact D.lev_one _
    lev_torsion := by
      intro W t P hP
      apply (B W t).injective
      rw [hnsmul, hone]
      exact D.lev_torsion _ _ ((hfactor W t P).mpr hP)
    lev_stable := by
      intro x W t P hP
      apply (hfactor W t _).mp
      rw [hpush]
      exact D.lev_stable x _ _ ((hfactor W t P).mpr hP)
    lev_finite := by simpa only [fT, Category.assoc] using hfinite
    lev_flat := by simpa only [fT, Category.assoc] using hflat
    lev_finitePresentation := by simpa only [fT, Category.assoc] using hfp
    lev_rank := by
      intro s
      simpa only [fT, Category.assoc] using (hrank s).trans (D.lev_rank _)
    lev_fibre := by
      intro K _ _ α hN
      let αU := α.comp k.symm.toRingHom
      have hgeom : geomPoint K α ≫ ε = geomPoint K αU := by
        simp only [geomPoint, αU, ε, CommRingCat.ofHom_comp, Spec.map_comp]
      obtain ⟨J, hJ, hJmul, _⟩ := transport _ _ _ hgeom
      have hlevel (P : SchemeHomOver (geomPoint K α) fT) :
          FactorsThrough D.lev P ↔ FactorsThrough D.lev (J P) := by
        unfold FactorsThrough
        rw [hJ]
      let Jlev := J.subtypeEquiv hlevel
      obtain ⟨eD, heD⟩ := D.lev_fibre K αU hN
      let e := eD.trans Jlev.symm
      refine ⟨e, ?_⟩
      have he (x : ZMod N × ZMod N) : J (e x).1 = (eD x).1 := by
        exact congrArg Subtype.val (Jlev.apply_symm_apply (eD x))
      intro x y
      apply J.injective
      rw [hJmul, he, he, he]
      exact heD x y }
  refine ⟨E, CategoryTheory.Iso.refl D.A, ?_, ?_⟩
  · have hs : CategoryTheory.IsPullback (𝟙 D.A) D.f fT κ :=
      CategoryTheory.IsPullback.of_horiz_isIso ⟨by simp only [Category.id_comp, fT]⟩
    refine ⟨hs, ?_, ?_, ?_⟩
    · intro W t P Q
      obtain ⟨J, hJ, hJmul, _⟩ := transport W (t ≫ κ) t
        (by rw [Category.assoc, hκε, Category.comp_id])
      dsimp only [E, CategoryTheory.Iso.refl_hom]
      simp only [Category.comp_id]
      have hJP (R : SchemeHomOver t D.f)
          (R' : SchemeHomOver (t ≫ κ) fT) (hR : R'.1 = R.1) : J R' = R :=
        Subtype.ext ((hJ R').trans hR)
      exact ((hJ _).symm.trans (congrArg Subtype.val
        ((hJmul _ _).trans (by rw [hJP P _ rfl, hJP Q _ rfl])))).symm
    · intro x
      simp only [E, CategoryTheory.Iso.refl_hom, Category.comp_id, Category.id_comp]
    · intro W t P hP
      simpa only [E, CategoryTheory.Iso.refl_hom, Category.comp_id, FactorsThrough] using hP
  · have hs : CategoryTheory.IsPullback (𝟙 D.A) fT D.f ε :=
      CategoryTheory.IsPullback.of_horiz_isIso ⟨by
        simp only [Category.id_comp, fT, Category.assoc, hκε, Category.comp_id]⟩
    refine ⟨hs, ?_, ?_, ?_⟩
    · intro W t P Q
      dsimp only [E, CategoryTheory.Iso.refl_inv]
      simp only [Category.comp_id]
      apply Eq.trans ((hB W t _).symm.trans (congrArg Subtype.val (hmul W t P Q)))
      apply congrArg Subtype.val
      exact congrArg₂ (D.L.mul (t ≫ ε))
        (Subtype.ext (hB W t P)) (Subtype.ext (hB W t Q))
    · intro x
      simp only [E, CategoryTheory.Iso.refl_inv, Category.comp_id, Category.id_comp]
    · intro W t P hP
      simpa only [E, CategoryTheory.Iso.refl_inv, Category.comp_id, FactorsThrough] using hP

end Submission

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


theorem Submission.p07_rr_pullback_comp_857cd4d38c
    {a b : ℚ} (Λ : Submodule ℤ (QuaternionAlgebra ℚ a 0 b)) (N : ℕ)
    (S₀ S₁ S₂ : Type) [CommRing S₀] [CommRing S₁] [CommRing S₂]
    (f : S₀ →+* S₁) (h : S₁ →+* S₂)
    (E₀ : FakeEllipticCurve Λ N S₀) (E₁ : FakeEllipticCurve Λ N S₁)
    (E₂ : FakeEllipticCurve Λ N S₂) (g₀₁ : E₁.A ⟶ E₀.A) (g₁₂ : E₂.A ⟶ E₁.A) :
    FakeEllipticCurve.IsPullbackVia f E₀ E₁ g₀₁ →
    FakeEllipticCurve.IsPullbackVia h E₁ E₂ g₁₂ →
    FakeEllipticCurve.IsPullbackVia (h.comp f) E₀ E₂ (g₁₂ ≫ g₀₁) := by
  rintro ⟨hg₀₁, hmul₀₁, hact₀₁, hlev₀₁⟩ ⟨hg₁₂, hmul₁₂, hact₁₂, hlev₁₂⟩
  have hspec : Spec.map (CommRingCat.ofHom (h.comp f)) =
      Spec.map (CommRingCat.ofHom h) ≫ Spec.map (CommRingCat.ofHom f) :=
    Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom h)
  have hg : IsPullback (g₁₂ ≫ g₀₁) E₂.f E₀.f
      (Spec.map (CommRingCat.ofHom (h.comp f))) := by
    rw [hspec]
    exact hg₁₂.paste_horiz hg₀₁
  refine ⟨hg, ?_, ?_, ?_⟩
  · intro T t P Q
    let P₁ : SchemeHomOver (t ≫ Spec.map (CommRingCat.ofHom h)) E₁.f :=
      ⟨P.1 ≫ g₁₂, by rw [Category.assoc, hg₁₂.w, ← Category.assoc, P.2]⟩
    let Q₁ : SchemeHomOver (t ≫ Spec.map (CommRingCat.ofHom h)) E₁.f :=
      ⟨Q.1 ≫ g₁₂, by rw [Category.assoc, hg₁₂.w, ← Category.assoc, Q.2]⟩
    have hmul := (congrArg (fun k => k ≫ g₀₁) (hmul₁₂ t P Q)).trans
      (hmul₀₁ (t ≫ Spec.map (CommRingCat.ofHom h)) P₁ Q₁)
    have hmul_congr {s₀ s₁ : T ⟶ Spec (CommRingCat.of S₀)} (hs : s₀ = s₁)
        (P₀ Q₀ : SchemeHomOver s₀ E₀.f) (P₀' Q₀' : SchemeHomOver s₁ E₀.f)
        (hP : P₀.1 = P₀'.1) (hQ : Q₀.1 = Q₀'.1) :
        (E₀.L.mul s₀ P₀ Q₀).1 = (E₀.L.mul s₁ P₀' Q₀').1 := by
      cases hs
      cases Subtype.ext hP
      cases Subtype.ext hQ
      rfl
    refine (Category.assoc _ _ _).symm.trans (hmul.trans ?_)
    apply hmul_congr
    · rw [hspec, Category.assoc]
    · exact Category.assoc _ _ _
    · exact Category.assoc _ _ _
  · intro x
    rw [← Category.assoc, hact₁₂, Category.assoc, hact₀₁, ← Category.assoc]
  · intro T t P hP
    let P₁ : SchemeHomOver (t ≫ Spec.map (CommRingCat.ofHom h)) E₁.f :=
      ⟨P.1 ≫ g₁₂, by rw [Category.assoc, hg₁₂.w, ← Category.assoc, P.2]⟩
    obtain ⟨w₁, hw₁⟩ := hlev₁₂ t P hP
    obtain ⟨w₀, hw₀⟩ := hlev₀₁ (t ≫ Spec.map (CommRingCat.ofHom h)) P₁ ⟨w₁, hw₁⟩
    exact ⟨w₀, by simpa only [P₁, Category.assoc] using hw₀⟩
theorem Submission.p07_rr_isogeny_transport_857cd4d38c :
    ∀ {a b : ℚ} (Λ : Submodule ℤ (QuaternionAlgebra ℚ a 0 b)) (N d : ℕ) (T U : Type) [CommRing T] [CommRing U] (k : T ≃+* U) (E F : CerednikDrinfeld.QM.FakeEllipticCurve Λ N T) (D H : CerednikDrinfeld.QM.FakeEllipticCurve Λ N U) (i : CategoryTheory.Iso D.A E.A) (j : CategoryTheory.Iso H.A F.A), CerednikDrinfeld.QM.FakeEllipticCurve.IsPullbackVia k.toRingHom E D i.hom → CerednikDrinfeld.QM.FakeEllipticCurve.IsPullbackVia k.symm.toRingHom D E i.inv → CerednikDrinfeld.QM.FakeEllipticCurve.IsPullbackVia k.toRingHom F H j.hom → CerednikDrinfeld.QM.FakeEllipticCurve.IsPullbackVia k.symm.toRingHom H F j.inv → ∀ (φ : Quiver.Hom D.A H.A) (ψ : Quiver.Hom H.A D.A) (hφ : CategoryTheory.CategoryStruct.comp φ H.f = D.f), CerednikDrinfeld.QM.FakeEllipticCurve.IsIsogenyPair d D H φ ψ → CerednikDrinfeld.QM.FakeEllipticCurve.PreservesLevel D H φ hφ → CerednikDrinfeld.QM.FakeEllipticCurve.IsIsogenyPair d E F (CategoryTheory.CategoryStruct.comp i.inv (CategoryTheory.CategoryStruct.comp φ j.hom)) (CategoryTheory.CategoryStruct.comp j.inv (CategoryTheory.CategoryStruct.comp ψ i.hom)) ∧ ∃ hΦ : CategoryTheory.CategoryStruct.comp (CategoryTheory.CategoryStruct.comp i.inv (CategoryTheory.CategoryStruct.comp φ j.hom)) F.f = E.f, CerednikDrinfeld.QM.FakeEllipticCurve.PreservesLevel E F (CategoryTheory.CategoryStruct.comp i.inv (CategoryTheory.CategoryStruct.comp φ j.hom)) hΦ := by
  intro a b Λ N d T U _ _ k E F D H i j hi hv hj hw φ ψ hφ hiso hlevel
  rcases hi with ⟨hi, _, hi_act, _⟩
  rcases hv with ⟨hv, hv_mul, hv_act, hv_level⟩
  rcases hj with ⟨hj, _, hj_act, hj_level⟩
  rcases hw with ⟨hw, hw_mul, hw_act, _⟩
  rcases hiso with ⟨_, hψ, hφ_mul, hψ_mul, hφ_act, hψ_act, hscalar⟩
  have hbase : Spec.map (CommRingCat.ofHom k.symm.toRingHom) ≫
      Spec.map (CommRingCat.ofHom k.toRingHom) = 𝟙 (Spec (CommRingCat.of T)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp,
      RingEquiv.symm_toRingHom_comp_toRingHom, CommRingCat.ofHom_id, Spec.map_id]
  have hΦ : (i.inv ≫ φ ≫ j.hom) ≫ F.f = E.f := by
    calc
      (i.inv ≫ φ ≫ j.hom) ≫ F.f = i.inv ≫ φ ≫ H.f ≫
          Spec.map (CommRingCat.ofHom k.toRingHom) := by
        rw [Category.assoc, Category.assoc, hj.w]
      _ = (i.inv ≫ D.f) ≫ Spec.map (CommRingCat.ofHom k.toRingHom) := by
        rw [← Category.assoc φ H.f, hφ, ← Category.assoc]
      _ = E.f := by rw [hv.w, Category.assoc, hbase, Category.comp_id]
  have hΨ : (j.inv ≫ ψ ≫ i.hom) ≫ E.f = F.f := by
    calc
      (j.inv ≫ ψ ≫ i.hom) ≫ E.f = j.inv ≫ ψ ≫ D.f ≫
          Spec.map (CommRingCat.ofHom k.toRingHom) := by
        rw [Category.assoc, Category.assoc, hi.w]
      _ = (j.inv ≫ H.f) ≫ Spec.map (CommRingCat.ofHom k.toRingHom) := by
        rw [← Category.assoc ψ D.f, hψ, ← Category.assoc]
      _ = F.f := by rw [hw.w, Category.assoc, hbase, Category.comp_id]
  constructor
  · refine ⟨hΦ, hΨ, ?_, ?_, ?_, ?_, ?_⟩
    · intro X t P Q
      apply Subtype.ext
      apply (cancel_mono j.inv).mp
      change ((E.L.mul t P Q).1 ≫ (i.inv ≫ φ ≫ j.hom)) ≫ j.inv =
        (F.L.mul t (mapPt (i.inv ≫ φ ≫ j.hom) hΦ P)
          (mapPt (i.inv ≫ φ ≫ j.hom) hΦ Q)).1 ≫ j.inv
      rw [hw_mul]
      simp only [mapPt_coe, Category.assoc, Iso.hom_inv_id, Category.comp_id]
      rw [← Category.assoc, hv_mul]
      exact congrArg Subtype.val (hφ_mul _ _ _)
    · intro X t P Q
      apply Subtype.ext
      apply (cancel_mono i.inv).mp
      change ((F.L.mul t P Q).1 ≫ (j.inv ≫ ψ ≫ i.hom)) ≫ i.inv =
        (E.L.mul t (mapPt (j.inv ≫ ψ ≫ i.hom) hΨ P)
          (mapPt (j.inv ≫ ψ ≫ i.hom) hΨ Q)).1 ≫ i.inv
      rw [hv_mul]
      simp only [mapPt_coe, Category.assoc, Iso.hom_inv_id, Category.comp_id]
      rw [← Category.assoc, hw_mul]
      exact congrArg Subtype.val (hψ_mul _ _ _)
    · intro x
      calc
        E.act x ≫ (i.inv ≫ φ ≫ j.hom) =
            i.inv ≫ (D.act x ≫ φ) ≫ j.hom := by
          rw [← Category.assoc, hv_act]
          simp only [Category.assoc]
        _ = i.inv ≫ (φ ≫ H.act x) ≫ j.hom := by rw [hφ_act]
        _ = (i.inv ≫ φ ≫ j.hom) ≫ F.act x := by
          rw [Category.assoc, hj_act]
          simp only [Category.assoc]
    · intro x
      calc
        F.act x ≫ (j.inv ≫ ψ ≫ i.hom) =
            j.inv ≫ (H.act x ≫ ψ) ≫ i.hom := by
          rw [← Category.assoc, hw_act]
          simp only [Category.assoc]
        _ = j.inv ≫ (ψ ≫ D.act x) ≫ i.hom := by rw [hψ_act]
        _ = (j.inv ≫ ψ ≫ i.hom) ≫ E.act x := by
          rw [Category.assoc, hi_act]
          simp only [Category.assoc]
    · intro hd
      constructor
      · calc
          (i.inv ≫ φ ≫ j.hom) ≫ (j.inv ≫ ψ ≫ i.hom) =
              i.inv ≫ (φ ≫ ψ) ≫ i.hom := by
            simp only [Category.assoc, Iso.hom_inv_id_assoc]
          _ = i.inv ≫ D.act ⟨((d : ℚ) : ℍ[ℚ, a, b]), hd⟩ ≫ i.hom := by
            rw [(hscalar hd).1]
          _ = (E.act ⟨((d : ℚ) : ℍ[ℚ, a, b]), hd⟩ ≫ i.inv) ≫ i.hom := by
            rw [← Category.assoc, ← hv_act]
          _ = E.act ⟨((d : ℚ) : ℍ[ℚ, a, b]), hd⟩ := by
            rw [Category.assoc, i.inv_hom_id, Category.comp_id]
      · calc
          (j.inv ≫ ψ ≫ i.hom) ≫ (i.inv ≫ φ ≫ j.hom) =
              j.inv ≫ (ψ ≫ φ) ≫ j.hom := by
            simp only [Category.assoc, Iso.hom_inv_id_assoc]
          _ = j.inv ≫ H.act ⟨((d : ℚ) : ℍ[ℚ, a, b]), hd⟩ ≫ j.hom := by
            rw [(hscalar hd).2]
          _ = (F.act ⟨((d : ℚ) : ℍ[ℚ, a, b]), hd⟩ ≫ j.inv) ≫ j.hom := by
            rw [← Category.assoc, ← hw_act]
          _ = F.act ⟨((d : ℚ) : ℍ[ℚ, a, b]), hd⟩ := by
            rw [Category.assoc, j.inv_hom_id, Category.comp_id]
  · refine ⟨hΦ, ?_⟩
    intro X t P hP
    let P' : SchemeHomOver (t ≫ Spec.map (CommRingCat.ofHom k.symm.toRingHom)) D.f :=
      ⟨P.1 ≫ i.inv, by rw [Category.assoc, hv.w, ← Category.assoc, P.2]⟩
    have hP' : FactorsThrough D.lev P' := hv_level t P hP
    obtain ⟨P₀, hP₀⟩ := hj_level _ (mapPt φ hφ P') (hlevel _ P' hP')
    refine ⟨P₀, ?_⟩
    simpa only [mapPt_coe, P', Category.assoc] using hP₀
namespace Submission

/-- Transport a relative group law along a ring equivalence. The equivalences of
relative points preserve their underlying scheme morphisms and all group operations. -/
theorem p07_cre_group_law_857cd4d38c :
    ∀ (T U : Type) [CommRing T] [CommRing U] (k : T ≃+* U)
      (A : AlgebraicGeometry.Scheme.{0})
      (f : Quiver.Hom A (AlgebraicGeometry.Spec (CommRingCat.of U)))
      (G : GoodReductionJacobian.RelativeGroupLaw U f),
    let κ := AlgebraicGeometry.Spec.map (CommRingCat.ofHom k.toRingHom);
    let ε := AlgebraicGeometry.Spec.map (CommRingCat.ofHom k.symm.toRingHom);
    let fT := CategoryTheory.CategoryStruct.comp f κ;
    let κ := AlgebraicGeometry.Spec.map (CommRingCat.ofHom k.toRingHom)
    let ε := AlgebraicGeometry.Spec.map (CommRingCat.ofHom k.symm.toRingHom)
    let fT := CategoryTheory.CategoryStruct.comp f κ
    ∃ (H : GoodReductionJacobian.RelativeGroupLaw T fT)
      (B : ∀ (W : AlgebraicGeometry.Scheme.{0})
        (t : Quiver.Hom W (AlgebraicGeometry.Spec (CommRingCat.of T))),
        NeronModelInfra.SchemeHomOver t fT ≃
          NeronModelInfra.SchemeHomOver (CategoryTheory.CategoryStruct.comp t ε) f),
      (G.IsCommutative → H.IsCommutative) ∧
      (∀ (W : AlgebraicGeometry.Scheme.{0})
        (t : Quiver.Hom W (AlgebraicGeometry.Spec (CommRingCat.of T)))
        (P : NeronModelInfra.SchemeHomOver t fT), (B W t P).1 = P.1) ∧
      (∀ (W : AlgebraicGeometry.Scheme.{0})
        (t : Quiver.Hom W (AlgebraicGeometry.Spec (CommRingCat.of T)))
        (P Q : NeronModelInfra.SchemeHomOver t fT),
        B W t (H.mul t P Q) =
          G.mul (CategoryTheory.CategoryStruct.comp t ε) (B W t P) (B W t Q)) ∧
      (∀ (W : AlgebraicGeometry.Scheme.{0})
        (t : Quiver.Hom W (AlgebraicGeometry.Spec (CommRingCat.of T))),
        B W t (H.one t) = G.one (CategoryTheory.CategoryStruct.comp t ε)) ∧
      (∀ (W : AlgebraicGeometry.Scheme.{0})
        (t : Quiver.Hom W (AlgebraicGeometry.Spec (CommRingCat.of T)))
        (P : NeronModelInfra.SchemeHomOver t fT),
        B W t (H.inv t P) = G.inv (CategoryTheory.CategoryStruct.comp t ε) (B W t P)) := by
  intro T U _ _ k A f G
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
  let κ := Spec.map (CommRingCat.ofHom k.toRingHom)
  let ε := Spec.map (CommRingCat.ofHom k.symm.toRingHom)
  have hκε : κ ≫ ε = 𝟙 _ := by
    dsimp [κ, ε]
    rw [← Spec.map_comp]
    have h : CommRingCat.ofHom k.symm.toRingHom ≫ CommRingCat.ofHom k.toRingHom =
        𝟙 (CommRingCat.of U) := by
      ext x
      exact k.apply_symm_apply x
    exact (congrArg Spec.map h).trans (Spec.map_id _)
  have hεκ : ε ≫ κ = 𝟙 _ := by
    dsimp [κ, ε]
    rw [← Spec.map_comp]
    have h : CommRingCat.ofHom k.toRingHom ≫ CommRingCat.ofHom k.symm.toRingHom =
        𝟙 (CommRingCat.of T) := by
      ext x
      exact k.symm_apply_apply x
    exact (congrArg Spec.map h).trans (Spec.map_id _)
  let B : ∀ (W : Scheme.{0}) (t : W ⟶ Spec (CommRingCat.of T)),
      SchemeHomOver t (f ≫ κ) ≃ SchemeHomOver (t ≫ ε) f := fun W t =>
    { toFun := fun P => ⟨P.1, by
        calc
          P.1 ≫ f = (P.1 ≫ (f ≫ κ)) ≫ ε := by
            rw [Category.assoc, Category.assoc, hκε, Category.comp_id]
          _ = t ≫ ε := by rw [P.2]⟩
      invFun := fun P => ⟨P.1, by
        rw [← Category.assoc, P.2, Category.assoc, hεκ, Category.comp_id]⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => Subtype.ext rfl }
  -- Both routes leave the underlying map equal to ψ ≫ P.1.
  have hBcomp (W W' : Scheme.{0}) (t : W ⟶ Spec (CommRingCat.of T))
      (t' : W' ⟶ Spec (CommRingCat.of T)) (ψ : W' ⟶ W) (hψ : ψ ≫ t = t')
      (P : SchemeHomOver t (f ≫ κ)) :
      B W' t' (GoodReductionJacobian.schemeHomOverComp ψ hψ P) =
        GoodReductionJacobian.schemeHomOverComp ψ
          (by rw [← Category.assoc, hψ]) (B W t P) :=
    Subtype.ext rfl
  let H : RelativeGroupLaw T (f ≫ κ) :=
    { mul := fun {W} t P Q => (B W t).symm (G.mul (t ≫ ε) (B W t P) (B W t Q))
      one := fun {W} t => (B W t).symm (G.one (t ≫ ε))
      inv := fun {W} t P => (B W t).symm (G.inv (t ≫ ε) (B W t P))
      mul_assoc := by
        intro W t P Q R
        apply (B W t).injective
        simp only [Equiv.apply_symm_apply]
        exact G.mul_assoc _ _ _ _
      one_mul := by
        intro W t P
        apply (B W t).injective
        simp only [Equiv.apply_symm_apply]
        exact G.one_mul _ _
      mul_one := by
        intro W t P
        apply (B W t).injective
        simp only [Equiv.apply_symm_apply]
        exact G.mul_one _ _
      inv_mul_cancel := by
        intro W t P
        apply (B W t).injective
        simp only [Equiv.apply_symm_apply]
        exact G.inv_mul_cancel _ _
      mul_natural := by
        intro W W' t t' ψ hψ P Q
        apply (B W' t').injective
        simp only [Equiv.apply_symm_apply, hBcomp]
        exact G.mul_natural _ _ ψ _ _ _ }
  refine ⟨H, B, ?_, ?_, ?_, ?_, ?_⟩
  · intro hG W t P Q
    apply (B W t).injective
    change B W t ((B W t).symm _) = B W t ((B W t).symm _)
    simp only [Equiv.apply_symm_apply]
    exact hG _ _ _
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

/-- Rebase an abelian surface along a ring equivalence. -/
theorem p07_cre_abelian_surface_857cd4d38c
    (T U : Type) [CommRing T] [CommRing U] (k : T ≃+* U)
    (A : Scheme.{0}) (f : A ⟶ Spec (CommRingCat.of U))
    (hf : AbelianSchemePropertyBundle U f)
    (hdim : ∀ s : Spec (CommRingCat.of U),
      topologicalKrullDim ↥(f.base ⁻¹' {s}) = 2) :
    let fT := f ≫ Spec.map (CommRingCat.ofHom k.toRingHom)
    AbelianSchemePropertyBundle T fT ∧
      (∀ s : Spec (CommRingCat.of T), topologicalKrullDim ↥(fT.base ⁻¹' {s}) = 2) := by
  let κ := Spec.map (CommRingCat.ofHom k.toRingHom)
  let ε := Spec.map (CommRingCat.ofHom k.symm.toRingHom)
  let fT := f ≫ κ
  change AbelianSchemePropertyBundle T fT ∧ _
  have hκε : κ ≫ ε = 𝟙 (Spec (CommRingCat.of U)) := by
    change Spec.map k.toCommRingCatIso.hom ≫ Spec.map k.toCommRingCatIso.inv = _
    rw [← Spec.map_comp, k.toCommRingCatIso.inv_hom_id, Spec.map_id]
  have hεκ : ε ≫ κ = 𝟙 (Spec (CommRingCat.of T)) := by
    change Spec.map k.toCommRingCatIso.inv ≫ Spec.map k.toCommRingCatIso.hom = _
    rw [← Spec.map_comp, k.toCommRingCatIso.hom_inv_id, Spec.map_id]
  let : IsIso ε :=
    (show IsIso (Spec.map k.toCommRingCatIso.inv) from inferInstance)
  have hpb : IsPullback (𝟙 A) fT f ε :=
    IsPullback.of_horiz_isIso ⟨by
      simp only [fT, Category.id_comp, Category.assoc, hκε, Category.comp_id]⟩
  have hfibre (s : Spec (CommRingCat.of T)) :
      fT.base ⁻¹' {s} = f.base ⁻¹' {ε.base s} := by
    ext x
    change κ.base (f.base x) = s ↔ f.base x = ε.base s
    constructor
    · intro hx
      calc
        f.base x = ε.base (κ.base (f.base x)) :=
          (congrArg (fun g => g.base (f.base x)) hκε).symm
        _ = ε.base s := congrArg ε.base hx
    · intro hx
      calc
        κ.base (f.base x) = κ.base (ε.base s) := congrArg κ.base hx
        _ = s := congrArg (fun g => g.base s) hεκ
  obtain ⟨G⟩ := hf.hasGroupLaw
  obtain ⟨H, _⟩ := Submission.p07_cre_group_law_857cd4d38c T U k A f G
  refine ⟨⟨MorphismProperty.of_isPullback (P := @Smooth) hpb hf.smooth,
    MorphismProperty.of_isPullback (P := @IsProper) hpb hf.proper, ?_, ⟨H⟩⟩, ?_⟩
  · intro s
    rw [hfibre s]
    exact hf.connectedFibres (ε.base s)
  · intro s
    rw [hfibre s]
    exact hdim (ε.base s)
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
  -- Contravariance gives `e.hom = Spec(k⁻¹)` and `e.inv = Spec(k)`.
  let e := Scheme.Spec.mapIso k.symm.toCommRingCatIso.op
  -- The identity on C identifies qT with the base change of q along e.hom.
  have hpb : IsPullback (𝟙 C) (q ≫ e.inv) q e.hom :=
    IsPullback.of_horiz_isIso
      ⟨by simp only [Category.id_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id]⟩
  let : IsFinite q := hfinite
  let : Flat q := hflat
  exact ⟨MorphismProperty.of_isPullback hpb hfinite,
    MorphismProperty.of_isPullback hpb hflat,
    MorphismProperty.of_isPullback hpb hpresentation,
    fun s => Scheme.Hom.finrank_of_isPullback (𝟙 C) (q ≫ e.inv) q e.hom hpb s⟩

end Submission
