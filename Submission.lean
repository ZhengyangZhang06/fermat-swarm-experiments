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

end Submission
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
namespace Submission

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
          (by rw [← Category.assoc, hh]) (B W t P) := by
    exact Subtype.ext (Category.assoc h P.1 g)
  -- Transport the operations; injectivity reduces their laws to those of G.
    apply Subtype.ext
    exact Category.assoc h P.1 g
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

end Submission

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

/-- The level immersion and its finite flat structure morphism commute with base change. -/
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
  have hpb : IsPullback (pullback.fst c β) ℓT ℓ (pullback.fst f β) := by
    apply IsPullback.of_bot (s := ?_) hfst.symm (IsPullback.of_hasPullback f β)
    rw [hsnd]
    exact IsPullback.of_hasPullback c β
  refine ⟨ℓT, hpb, hsnd, ?_, inferInstance, inferInstance, inferInstance, ?_, ?_⟩
  · exact MorphismProperty.of_isPullback hpb hℓ
  · exact Scheme.Hom.finrank_pullback_snd c β
  · intro W Q
    constructor
    · rintro ⟨U, hU⟩
      refine ⟨U ≫ pullback.fst c β, ?_⟩
      rw [Category.assoc, hpb.w, ← Category.assoc, hU]
    · rintro ⟨R, hR⟩
      exact ⟨hpb.lift R Q hR, hpb.lift_snd R Q hR⟩

end Submission
