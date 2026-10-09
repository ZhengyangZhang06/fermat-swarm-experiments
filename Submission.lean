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

/-- Full level structures pull back along any pullback of fake elliptic curves. -/
theorem p07_flq_full_level_pullback_857cd4d38c
    {a b : ℚ} (Λ : Submodule ℤ (QuaternionAlgebra ℚ a 0 b)) (N n : ℕ)
    (S T : Type) [CommRing S] [CommRing T] (φ : S →+* T)
    (E : FakeEllipticCurve Λ N S) (ET : FakeEllipticCurve Λ N T)
    (g : ET.A ⟶ E.A) (hg : FakeEllipticCurve.IsPullbackVia φ E ET g)
    (L : E.FullLevel n) :
    ∃ LT : ET.FullLevel n,
      LT.P.1 ≫ g = Spec.map (CommRingCat.ofHom φ) ≫ L.P.1 := by
  classical
  let β := Spec.map (CommRingCat.ofHom φ)
  -- Identify the target base map before using the point equivalence.
  have equiv_over (W : Scheme.{0}) (t : W ⟶ Spec (CommRingCat.of T))
      (s : W ⟶ Spec (CommRingCat.of S)) (hs : t ≫ β = s) :
      ∃ B : SchemeHomOver t ET.f ≃ SchemeHomOver s E.f,
        (∀ P : SchemeHomOver t ET.f, (B P).1 = P.1 ≫ g) ∧
        B (ET.L.one t) = E.L.one s ∧
        (∀ (k : ℕ) (P : SchemeHomOver t ET.f),
          B (nsmulPt ET.L t k P) = nsmulPt E.L s k (B P)) ∧
        (∀ (x : ↥Λ) (P : SchemeHomOver t ET.f),
          B (pushPt (ET.act x) (ET.act_over x) P) =
            pushPt (E.act x) (E.act_over x) (B P)) := by
    subst s
    obtain ⟨B, hB, _, hOne, hSum, hAct⟩ :=
      p07_flp_point_equiv_857cd4d38c Λ N S T φ E ET g hg W t
    exact ⟨B, hB, hOne, hSum, hAct⟩
  obtain ⟨B, hB, hOne, hSum, _⟩ :=
    equiv_over (Spec (CommRingCat.of T)) (𝟙 _) β (Category.id_comp β)
  let Pβ : SchemeHomOver β E.f := schemeHomOverComp β (Category.comp_id β) L.P
  let PT : SchemeHomOver (𝟙 (Spec (CommRingCat.of T))) ET.f := B.symm Pβ
  have hPT : B PT = Pβ := B.apply_symm_apply Pβ
  have hproj : PT.1 ≫ g = β ≫ L.P.1 := by
    rw [← hB, hPT]
    rfl
  have htorsion : nsmulPt ET.L (𝟙 _) n PT = ET.L.one (𝟙 _) := by
    apply B.injective
    rw [hSum, hOne, hPT]
    change nsmulPt E.L β n (schemeHomOverComp β (Category.comp_id β) L.P) = _
    rw [← p07_flp_nsmul_precomp_857cd4d38c S E.A
      (Spec (CommRingCat.of S)) (Spec (CommRingCat.of T)) E.f E.L
      (𝟙 _) β β (Category.comp_id β) n L.P, L.torsion]
    exact E.L.one_natural (𝟙 _) β β (Category.comp_id β)
  have hgeom (K : Type) [Field K] [IsAlgClosed K] (α : T →+* K) :
      (∀ Q : SchemeHomOver (geomPoint K α) ET.f,
        nsmulPt ET.L (geomPoint K α) n Q = ET.L.one (geomPoint K α) →
        ∃ x : ↥Λ,
          pushPt (ET.act x) (ET.act_over x) (FakeEllipticCurve.sectionAt PT K α) = Q) ∧
      (∀ x : ↥Λ,
        pushPt (ET.act x) (ET.act_over x) (FakeEllipticCurve.sectionAt PT K α) =
            ET.L.one (geomPoint K α) ↔
          ∃ y : ↥Λ, (x : QuaternionAlgebra ℚ a 0 b) =
            (n : ℚ) • (y : QuaternionAlgebra ℚ a 0 b)) := by
    have hbase : geomPoint K α ≫ β = geomPoint K (α.comp φ) := by
      simp only [geomPoint, β, CommRingCat.ofHom_comp, Spec.map_comp]
    obtain ⟨BK, hBK, hOneK, hSumK, hActK⟩ :=
      equiv_over (Spec (CommRingCat.of K)) (geomPoint K α)
        (geomPoint K (α.comp φ)) hbase
    have hsection : BK (FakeEllipticCurve.sectionAt PT K α) =
        FakeEllipticCurve.sectionAt L.P K (α.comp φ) := by
      apply Subtype.ext
      rw [hBK]
      change (geomPoint K α ≫ PT.1) ≫ g = geomPoint K (α.comp φ) ≫ L.P.1
      rw [Category.assoc, hproj, ← Category.assoc, hbase]
    constructor
    · intro Q hQ
      have hQ' : nsmulPt E.L (geomPoint K (α.comp φ)) n (BK Q) =
          E.L.one (geomPoint K (α.comp φ)) := by
        rw [← hSumK, hQ, hOneK]
      obtain ⟨x, hx⟩ := L.generates K (α.comp φ) (BK Q) hQ'
      refine ⟨x, BK.injective ?_⟩
      rw [hActK, hsection]
      exact hx
    · intro x
      rw [← L.annihilator K (α.comp φ) x]
      constructor
      · intro hx
        have h := congrArg BK hx
        rw [hActK, hsection, hOneK] at h
        exact h
      · intro hx
        apply BK.injective
        rw [hActK, hsection, hOneK]
        exact hx
  exact ⟨{ P := PT
           torsion := htorsion
           generates := fun K _ _ α => (hgeom K α).1
           annihilator := fun K _ _ α => (hgeom K α).2 }, hproj⟩

end Submission
