/-
Copyright 2026 Anthropic, PBC. Licensed under Apache-2.0; see LICENSE.
Source: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_AlgebraicCurve_hasPrincipalDivisors_of_transcendental.lean
Modified: replaced the proof with sorry and removed P2M proof imports.
Requires the upstream Definitions modules and their dependencies.
-/

import Definitions.Def_AlgebraicCurve_PlacesOverDVR
attribute [-instance] AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy
attribute [-simp] AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul
attribute [-simp] AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply

open AlgebraicCurve
theorem AlgebraicCurve.hasPrincipalDivisors_of_transcendental (K : Type*) [Field K] [CharZero K] {F : Type*} [Field F]
    [Algebra K F] (x : F) (hx : Transcendental K x)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F] : HasPrincipalDivisors K F := by
  sorry

namespace Submission

/-- An algebra equivalence transports places and preserves their residue degrees.
The valuation rings are pulled back along the inverse equivalence; their induced residue
algebra equivalences preserve `finrank` without a finite-dimensionality assumption. -/
theorem p06_9e0f5043ff_pae_place_equivalence_degree :
    ∀ (K E L : Type*) [Field K] [Field E] [Field L] [Algebra K E] [Algebra K L]
      (e : E ≃ₐ[K] L),
      ∃ θ : AlgebraicCurve.Place K E ≃ AlgebraicCurve.Place K L,
        (∀ v : AlgebraicCurve.Place K E, (θ v).deg = v.deg) ∧
        (∀ v : AlgebraicCurve.Place K E,
          ∃ r : v.toValuationSubring ≃ₐ[K] (θ v).toValuationSubring,
            ∀ a : v.toValuationSubring, (r a : L) = e (a : E)) := by
  intro K E L _ _ _ _ _ e
  classical
  -- Prove both directions together so the fields retain independent universes.
  have transport :
      (∀ (f : E ≃ₐ[K] L) (v : AlgebraicCurve.Place K E),
        ∃ w : AlgebraicCurve.Place K L,
          w.toValuationSubring = v.toValuationSubring.comap f.symm.toRingHom ∧
          ∃ r : v.toValuationSubring ≃ₐ[K] w.toValuationSubring,
            ∀ a : v.toValuationSubring, (r a : L) = f (a : E)) ∧
      (∀ (f : L ≃ₐ[K] E) (v : AlgebraicCurve.Place K L),
        ∃ w : AlgebraicCurve.Place K E,
          w.toValuationSubring = v.toValuationSubring.comap f.symm.toRingHom ∧
          ∃ r : v.toValuationSubring ≃ₐ[K] w.toValuationSubring,
            ∀ a : v.toValuationSubring, (r a : E) = f (a : L)) := by
    constructor <;> intro f v
    all_goals
      let A := v.toValuationSubring.comap f.symm.toRingHom
      let r₀ : v.toValuationSubring ≃+* A :=
        { toFun := fun a => ⟨f a, by simp [A, a.property]⟩
          invFun := fun b => ⟨f.symm b, b.property⟩
          left_inv := fun a => Subtype.ext (f.symm_apply_apply a)
          right_inv := fun b => Subtype.ext (f.apply_symm_apply b)
          map_mul' := fun a b => Subtype.ext (f.map_mul a b)
          map_add' := fun a b => Subtype.ext (f.map_add a b) }
      let w : AlgebraicCurve.Place K _ :=
        { toValuationSubring := A
          algebraMap_mem' := fun k => by
            change f.symm (algebraMap K _ k) ∈ v.toValuationSubring
            rw [f.symm.commutes]
            exact v.algebraMap_mem' k
          ne_top' := by
            intro h
            apply v.ne_top'
            apply eq_top_iff.mpr
            intro x _
            have hx : f x ∈ A := by
              rw [h]
              exact ValuationSubring.mem_top _
            change f.symm (f x) ∈ v.toValuationSubring at hx
            simpa using hx
          -- The pinned library transports generators through this surjective ring map.
          isPrincipalIdealRing' := IsPrincipalIdealRing.of_surjective r₀ r₀.surjective }
      let := AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring w
      let r : v.toValuationSubring ≃ₐ[K] w.toValuationSubring :=
        { r₀ with commutes' := fun k => Subtype.ext (f.commutes k) }
      exact ⟨w, rfl, r, fun _ => rfl⟩
  choose T hT using transport.1 e
  choose S hS using transport.2 e.symm
  let θ : AlgebraicCurve.Place K E ≃ AlgebraicCurve.Place K L :=
    { toFun := T
      invFun := S
      left_inv := fun v => by
        apply AlgebraicCurve.Place.ext
        rw [(hS (T v)).1, (hT v).1]
        apply SetLike.ext
        intro x
        change e.symm (e x) ∈ v.toValuationSubring ↔ x ∈ v.toValuationSubring
        rw [e.symm_apply_apply]
      right_inv := fun v => by
        apply AlgebraicCurve.Place.ext
        rw [(hT (S v)).1, (hS v).1]
        apply SetLike.ext
        intro x
        change e (e.symm x) ∈ v.toValuationSubring ↔ x ∈ v.toValuationSubring
        rw [e.apply_symm_apply] }
  refine ⟨θ, ?_, fun v => (hT v).2⟩
  intro v
  obtain ⟨r, _⟩ := (hT v).2
  -- The residue equivalence descends through the maximal ideals; finrank needs no finiteness.
  exact (IsLocalRing.ResidueField.mapAlgEquiv r).toLinearEquiv.finrank_eq.symm

end Submission
