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

/-- A residue module localized at a height-one prime is simple at its own prime
and is the zero module at every distinct height-one prime.

At its own prime, the localization equivalence over `B` transfers simplicity of
the residue field. Every nonzero element then also generates the module over the
localized ring, since the original scalars act through its canonical algebra map. -/
theorem p06_9e0f5043ff_llm_localized_residue_factors
    (B : Type*) [CommRing B] [IsDedekindDomain B]
    (p q : IsDedekindDomain.HeightOneSpectrum B) :
    (p = q → IsSimpleModule (Localization.AtPrime q.asIdeal)
      (LocalizedModule q.asIdeal.primeCompl (B ⧸ p.asIdeal))) ∧
    (p ≠ q → Subsingleton (LocalizedModule q.asIdeal.primeCompl (B ⧸ p.asIdeal))) := by
  constructor
  · rintro rfl
    -- At the same prime, every denominator acts invertibly on the residue field.
    let k := B ⧸ p.asIdeal
    let : Field k := Ideal.Quotient.field p.asIdeal
    let T := p.asIdeal.primeCompl
    have : IsLocalizedModule T (LinearMap.id : k →ₗ[B] k) := by
      refine ⟨?_, fun m ↦ ⟨(m, 1), by simp⟩, fun h ↦ ⟨1, by simpa using h⟩⟩
      intro s
      rw [Module.End.isUnit_iff]
      change Function.Bijective (fun m : k ↦ (s : B) • m)
      have hs : (Ideal.Quotient.mk p.asIdeal (s : B) : k) ≠ 0 :=
        fun h ↦ s.property ((Ideal.Quotient.eq_zero_iff_mem).mp h)
      simpa only [Algebra.smul_def, k, Ideal.Quotient.algebraMap_eq] using
        mulLeft_bijective₀ (Ideal.Quotient.mk p.asIdeal (s : B)) hs
    have : IsSimpleModule B k :=
      isSimpleModule_iff_isCoatom.mpr (Ideal.isMaximal_def.mp p.isMaximal)
    -- The localization equivalence preserves simplicity over B; enlarging scalars
    -- preserves the fact that each nonzero element generates the whole module.
    have : IsSimpleModule B (LocalizedModule T k) :=
      IsSimpleModule.congr
        (IsLocalizedModule.linearEquiv T (LocalizedModule.mkLinearMap T k) LinearMap.id)
    refine isSimpleModule_iff_toSpanSingleton_surjective.mpr
      ⟨IsSimpleModule.nontrivial B _, ?_⟩
    intro x hx y
    obtain ⟨b, hb⟩ := IsSimpleModule.toSpanSingleton_surjective B hx y
    exact ⟨algebraMap B (Localization.AtPrime p.asIdeal) b, by
      simpa only [LinearMap.toSpanSingleton_apply, algebraMap_smul] using hb⟩
  · intro hpq
    -- A distinct maximal ideal contains an annihilator outside the localization prime.
    have hnot : ¬p.asIdeal ≤ q.asIdeal := by
      intro h
      exact hpq (IsDedekindDomain.HeightOneSpectrum.asIdeal_injective
        (p.isMaximal.eq_of_le q.isPrime.ne_top h))
    obtain ⟨t, htp, htq⟩ := SetLike.not_le_iff_exists.mp hnot
    apply LocalizedModule.subsingleton_iff.mpr
    intro m
    refine ⟨t, htq, ?_⟩
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem.mpr htp, zero_mul]

end Submission
