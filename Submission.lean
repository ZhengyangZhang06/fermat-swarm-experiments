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
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Quotient.Basic

open AlgebraicCurve
theorem AlgebraicCurve.hasPrincipalDivisors_of_transcendental (K : Type*) [Field K] [CharZero K] {F : Type*} [Field F]
    [Algebra K F] (x : F) (hx : Transcendental K x)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F] : HasPrincipalDivisors K F := by
  sorry

namespace Submission

/-- Left and right multiplication by unit matrices preserve the cokernel up to linear equivalence. -/
theorem p06_9e0f5043ff_dmc_cokernel_units :
    ∀ (R : Type*) [CommRing R] (m : ℕ) (D P Q : Matrix (Fin m) (Fin m) R),
      IsUnit P → IsUnit Q →
        Nonempty (((Fin m → R) ⧸ LinearMap.range (Matrix.mulVecLin D)) ≃ₗ[R]
          ((Fin m → R) ⧸ LinearMap.range (Matrix.mulVecLin (P * D * Q)))) := by
  intro R _ m D P Q hP hQ
  let eP := Matrix.toLinearEquiv' P hP.invertible
  let eQ := Matrix.toLinearEquiv' Q hQ.invertible
  -- Descend P and its inverse once P maps range(D) onto range(P * D * Q).
  refine ⟨Submodule.Quotient.equiv _ _ eP ?_⟩
  -- P(range D) = range (P * D), and surjectivity of Q gives range (P * D * Q).
  change (LinearMap.range D.mulVecLin).map P.mulVecLin =
    LinearMap.range (P * D * Q).mulVecLin
  rw [← LinearMap.range_comp, ← Matrix.mulVecLin_mul, Matrix.mulVecLin_mul (P * D) Q]
  exact (eQ.range_comp _).symm
/-- The cokernel of a diagonal matrix is the product of its coordinate principal quotients. -/
theorem p06_9e0f5043ff_dmc_diagonal_quotient
    (R : Type*) [CommRing R] (m : ℕ) (d : Fin m → R) :
    Nonempty (((Fin m → R) ⧸ LinearMap.range (Matrix.mulVecLin (Matrix.diagonal d)))
      ≃ₗ[R] ((i : Fin m) → R ⧸ Ideal.span ({d i} : Set R))) := by
  classical
  -- Reduce each coordinate modulo the corresponding principal ideal.
  let C : (Fin m → R) →ₗ[R] ((i : Fin m) → R ⧸ Ideal.span ({d i} : Set R)) :=
    LinearMap.pi fun i => (Ideal.span ({d i} : Set R)).mkQ.comp (LinearMap.proj i)
  have hker : LinearMap.ker C = LinearMap.range (Matrix.mulVecLin (Matrix.diagonal d)) := by
    ext y
    simp only [LinearMap.mem_ker, LinearMap.mem_range]
    constructor
    · intro hy
      have hyi : ∀ i, d i ∣ y i := by
        intro i
        apply Ideal.mem_span_singleton.mp
        apply (Submodule.Quotient.mk_eq_zero _).mp
        exact congrFun hy i
      choose z hz using hyi
      exact ⟨z, funext fun i => (Matrix.mulVec_diagonal d z i).trans (hz i).symm⟩
    · rintro ⟨z, rfl⟩
      funext i
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      exact Ideal.mem_span_singleton.mpr ⟨z i, Matrix.mulVec_diagonal d z i⟩
  have hsurj : Function.Surjective C := by
    intro w
    choose y hy using fun i => (Ideal.span ({d i} : Set R)).mkQ_surjective (w i)
    exact ⟨y, funext hy⟩
  -- The first isomorphism theorem supplies the induced bijection and its linear inverse.
  exact ⟨(Submodule.quotEquivOfEq _ _ hker.symm).trans (C.quotKerEquivOfSurjective hsurj)⟩

end Submission


namespace Submission

theorem p06_9e0f5043ff_dlen_diagonal_cokernel
    (R : Type*) [CommRing R] (m : ℕ) (D P Q : Matrix (Fin m) (Fin m) R)
    (d : Fin m → R) (hP : IsUnit P) (hQ : IsUnit Q)
    (hdiag : P * D * Q = Matrix.diagonal d) :
    Nonempty (((Fin m → R) ⧸ LinearMap.range (Matrix.mulVecLin D)) ≃ₗ[R]
      ((i : Fin m) → R ⧸ Ideal.span ({d i} : Set R))) := by
  obtain ⟨eUnits⟩ := Submission.p06_9e0f5043ff_dmc_cokernel_units R m D P Q hP hQ
  rw [hdiag] at eUnits
  obtain ⟨eDiagonal⟩ := Submission.p06_9e0f5043ff_dmc_diagonal_quotient R m d
  exact ⟨eUnits.trans eDiagonal⟩

end Submission
