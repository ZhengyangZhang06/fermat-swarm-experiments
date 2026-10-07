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

open IsDedekindDomain IsLocalRing AlgebraicCurve.Place

theorem p06_9e0f5043ff_ifl_residue_length_inertia
    (K E L : Type*) [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra K L] [Algebra E L] [IsScalarTower K E L]
    [FiniteDimensional E L] [Algebra.IsSeparable E L]
    (v : AlgebraicCurve.Place K E) (w : AlgebraicCurve.Place K L)
    (hw : w.restrict E = v) :
    Module.length v.toValuationSubring
      (integralClosureAt L v ⧸ (fiberCenter L v hw).asIdeal) =
        (w.inertiaDeg E : ℕ∞) := by
  classical
  subst v
  let A := (w.restrict E).toValuationSubring
  let B := integralClosureAt L (w.restrict E)
  let q := (fiberCenter L (w.restrict E) rfl).asIdeal
  -- The fiber center is the inverse image of the maximal ideal of O_w.
  let f : B →+* w.toValuationSubring :=
    (algebraMap B L).codRestrict w.toValuationSubring.toSubring
      (forall_mem_of_restrict_eq rfl)
  let g : B ⧸ q →+* w.ResidueField :=
    Ideal.Quotient.lift q ((residue _).comp f) (by
      intro b hb
      exact (Ideal.Quotient.eq_zero_iff_mem).mpr hb)
  have : q.IsMaximal := (fiberCenter L (w.restrict E) rfl).isMaximal
  let : Field (B ⧸ q) := Ideal.Quotient.field q
  have hg : Function.Surjective g := by
    -- Every element of O_w is a fraction with denominator outside the fiber center.
    intro y
    obtain ⟨x, rfl⟩ := residue_surjective (R := w.toValuationSubring) y
    have hx := x.property
    simp only [toValuationSubring_eq_of_restrict_eq (w := w) (v := w.restrict E) rfl] at hx
    obtain ⟨a, s, hs, hxs⟩ := hx
    have hs' : g (Ideal.Quotient.mk q s) ≠ 0 := by
      intro h
      have hmem : f s ∈ maximalIdeal w.toValuationSubring :=
        (Ideal.Quotient.eq_zero_iff_mem).mp h
      exact hs hmem
    refine ⟨Ideal.Quotient.mk q a / Ideal.Quotient.mk q s, ?_⟩
    rw [map_div₀, div_eq_iff hs']
    change residue _ (f a) = residue _ x * residue _ (f s)
    rw [← map_mul]
    apply congrArg (residue _)
    apply Subtype.ext
    change algebraMap B L a = (x : L) * algebraMap B L s
    rw [hxs]
    have hs0 : algebraMap B L s ≠ 0 := by
      intro h
      apply hs'
      change residue _ (f s) = 0
      have : f s = 0 := Subtype.ext h
      rw [this, map_zero]
    simpa only [div_eq_mul_inv] using (div_mul_cancel₀ (algebraMap B L a) hs0).symm
  let e := RingEquiv.ofBijective g ⟨g.injective, hg⟩
  -- Use exactly the residue-field scalar action defining the inertia degree.
  let : Algebra A w.ResidueField :=
    ((restrictResidueMap E w).comp (residue A)).toAlgebra
  have : IsScalarTower A (w.restrict E).ResidueField w.ResidueField :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let eA : (B ⧸ q) ≃ₐ[A] w.ResidueField :=
    { e with
      commutes' := by
        intro a
        change residue _ (f (algebraMap A B a)) =
          restrictResidueMap E w (residue A a)
        rw [restrictResidueMap_residue]
        apply congrArg (residue _)
        exact Subtype.ext rfl }
  have : Module.Finite A w.ResidueField :=
    Module.Finite.of_surjective eA.toLinearMap eA.surjective
  have : FiniteDimensional (w.restrict E).ResidueField w.ResidueField :=
    Module.Finite.of_restrictScalars_finite A (w.restrict E).ResidueField w.ResidueField
  -- Surjectivity of the residue map identifies the two submodule lattices.
  calc
    Module.length A (B ⧸ q) = Module.length A w.ResidueField := eA.toLinearEquiv.length_eq
    _ = Module.length (w.restrict E).ResidueField w.ResidueField :=
      Module.length_eq_of_surjective (residue_surjective (R := A))
    _ = (w.inertiaDeg E : ℕ∞) := Module.length_eq_finrank _ _

end Submission
