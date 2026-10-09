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

/-- Finite order supports give a finite exceptional set for all coefficients of a polynomial.
Take the union of the order supports of its nonzero coefficients. Outside that union,
unit–uniformizer factorization makes each nonzero coefficient a valuation-subring unit. -/
theorem p06_9e0f5043ff_fosa_coefficients_integral_off_finite
    (K E : Type*) [Field K] [Field E] [Algebra K E]
    (hfinite : ∀ a : E, a ≠ 0 → {v : AlgebraicCurve.Place K E | v.ord a ≠ 0}.Finite)
    (P : Polynomial E) :
    ∃ T : Set (AlgebraicCurve.Place K E), T.Finite ∧
      ∀ v : AlgebraicCurve.Place K E, v ∉ T → ∀ i : ℕ,
        P.coeff i ∈ v.toValuationSubring := by
  classical
  refine ⟨⋃ i ∈ P.support, {v | v.ord (P.coeff i) ≠ 0}, ?_, ?_⟩
  · exact P.support.finite_toSet.biUnion fun i hi =>
      hfinite (P.coeff i) (Polynomial.mem_support_iff.mp hi)
  · intro v hv i
    by_cases hi : P.coeff i = 0
    · rw [hi]
      exact v.toValuationSubring.zero_mem
    · have hord : v.ord (P.coeff i) = 0 := by
        by_contra h
        exact hv (Set.mem_biUnion (Polynomial.mem_support_iff.mpr hi) h)
      obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
      obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hi hπ
      rw [hu, hord, zpow_zero, mul_one]
      exact (u : v.toValuationSubring).property

end Submission

namespace Submission

/-- Monic equations for a nonzero element and its inverse over the restricted valuation ring
make the element a unit upstairs, so its order is zero.

Map each polynomial to `L`, use `Place.mem_restrict_iff` to transfer its coefficient
memberships, and apply `Place.mem_of_eval_monic_eq_zero`. The resulting unit has order
zero by `Place.ord_coe_unit`. -/
theorem p06_9e0f5043ff_fosa_ord_zero_of_monic_pair
    (K E L : Type*) [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra K L] [Algebra E L] [IsScalarTower K E L]
    [Algebra.IsIntegral E L] (w : AlgebraicCurve.Place K L) (f : L)
    (P Q : Polynomial E) (hf : f ≠ 0) (hP : P.Monic) (hQ : Q.Monic)
    (hPf : Polynomial.eval₂ (algebraMap E L) f P = 0)
    (hQf : Polynomial.eval₂ (algebraMap E L) (f⁻¹) Q = 0)
    (hPcoeff : ∀ i : ℕ, P.coeff i ∈ (w.restrict E).toValuationSubring)
    (hQcoeff : ∀ i : ℕ, Q.coeff i ∈ (w.restrict E).toValuationSubring) :
    w.ord f = 0 := by
  have mem_of_root (R : Polynomial E) (x : L) (hR : R.Monic)
      (hcoeff : ∀ i : ℕ, R.coeff i ∈ (w.restrict E).toValuationSubring)
      (hx : Polynomial.eval₂ (algebraMap E L) x R = 0) :
      x ∈ w.toValuationSubring := by
    apply w.mem_of_eval_monic_eq_zero (P := R.map (algebraMap E L)) (hR.map _)
    · intro i
      simpa only [Polynomial.coeff_map] using w.mem_restrict_iff.mp (hcoeff i)
    · simpa only [Polynomial.eval_map] using hx
  exact w.ord_coe_unit
    { val := ⟨f, mem_of_root P f hP hPcoeff hPf⟩
      inv := ⟨f⁻¹, mem_of_root Q f⁻¹ hQ hQcoeff hQf⟩
      val_inv := Subtype.ext (mul_inv_cancel₀ hf)
      inv_val := Subtype.ext (inv_mul_cancel₀ hf) }

end Submission

namespace Submission

/-- Finite order support ascends along a finite separable field extension.
Choose monic equations for the element and its inverse. The approved coefficient lemma
gives two finite exceptional sets downstairs; the approved monic-pair lemma makes the
order zero outside their inverse image. Restriction has finite fibers by the pinned
`AlgebraicCurve.Place.finite_setOf_restrict_eq`, so that inverse image is finite. -/
theorem p06_9e0f5043ff_finite_order_support_ascent
    (K E L : Type*) [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra K L] [Algebra E L] [IsScalarTower K E L]
    [FiniteDimensional E L] [Algebra.IsSeparable E L]
    (hE : ∀ a : E, a ≠ 0 → {v : AlgebraicCurve.Place K E | v.ord a ≠ 0}.Finite)
    (f : L) (hf : f ≠ 0) :
    {w : AlgebraicCurve.Place K L | w.ord f ≠ 0}.Finite := by
  classical
  obtain ⟨P, hP, hPf⟩ := IsIntegral.of_finite E f
  obtain ⟨Q, hQ, hQf⟩ := IsIntegral.of_finite E (f⁻¹)
  obtain ⟨TP, hTP, hPcoeff⟩ :=
    p06_9e0f5043ff_fosa_coefficients_integral_off_finite K E hE P
  obtain ⟨TQ, hTQ, hQcoeff⟩ :=
    p06_9e0f5043ff_fosa_coefficients_integral_off_finite K E hE Q
  have hfinite :
      ((fun w : AlgebraicCurve.Place K L => w.restrict E) ⁻¹' (TP ∪ TQ)).Finite :=
    (hTP.union hTQ).preimage' fun v _ =>
      AlgebraicCurve.Place.finite_setOf_restrict_eq (F' := L) v
  refine hfinite.subset ?_
  intro w hw
  change w.restrict E ∈ TP ∪ TQ
  by_contra hout
  apply hw
  exact p06_9e0f5043ff_fosa_ord_zero_of_monic_pair K E L w f P Q
    hf hP hQ hPf hQf
    (hPcoeff (w.restrict E) (fun hv => hout (Or.inl hv)))
    (hQcoeff (w.restrict E) (fun hv => hout (Or.inr hv)))

end Submission
