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

set_option warningAsError true

/-- In the given polynomial-fraction model of a place, a fraction is a unit exactly when
its numerator is not divisible by the defining irreducible polynomial. -/
theorem p06_9e0f5043ff_fno_fraction_isunit
    (K F : Type*) [Field K] [Field F] [Algebra K F] (x : F)
    (hx : Transcendental K x) (q : Polynomial K) (_hqmonic : q.Monic)
    (hq : Irreducible q) (v : AlgebraicCurve.Place K F)
    (hmem : ∀ f : F, f ∈ v.toValuationSubring ↔
      ∃ a b : Polynomial K, ¬ q ∣ b ∧
        f = Polynomial.aeval x a / Polynomial.aeval x b)
    (a b : Polynomial K) (z : v.toValuationSubring) (hb : ¬ q ∣ b)
    (hz : (z : F) = Polynomial.aeval x a / Polynomial.aeval x b) :
    IsUnit z ↔ ¬ q ∣ a := by
  -- Transcendence lets us recover polynomial identities from identities in F.
  have hinj : Function.Injective (Polynomial.aeval x : Polynomial K →ₐ[K] F) :=
    transcendental_iff_injective.mp hx
  have hnonzero : ∀ p : Polynomial K, ¬ q ∣ p → Polynomial.aeval x p ≠ 0 := by
    intro p hp he
    have hpzero : p = 0 := hinj (by simpa only [map_zero] using he)
    exact hp (hpzero ▸ dvd_zero q)
  have hbzero := hnonzero b hb
  constructor
  · intro hu hqa
    -- Represent a unit's inverse, clear denominators, and use primality of q.
    obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.mp hu
    obtain ⟨c, d, hd, hwd⟩ := (hmem (w : F)).mp w.property
    have hprod : Polynomial.aeval x a * Polynomial.aeval x c =
        Polynomial.aeval x b * Polynomial.aeval x d := by
      have heq : (z : F) * (w : F) = 1 :=
        congrArg (fun t : v.toValuationSubring => (t : F)) hw
      rw [hz, hwd, div_mul_div_comm] at heq
      exact (div_eq_one_iff_eq (mul_ne_zero hbzero (hnonzero d hd))).mp heq
    have hpoly : a * c = b * d := hinj (by simpa only [map_mul] using hprod)
    have hdiv : q ∣ b * d := hpoly ▸ dvd_mul_of_dvd_left hqa c
    exact (hq.prime.dvd_or_dvd hdiv).elim hb hd
  · intro ha
    -- The reversed fraction belongs to the valuation subring and is an inverse.
    have hwmem : Polynomial.aeval x b / Polynomial.aeval x a ∈ v.toValuationSubring :=
      (hmem _).mpr ⟨b, a, ha, rfl⟩
    apply isUnit_iff_exists_inv.mpr
    refine ⟨⟨_, hwmem⟩, ?_⟩
    apply Subtype.ext
    change (z : F) * (Polynomial.aeval x b / Polynomial.aeval x a) = 1
    rw [hz, div_mul_div_comm, mul_comm (Polynomial.aeval x b) (Polynomial.aeval x a)]
    exact div_self (mul_ne_zero (hnonzero a ha) hbzero)

end Submission


namespace Submission

set_option warningAsError true

theorem p06_9e0f5043ff_fno_irreducible_aeval
    (K F : Type*) [Field K] [Field F] [Algebra K F] (x : F)
    (hx : Transcendental K x) (q : Polynomial K) (hq : q.Monic)
    (hqi : Irreducible q) (v : AlgebraicCurve.Place K F)
    (hv : ∀ f : F, f ∈ v.toValuationSubring ↔
      ∃ a b : Polynomial K, ¬ q ∣ b ∧
        f = Polynomial.aeval x a / Polynomial.aeval x b) :
    ∃ π : v.toValuationSubring, (π : F) = Polynomial.aeval x q ∧ Irreducible π := by
  classical
  have hinj : Function.Injective (Polynomial.aeval x : Polynomial K →ₐ[K] F) :=
    transcendental_iff_injective.mp hx
  have hq1 : ¬ q ∣ (1 : Polynomial K) := hqi.not_dvd_one
  let π : v.toValuationSubring :=
    ⟨Polynomial.aeval x q, (hv _).mpr ⟨q, 1, hq1, by simp⟩⟩
  refine ⟨π, rfl, ?_⟩
  constructor
  · intro hunit
    have hnot :=
      (Submission.p06_9e0f5043ff_fno_fraction_isunit K F x hx q hq hqi v hv
        q 1 π hq1 (by simp [π])).mp hunit
    exact hnot (dvd_refl q)
  · intro y z hyz
    obtain ⟨a, b, hb, hy⟩ := (hv (y : F)).mp y.property
    obtain ⟨c, t, ht, hz⟩ := (hv (z : F)).mp z.property
    have hb0 : Polynomial.aeval x b ≠ 0 := by
      intro h
      have : b = 0 := hinj (by simpa only [map_zero] using h)
      exact hb (this.symm ▸ dvd_zero q)
    have ht0 : Polynomial.aeval x t ≠ 0 := by
      intro h
      have : t = 0 := hinj (by simpa only [map_zero] using h)
      exact ht (this.symm ▸ dvd_zero q)
    have hprod : Polynomial.aeval x q =
        (Polynomial.aeval x a / Polynomial.aeval x b) *
          (Polynomial.aeval x c / Polynomial.aeval x t) := by
      calc
        Polynomial.aeval x q = (π : F) := rfl
        _ = (y : F) * (z : F) :=
          congrArg (fun w : v.toValuationSubring => (w : F)) hyz
        _ = _ := by rw [hy, hz]
    have hac : a * c = q * (b * t) := by
      apply hinj
      rw [div_mul_div_comm, eq_div_iff (mul_ne_zero hb0 ht0)] at hprod
      simpa only [map_mul] using hprod.symm
    by_cases ha : q ∣ a
    · right
      apply (Submission.p06_9e0f5043ff_fno_fraction_isunit K F x hx q hq hqi v hv
        c t z ht hz).mpr
      intro hc
      obtain ⟨a₁, ha₁⟩ := ha
      obtain ⟨c₁, hc₁⟩ := hc
      have hcancel : q * (q * (a₁ * c₁)) = q * (b * t) := by
        calc
          q * (q * (a₁ * c₁)) = (q * a₁) * (q * c₁) := by ring
          _ = a * c := by rw [← ha₁, ← hc₁]
          _ = q * (b * t) := hac
      have hbt : q ∣ b * t :=
        ⟨a₁ * c₁, (mul_left_cancel₀ hqi.ne_zero hcancel).symm⟩
      exact (hqi.prime.dvd_or_dvd hbt).elim hb ht
    · left
      exact (Submission.p06_9e0f5043ff_fno_fraction_isunit K F x hx q hq hqi v hv
        a b y hb hy).mpr ha

end Submission

namespace Submission

set_option warningAsError true

theorem p06_9e0f5043ff_fpm_normalized_orders
    (K F : Type*) [Field K] [Field F] [Algebra K F] (x : F)
    (hx : Transcendental K x) (q : Polynomial K) (hq : q.Monic)
    (hqirr : Irreducible q) (v : AlgebraicCurve.Place K F)
    (hv : ∀ f : F, f ∈ v.toValuationSubring ↔
      ∃ a b : Polynomial K, ¬ q ∣ b ∧
        f = Polynomial.aeval x a / Polynomial.aeval x b) :
    v.ord (Polynomial.aeval x q) = 1 ∧
      (∀ a : Polynomial K, ¬ q ∣ a → v.ord (Polynomial.aeval x a) = 0) := by
  obtain ⟨π, hπ, hπirr⟩ :=
    Submission.p06_9e0f5043ff_fno_irreducible_aeval K F x hx q hq hqirr v hv
  constructor
  · simpa only [hπ] using v.ord_coe_irreducible hπirr
  · intro a ha
    have hqone : ¬ q ∣ (1 : Polynomial K) := hqirr.not_dvd_one
    have hamem : Polynomial.aeval x a ∈ v.toValuationSubring :=
      (hv _).mpr ⟨a, 1, hqone, by simp⟩
    let z : v.toValuationSubring := ⟨Polynomial.aeval x a, hamem⟩
    have hz : IsUnit z :=
      (Submission.p06_9e0f5043ff_fno_fraction_isunit K F x hx q hq hqirr v hv
        a 1 z hqone (by simp [z])).mpr ha
    simpa only [IsUnit.unit_spec] using v.ord_coe_unit hz.unit

end Submission
