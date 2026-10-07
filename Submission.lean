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

/-- Polynomial evaluation at the finite place has residue kernel generated by `q`. -/
theorem p06_9e0f5043ff_fpm_rd_eval_kernel
    (K F : Type*) [Field K] [Field F] [Algebra K F] (x : F)
    (hx : Transcendental K x) (q : Polynomial K) (hq : Irreducible q)
    (v : AlgebraicCurve.Place K F)
    (hv : ∀ f : F, f ∈ v.toValuationSubring ↔
      ∃ a b : Polynomial K, ¬ q ∣ b ∧
        f = Polynomial.aeval x a / Polynomial.aeval x b) :
    ∃ e : Polynomial K →ₐ[K] v.toValuationSubring,
      (∀ a : Polynomial K, (e a : F) = Polynomial.aeval x a) ∧
      RingHom.ker ((IsLocalRing.residue v.toValuationSubring).comp e.toRingHom) =
        Ideal.span ({q} : Set (Polynomial K)) := by
  classical
  have hinj := transcendental_iff_injective.mp hx
  have hne (a : Polynomial K) (ha : a ≠ 0) : Polynomial.aeval x a ≠ 0 := by
    intro h
    exact ha (hinj (h.trans (map_zero (Polynomial.aeval x)).symm))
  -- Denominator 1 lifts every polynomial evaluation into the valuation ring.
  have hmem (a : Polynomial K) : Polynomial.aeval x a ∈ v.toValuationSubring :=
    (hv _).mpr ⟨a, 1, hq.not_dvd_one, by rw [map_one, div_one]⟩
  let e : Polynomial K →ₐ[K] v.toValuationSubring :=
    { toFun := fun a => ⟨Polynomial.aeval x a, hmem a⟩
      map_one' := Subtype.ext (map_one (Polynomial.aeval x))
      map_mul' := fun a b => Subtype.ext (map_mul (Polynomial.aeval x) a b)
      map_zero' := Subtype.ext (map_zero (Polynomial.aeval x))
      map_add' := fun a b => Subtype.ext (map_add (Polynomial.aeval x) a b)
      commutes' := fun c => Subtype.ext ((Polynomial.aeval x).commutes c) }
  have he (a : Polynomial K) : (e a : F) = Polynomial.aeval x a := rfl
  -- A polynomial not divisible by q has an inverse evaluation in the valuation ring.
  have hunit (a : Polynomial K) (ha : ¬ q ∣ a) : IsUnit (e a) := by
    have ha0 : Polynomial.aeval x a ≠ 0 := hne a (fun h => ha (h ▸ dvd_zero q))
    have hi : (Polynomial.aeval x a)⁻¹ ∈ v.toValuationSubring :=
      (hv _).mpr ⟨1, a, ha, by rw [map_one, one_div]⟩
    exact isUnit_iff_exists_inv.mpr
      ⟨⟨(Polynomial.aeval x a)⁻¹, hi⟩, Subtype.ext (mul_inv_cancel₀ ha0)⟩
  -- An inverse of q(x) would force q to divide an allowed denominator.
  have hq_nonunit : ¬ IsUnit (e q) := by
    intro hu
    obtain ⟨z, hz⟩ := isUnit_iff_exists_inv.mp hu
    have hmul : Polynomial.aeval x q * (z : F) = 1 :=
      congrArg (fun t : v.toValuationSubring => (t : F)) hz
    obtain ⟨a, b, hb, hzrep⟩ := (hv (z : F)).mp z.property
    have hb0 : Polynomial.aeval x b ≠ 0 := hne b (fun h => hb (h ▸ dvd_zero q))
    have hab : Polynomial.aeval x q * Polynomial.aeval x a = Polynomial.aeval x b := by
      calc
        Polynomial.aeval x q * Polynomial.aeval x a =
            (Polynomial.aeval x q * (z : F)) * Polynomial.aeval x b := by
          rw [hzrep, ← mul_div_assoc, div_mul_cancel₀ _ hb0]
        _ = Polynomial.aeval x b := by rw [hmul, one_mul]
    apply hb
    refine ⟨a, hinj ?_⟩
    rw [map_mul]
    exact hab.symm
  have hq_zero : IsLocalRing.residue v.toValuationSubring (e q) = 0 := by
    by_contra h
    exact hq_nonunit ((IsLocalRing.residue_ne_zero_iff_isUnit _).mp h)
  refine ⟨e, he, ?_⟩
  ext a
  rw [RingHom.mem_ker, Ideal.mem_span_singleton]
  change IsLocalRing.residue v.toValuationSubring (e a) = 0 ↔ q ∣ a
  constructor
  · intro ha
    by_contra hqa
    exact ((IsLocalRing.residue_ne_zero_iff_isUnit _).mpr (hunit a hqa)) ha
  · rintro ⟨b, rfl⟩
    rw [map_mul, map_mul, hq_zero, zero_mul]
theorem p06_9e0f5043ff_fpm_rd_residue_surjective
    (K F : Type*) [Field K] [Field F] [Algebra K F] (x : F)
    (hx : Transcendental K x) (q : Polynomial K) (hq : Irreducible q)
    (v : AlgebraicCurve.Place K F)
    (hrep : ∀ h : v.toValuationSubring, ∃ a b : Polynomial K,
      ¬ q ∣ b ∧ (h : F) = Polynomial.aeval x a / Polynomial.aeval x b)
    (e : Polynomial K →ₐ[K] v.toValuationSubring)
    (he : ∀ a : Polynomial K, (e a : F) = Polynomial.aeval x a)
    (heq : IsLocalRing.residue v.toValuationSubring (e q) = 0) :
    Function.Surjective ((IsLocalRing.residue v.toValuationSubring).comp e.toRingHom) := by
  let ρ := IsLocalRing.residue v.toValuationSubring
  let φ := ρ.comp e.toRingHom
  intro r
  obtain ⟨h, rfl⟩ := IsLocalRing.residue_surjective (R := v.toValuationSubring) r
  obtain ⟨a, b, hb, hab⟩ := hrep h
  have hb0 : b ≠ 0 := fun hb0 => hb (hb0 ▸ dvd_zero q)
  have heb0 : Polynomial.aeval x b ≠ 0 := by
    intro heb0
    apply hb0
    exact (transcendental_iff_injective.mp hx) (by simpa using heb0)
  obtain ⟨u, t, hut⟩ := hq.coprime_iff_not_dvd.mpr hb
  have htb : φ t * φ b = 1 := by
    have hφq : φ q = 0 := heq
    simpa only [map_add, map_mul, map_one, hφq, mul_zero, zero_add]
      using congrArg φ hut
  have hmul : h * e b = e a := by
    apply Subtype.ext
    change (h : F) * (e b : F) = (e a : F)
    rw [he, he, hab, div_mul_cancel₀ _ heb0]
  have hres : ρ h * φ b = φ a := by
    change ρ h * ρ (e b) = ρ (e a)
    simpa only [map_mul] using congrArg ρ hmul
  refine ⟨a * t, ?_⟩
  change φ (a * t) = ρ h
  calc
    φ (a * t) = φ a * φ t := map_mul φ a t
    _ = (ρ h * φ b) * φ t := by rw [hres]
    _ = ρ h := by rw [mul_assoc, mul_comm (φ b) (φ t), htb, mul_one]

end Submission
