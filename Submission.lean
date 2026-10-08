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

/-- An integer order characterizing subring membership makes every ideal principal. -/
theorem p06_9e0f5043ff_elp_principal_ideals_of_order :
    ∀ (F : Type*) [Field F] (A : Subring F) (ν : F → ℤ),
      (∀ f g : F, f ≠ 0 → g ≠ 0 → ν (f / g) = ν f - ν g) →
      (∀ f : F, f ≠ 0 → (f ∈ A ↔ 0 ≤ ν f)) → IsPrincipalIdealRing A := by
  intro F _ A ν hdiv hmem
  classical
  constructor
  intro I
  by_cases hI : I = ⊥
  · subst I
    infer_instance
  obtain ⟨z, hzI, hz⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  -- Minimize natural orders; subring membership will recover their integer values.
  have hex : ∃ n : ℕ, ∃ h : A, h ∈ I ∧ (h : F) ≠ 0 ∧ (ν (h : F)).toNat = n :=
    ⟨_, z, hzI, fun h => hz (Subtype.ext h), rfl⟩
  obtain ⟨h, hhI, hh, hν⟩ := Nat.find_spec hex
  refine ⟨⟨h, le_antisymm ?_ ((Ideal.span_singleton_le_iff_mem I).mpr hhI)⟩⟩
  intro z hzI
  by_cases hz : (z : F) = 0
  · have hz' : z = 0 := Subtype.ext hz
    rw [hz']
    exact Ideal.zero_mem _
  have hh_nonneg : 0 ≤ ν (h : F) := (hmem _ hh).mp h.property
  have hz_nonneg : 0 ≤ ν (z : F) := (hmem _ hz).mp z.property
  have hmin : (ν (h : F)).toNat ≤ (ν (z : F)).toNat := by
    rw [hν]
    exact Nat.find_min' hex ⟨z, hzI, hz, rfl⟩
  have horder : ν (h : F) ≤ ν (z : F) := by
    simpa only [Int.toNat_of_nonneg hh_nonneg, Int.toNat_of_nonneg hz_nonneg] using
      (Int.ofNat_le.mpr hmin)
  -- Leastness makes the quotient an element of A, giving the required multiple of h.
  have hquot : (z : F) / (h : F) ∈ A := by
    apply (hmem _ (div_ne_zero hz hh)).mpr
    rw [hdiv _ _ hz hh]
    exact sub_nonneg.mpr horder
  apply Ideal.mem_span_singleton'.mpr
  refine ⟨⟨(z : F) / (h : F), hquot⟩, ?_⟩
  apply Subtype.ext
  exact div_mul_cancel₀ _ hh

/-- Clear the first row by an invertible column operation, preserving the trailing block.
The correction matrix squares to zero, so `1 - M` has the explicit inverse `1 + M`.
Divisibility supplies the coefficients without requiring the pivot to be nonzero or a unit. -/
theorem p06_9e0f5043ff_sdp_clear_first_row :
    ∀ (R : Type*) [CommRing R] (m : ℕ)
      (H : Matrix (Fin (m + 1)) (Fin (m + 1)) R),
      (∀ i : Fin m, H i.succ 0 = 0) →
      (∀ j : Fin m, H 0 0 ∣ H 0 j.succ) →
      ∃ V : Matrix (Fin (m + 1)) (Fin (m + 1)) R,
        IsUnit V ∧ H * V = Matrix.of (fun i j =>
          Fin.cases (Fin.cases (H 0 0) (fun _ => 0) j)
            (fun i' => Fin.cases 0 (fun j' => H i'.succ j'.succ) j) i) := by
  classical
  intro R _ m H hcol hdiv
  choose b hb using hdiv
  let M : Matrix (Fin (m + 1)) (Fin (m + 1)) R :=
    Matrix.of (fun i j => Fin.cases (Fin.cases 0 b j) (fun _ => 0) i)
  have hM0 (i : Fin (m + 1)) : M i 0 = 0 := by
    refine Fin.cases ?_ (fun _ => ?_) i <;> rfl
  have hMs (i : Fin m) (j : Fin (m + 1)) : M i.succ j = 0 := rfl
  have hMM : M * M = 0 := by
    ext i j
    simp [Matrix.mul_apply, Fin.sum_univ_succ, hM0, hMs]
  have hHM (i j : Fin (m + 1)) :
      (H * M) i j = H i 0 * Fin.cases 0 b j := by
    simp [Matrix.mul_apply, Fin.sum_univ_succ, M]
  refine ⟨1 - M, ?_, ?_⟩
  · refine ⟨⟨1 - M, 1 + M, ?_, ?_⟩, rfl⟩
    · simp [sub_mul, mul_add, hMM]
    · simp [mul_sub, add_mul, hMM]
  · rw [mul_sub, mul_one]
    ext i j
    refine Fin.cases ?_ (fun i' => ?_) i <;>
      refine Fin.cases ?_ (fun j' => ?_) j <;>
      simp [Matrix.sub_apply, hHM, hcol, hb]
/-- Clear the first column below a divisible pivot by a unit that preserves the first row. -/
theorem p06_9e0f5043ff_sdp_clear_first_column
    (R : Type*) [CommRing R] (m : ℕ)
    (B : Matrix (Fin (m + 1)) (Fin (m + 1)) R)
    (h : ∀ i : Fin m, B 0 0 ∣ B i.succ 0) :
    ∃ U : Matrix (Fin (m + 1)) (Fin (m + 1)) R,
      IsUnit U ∧ (∀ j : Fin (m + 1), (U * B) 0 j = B 0 j) ∧
        (∀ i : Fin m, (U * B) i.succ 0 = 0) := by
  classical
  choose a ha using h
  -- Extend the chosen coefficients by zero so the first row is unchanged.
  let c : Fin (m + 1) → R := Fin.cases 0 a
  let N : Matrix (Fin (m + 1)) (Fin (m + 1)) R :=
    Matrix.of fun i j => if j = 0 then c i else 0
  have hmul (M : Matrix (Fin (m + 1)) (Fin (m + 1)) R)
      (i j : Fin (m + 1)) : (N * M) i j = c i * M 0 j := by
    simp [Matrix.mul_apply, N]
  have hsq : N * N = 0 := by
    ext i j
    simp [hmul, N, c]
  -- Since N² = 0, the clearing matrix 1 - N has two-sided inverse 1 + N.
  refine ⟨1 - N, ?_, ?_, ?_⟩
  · refine ⟨⟨1 - N, 1 + N, ?_, ?_⟩, rfl⟩
    · simp [sub_mul, mul_add, hsq]
    · simp [mul_sub, add_mul, hsq]
  · intro j
    simp [sub_mul, hmul, c]
  · intro i
    simp [sub_mul, hmul, c, ha i, mul_comm]

end Submission

/-- Reciprocal evaluation has order minus the degree at the place above the origin. -/
theorem Submission.p06_9e0f5043ff_inf_reciprocal_polynomial_order :
    ∀ (K F : Type*) [Field K] [Field F] [Algebra K F] (s : F),
      Transcendental K s → ∀ v : AlgebraicCurve.Place K F, v.ord s = 1 →
      (∀ c : Polynomial K, ¬ (Polynomial.X : Polynomial K) ∣ c →
        v.ord (Polynomial.aeval s c) = 0) →
      ∀ a : Polynomial K, a ≠ 0 →
        v.ord (Polynomial.aeval s⁻¹ a) = -(a.natDegree : ℤ) := by
  intro K F _ _ _ s hs v hv hzero a ha
  have hs0 : s ≠ 0 := by
    intro h
    exact hs ⟨Polynomial.X, Polynomial.X_ne_zero, by simpa using h⟩
  have hrev : a.reverse ≠ 0 := fun h => ha (Polynomial.reverse_eq_zero.mp h)
  have heval : Polynomial.aeval s a.reverse ≠ 0 := fun h => hs ⟨a.reverse, hrev, h⟩
  have hnot : ¬ (Polynomial.X : Polynomial K) ∣ a.reverse := by
    simpa only [Polynomial.X_dvd_iff, Polynomial.coeff_zero_reverse,
      Polynomial.leadingCoeff_eq_zero] using ha
  have horder : v.ord (Polynomial.aeval s a.reverse) = 0 := hzero _ hnot
  -- Reversal writes reciprocal evaluation as a negative power times a unit at v.
  have hidentity : Polynomial.aeval s⁻¹ a =
      s ^ (-(a.natDegree : ℤ)) * Polynomial.aeval s a.reverse := by
    let : Invertible s⁻¹ := invertibleOfNonzero (inv_ne_zero hs0)
    simpa only [invOf_eq_inv, inv_inv, ← Polynomial.aeval_def, zpow_neg,
      zpow_natCast, inv_pow, mul_comm] using
      (Polynomial.eval₂_reverse_mul_pow (algebraMap K F) s⁻¹ a).symm
  rw [hidentity, v.ord_mul (zpow_ne_zero _ hs0) heval, v.ord_zpow, hv,
    horder, mul_one, add_zero]
