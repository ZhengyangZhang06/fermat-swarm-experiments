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

/-- The reciprocal of the fraction-ring variable is transcendental and presents every fraction. -/
theorem Submission.p06_9e0f5043ff_inf_reciprocal_presentation :
    ∀ (K : Type*) [Field K],
      Transcendental K
        ((algebraMap (Polynomial K) (FractionRing (Polynomial K)) Polynomial.X)⁻¹) ∧
      (∀ f : FractionRing (Polynomial K), ∃ a b : Polynomial K, b ≠ 0 ∧
        f = Polynomial.aeval
          ((algebraMap (Polynomial K) (FractionRing (Polynomial K)) Polynomial.X)⁻¹) a /
          Polynomial.aeval
          ((algebraMap (Polynomial K) (FractionRing (Polynomial K)) Polynomial.X)⁻¹) b) := by
  intro K _
  let t : FractionRing (Polynomial K) :=
    algebraMap (Polynomial K) (FractionRing (Polynomial K)) Polynomial.X
  have hinj := IsFractionRing.injective (Polynomial K) (FractionRing (Polynomial K))
  have ht : t ≠ 0 := by
    exact fun h => Polynomial.X_ne_zero (hinj (h.trans (map_zero _).symm))
  have heval (p : Polynomial K) :
      Polynomial.aeval t p = algebraMap (Polynomial K) (FractionRing (Polynomial K)) p := by
    simp [t, Polynomial.aeval_algebraMap_apply]
  have htrans : Transcendental K t :=
    (transcendental_algebraMap_iff hinj).mpr (Polynomial.transcendental_X K)
  have hs : Transcendental K t⁻¹ := by
    intro h
    exact htrans (IsAlgebraic.inv_iff.mp h)
  refine ⟨hs, ?_⟩
  intro f
  change ∃ a b : Polynomial K, b ≠ 0 ∧
    f = Polynomial.aeval t⁻¹ a / Polynomial.aeval t⁻¹ b
  by_cases hf : f = 0
  · exact ⟨0, 1, one_ne_zero, by simp [hf]⟩
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (Polynomial K) f
  have hb0 : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
  have hbr : b.reverse ≠ 0 := by simpa using hb0
  have hbev : Polynomial.aeval t⁻¹ b.reverse ≠ 0 := by
    exact fun h => hbr ((transcendental_iff_injective.mp hs) (by simpa using h))
  let : Invertible t := invertibleOfNonzero ht
  have hreverse (p : Polynomial K) :
      algebraMap (Polynomial K) (FractionRing (Polynomial K)) p =
        Polynomial.aeval t⁻¹ p.reverse / (t⁻¹) ^ p.natDegree := by
    have h := Polynomial.eval₂_reverse_mul_pow
      (algebraMap K (FractionRing (Polynomial K))) t p
    simpa only [invOf_eq_inv, ← Polynomial.aeval_def, heval, inv_pow,
      div_inv_eq_mul] using h.symm
  rw [← hab, hreverse a, hreverse b]
  by_cases hdeg : a.natDegree ≤ b.natDegree
  · refine ⟨Polynomial.X ^ (b.natDegree - a.natDegree) * a.reverse,
      b.reverse, hbr, ?_⟩
    rw [map_mul, map_pow, Polynomial.aeval_X, pow_sub₀ _ (inv_ne_zero ht) hdeg]
    field_simp
  · refine ⟨a.reverse, Polynomial.X ^ (a.natDegree - b.natDegree) * b.reverse,
      mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) hbr, ?_⟩
    rw [map_mul, map_pow, Polynomial.aeval_X,
      pow_sub₀ _ (inv_ne_zero ht) (Nat.le_of_lt (Nat.lt_of_not_ge hdeg))]
    field_simp
