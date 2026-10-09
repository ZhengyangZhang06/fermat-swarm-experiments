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

/-- Polynomial evaluation at a nonunit of a place is a unit exactly away from `(X)`. -/
theorem Submission.p06_9e0f5043ff_vfc_polynomial_unit_criterion :
    ∀ (K F : Type*) [Field K] [Field F] [Algebra K F]
      (s : F) (w : AlgebraicCurve.Place K F),
      s⁻¹ ∉ w.toValuationSubring → ∀ p : Polynomial K,
        (∃ u : Units w.toValuationSubring,
          ((u : w.toValuationSubring) : F) = Polynomial.aeval s p) ↔
        ¬ (Polynomial.X : Polynomial K) ∣ p := by
  intro K F _ _ _ s w hinv p
  have hs : s ∈ w.toValuationSubring :=
    (w.toValuationSubring.mem_or_inv_mem s).resolve_right hinv
  let t : w.toValuationSubring := ⟨s, hs⟩
  have ht : ¬ IsUnit t := by
    rintro ⟨u, hu⟩
    have hmul : s * (((u⁻¹ : Units w.toValuationSubring) : w.toValuationSubring) : F) = 1 := by
      change (t : F) * _ = 1
      rw [← hu]
      exact congrArg (fun x : w.toValuationSubring => (x : F)) u.val_inv
    have hi : (((u⁻¹ : Units w.toValuationSubring) : w.toValuationSubring) : F) = s⁻¹ :=
      eq_inv_of_mul_eq_one_right hmul
    exact hinv (hi ▸ (u⁻¹).val.property)
  -- Evaluate inside the valuation subring using its inherited K-algebra structure.
  let E : Polynomial K →+* w.toValuationSubring := (Polynomial.aeval t).toRingHom
  have hE (q : Polynomial K) : (E q : F) = Polynomial.aeval s q := by
    exact (Polynomial.aeval_algHom_apply
      (IsScalarTower.toAlgHom K w.toValuationSubring F) t q).symm
  let J : Ideal (Polynomial K) := (IsLocalRing.maximalIdeal w.toValuationSubring).comap E
  have hJ : J ≠ ⊤ :=
    Ideal.comap_ne_top E (IsLocalRing.maximalIdeal.isMaximal w.toValuationSubring).ne_top
  have hX : (Polynomial.X : Polynomial K) ∈ J := by
    change E Polynomial.X ∈ IsLocalRing.maximalIdeal w.toValuationSubring
    change Polynomial.aeval t Polynomial.X ∈ IsLocalRing.maximalIdeal w.toValuationSubring
    rw [Polynomial.aeval_X, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact ht
  -- The proper contraction contains the maximal ideal (X), so they coincide.
  have hspan : Ideal.span ({Polynomial.X} : Set (Polynomial K)) = J :=
    (PrincipalIdealRing.isMaximal_of_irreducible Polynomial.irreducible_X).eq_of_le hJ
      (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hX))
  have hunit : IsUnit (E p) ↔ ¬ (Polynomial.X : Polynomial K) ∣ p := by
    rw [← IsLocalRing.notMem_maximalIdeal]
    change p ∉ J ↔ ¬ (Polynomial.X : Polynomial K) ∣ p
    rw [← hspan, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨u, hu⟩
    apply hunit.mp
    refine ⟨u, ?_⟩
    exact Subtype.ext (hu.trans (hE p).symm)
  · intro hp
    obtain ⟨u, hu⟩ := hunit.mpr hp
    exact ⟨u, (congrArg (fun x : w.toValuationSubring => (x : F)) hu).trans (hE p)⟩
/-- Membership of a unit times a parameter-power quotient forces nonnegative exponent. -/
theorem Submission.p06_9e0f5043ff_vfc_unit_power_quotient_exponents :
    ∀ (F : Type*) [Field F] (W : Subring F) (s : F), s ∈ W → s⁻¹ ∉ W →
      ∀ (u : Units W) (r k : ℕ), ((u : W) : F) * s ^ r / s ^ k ∈ W → k ≤ r := by
  intro F _ W s hs hsinv u r k hquot
  have hs0 : s ≠ 0 := by
    intro h
    apply hsinv
    simp [h]
  have hu : ((u : W) : F) * ((↑(u⁻¹) : W) : F) = 1 := by
    exact_mod_cast u.mul_inv
  by_contra hle
  let n := k - r - 1
  have hk : k = r + n + 1 := by
    dsimp [n]
    omega
  have hprod :
      (((u : W) : F) * s ^ r / s ^ k) * ((↑(u⁻¹) : W) : F) * s ^ n ∈ W :=
    W.mul_mem (W.mul_mem hquot (↑(u⁻¹) : W).property) (W.pow_mem hs n)
  have heq :
      (((u : W) : F) * s ^ r / s ^ k) * ((↑(u⁻¹) : W) : F) * s ^ n = s⁻¹ := by
    calc
      _ = (((u : W) : F) * ((↑(u⁻¹) : W) : F)) * (s ^ r * s ^ n) / s ^ k := by
        ring
      _ = s ^ (r + n) / s ^ (r + n + 1) := by
        rw [hu, one_mul, ← pow_add, hk]
      _ = s⁻¹ := by
        rw [pow_succ, div_mul_eq_div_div, div_self (pow_ne_zero _ hs0), one_div]
  exact hsinv (heq ▸ hprod)


namespace Submission
/-- The valuation ring in which the parameter is a nonunit consists exactly of
fractions whose denominator is not divisible by `X`. -/
theorem p06_9e0f5043ff_inf_valuation_fraction_characterization :
    ∀ (K F : Type*) [Field K] [Field F] [Algebra K F] (s : F),
      Transcendental K s →
      (∀ f : F, ∃ a b : Polynomial K, b ≠ 0 ∧
        f = Polynomial.aeval s a / Polynomial.aeval s b) →
      ∀ w : AlgebraicCurve.Place K F, s⁻¹ ∉ w.toValuationSubring →
      ∀ f : F, f ∈ w.toValuationSubring ↔
        ∃ a b : Polynomial K, ¬ (Polynomial.X : Polynomial K) ∣ b ∧
          f = Polynomial.aeval s a / Polynomial.aeval s b := by
  intro K F _ _ _ s hs hfrac w hsinv f
  classical
  let W : Subring F := w.toValuationSubring.toSubring
  have hsW : s ∈ W := (w.toValuationSubring.mem_or_inv_mem s).resolve_right hsinv
  have hs0 : s ≠ 0 := by
    intro h
    apply hsinv
    simp [h]
  have heval_mem (p : Polynomial K) : Polynomial.aeval s p ∈ W := by
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simpa only [map_add] using W.add_mem hp hq
    | monomial n a =>
      rw [Polynomial.aeval_monomial]
      exact W.mul_mem (w.algebraMap_mem' a) (W.pow_mem hsW n)
  have hunit_inv (u : Units W) :
      (((u⁻¹ : Units W) : W) : F) = (((u : W) : F))⁻¹ := by
    exact (Units.map W.subtype.toMonoidHom u).val_inv_eq_inv_val
  have heval_ne (p : Polynomial K) (hp : p ≠ 0) : Polynomial.aeval s p ≠ 0 := by
    intro h
    apply hp
    exact (transcendental_iff_injective.mp hs) (h.trans (map_zero _).symm)
  constructor
  · intro hf
    by_cases hf0 : f = 0
    · exact ⟨0, 1, by simp [Polynomial.X_dvd_iff], by simp [hf0]⟩
    obtain ⟨a, b, hb, hfab⟩ := hfrac f
    have ha : a ≠ 0 := by
      intro h
      apply hf0
      simpa [h] using hfab
    -- Remove all factors of X, leaving polynomials that evaluate to units.
    obtain ⟨a₀, ha_factor, ha₀⟩ :=
      Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd a ha 0
    obtain ⟨b₀, hb_factor, hb₀⟩ :=
      Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd b hb 0
    simp only [map_zero, sub_zero] at ha_factor ha₀ hb_factor hb₀
    obtain ⟨ua, hua⟩ :=
      (p06_9e0f5043ff_vfc_polynomial_unit_criterion K F s w hsinv a₀).mpr ha₀
    obtain ⟨ub, hub⟩ :=
      (p06_9e0f5043ff_vfc_polynomial_unit_criterion K F s w hsinv b₀).mpr hb₀
    let r := a.rootMultiplicity 0
    let k := b.rootMultiplicity 0
    let u : Units W := ua * ub⁻¹
    have hu : ((u : W) : F) = Polynomial.aeval s a₀ / Polynomial.aeval s b₀ := by
      change ((ua : W) : F) * (((ub⁻¹ : Units W) : W) : F) = _
      rw [hunit_inv, hua, hub, div_eq_mul_inv]
    have hnormalized : f = ((u : W) : F) * s ^ r / s ^ k := by
      rw [hfab, ha_factor, hb_factor, hu]
      simp only [map_mul, map_pow, Polynomial.aeval_X]
      dsimp only [r, k]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    -- Membership rules out a negative exponent of the nonunit parameter.
    have hkr : k ≤ r :=
      p06_9e0f5043ff_vfc_unit_power_quotient_exponents F W s hsW hsinv u r k
        (hnormalized ▸ hf)
    refine ⟨Polynomial.X ^ (r - k) * a₀, b₀, hb₀, ?_⟩
    have hb₀_ne : Polynomial.aeval s b₀ ≠ 0 :=
      heval_ne b₀ (fun h => hb₀ (by simp [h]))
    have hpow : s ^ r = s ^ (r - k) * s ^ k := by
      rw [← pow_add, Nat.sub_add_cancel hkr]
    rw [hnormalized, hu]
    simp only [map_mul, map_pow, Polynomial.aeval_X]
    rw [hpow]
    field_simp [hs0, hb₀_ne]
  · rintro ⟨a, b, hb, rfl⟩
    obtain ⟨u, hu⟩ :=
      (p06_9e0f5043ff_vfc_polynomial_unit_criterion K F s w hsinv b).mpr hb
    have hinv : (Polynomial.aeval s b)⁻¹ ∈ W := by
      rw [← hu, ← hunit_inv]
      exact ((u⁻¹ : Units W) : W).property
    change Polynomial.aeval s a / Polynomial.aeval s b ∈ W
    rw [div_eq_mul_inv]
    exact W.mul_mem (heval_mem a) hinv
end Submission
