/-
Copyright 2026 Anthropic, PBC. Licensed under Apache-2.0; see LICENSE.
Source: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_HeckeEis_eichlerShimuraMap_injective.lean
Modified: replaced the proof with sorry and removed P2M proof imports.
Requires the upstream Definitions modules and their dependencies.
-/

import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_HeckeEis_EichlerIntegral

set_option autoImplicit false

open scoped Manifold MatrixGroups ModularForm

theorem HeckeEis.eichlerShimuraMap_injective (N : ℕ) [NeZero N] (n : ℕ) :
    Function.Injective
      (fun f : CuspForm (CongruenceSubgroup.Gamma0 N) ((n : ℤ) + 2) ↦ HeckeEis.eichlerShimuraMap n N f) := by
  sorry

namespace Submission

theorem p02_es_177ebb5a_sm_holomorphic
    (n : ℕ) (h : UpperHalfPlane → ℂ)
    (E : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n))
    (hE : HeckeEis.IsEichlerIntegral n h E) :
    DifferentiableOn ℂ
      (fun z : ℂ => MvPolynomial.eval (fun j : Fin 2 => if j = 0 then 1 else -z)
        (E (UpperHalfPlane.ofComplex z)).val)
      {z : ℂ | 0 < z.im} := by
  classical
  let s := (Finsupp.finite_of_degree_eq (σ := Fin 2) n).toFinset
  have hexpand (z : ℂ) :
      MvPolynomial.eval (fun j : Fin 2 => if j = 0 then 1 else -z)
          (E (UpperHalfPlane.ofComplex z)).val =
        ∑ d ∈ s, MvPolynomial.coeff d (E (UpperHalfPlane.ofComplex z)).val *
          (-z) ^ d 1 := by
    rw [MvPolynomial.eval_eq']
    simp only [Fin.prod_univ_two, Fin.isValue, ite_true, one_pow, one_ne_zero,
      ite_false, one_mul]
    apply Finset.sum_subset
    · intro d hd
      have hdeg := (E (UpperHalfPlane.ofComplex z)).property
        (MvPolynomial.mem_support_iff.mp hd)
      simpa [s, Finsupp.degree_eq_weight_one, Pi.one_def] using hdeg
    · intro d _ hd
      simp [MvPolynomial.notMem_support_iff.mp hd]
  simp_rw [hexpand]
  apply DifferentiableOn.fun_sum
  intro d _
  apply DifferentiableOn.mul
  · intro z hz
    exact (hE d ⟨z, hz⟩).differentiableAt.differentiableWithinAt
  · exact (differentiable_id.neg.pow (d 1)).differentiableOn

open scoped Pointwise in
theorem p02_es_177ebb5a_pp_scaled_cusp_decay
    (N : ℕ) [NeZero N] (n : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) ((n : ℤ) + 2))
    (σ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    ∃ (a C Y : ℝ), 0 < a ∧ 0 ≤ C ∧ ∀ τ : UpperHalfPlane, Y ≤ τ.im →
      ‖(HeckeEis.jFactor σ τ) ^ (-((n : ℤ) + 2)) * f (σ • τ)‖ ≤
        C * Real.exp (-a * τ.im) := by
  let Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ) := CongruenceSubgroup.Gamma0 N
  let g : Matrix.GeneralLinearGroup (Fin 2) ℝ := σ
  have hg : (Matrix.SpecialLinearGroup.mapGL ℚ σ⁻¹).map (Rat.castHom ℝ) = g⁻¹ := by
    change (Matrix.SpecialLinearGroup.mapGL ℚ σ⁻¹).map (algebraMap ℚ ℝ) = g⁻¹
    rw [Matrix.SpecialLinearGroup.map_mapGL, map_inv]
    rfl
  have : (ConjAct.toConjAct g⁻¹ • Γ).IsArithmetic := by
    rw [← hg]
    exact Subgroup.IsArithmetic.conj Γ (Matrix.SpecialLinearGroup.mapGL ℚ σ⁻¹)
  let u := CuspForm.translate f g
  obtain ⟨a, ha, hdecay⟩ := CuspFormClass.exp_decay_atImInfty' u
  obtain ⟨C, hC, hbound⟩ := hdecay.exists_nonneg
  obtain ⟨Y, hY⟩ := (UpperHalfPlane.atImInfty_mem _).mp hbound.bound
  refine ⟨a, C, Y, ha, hC, ?_⟩
  intro τ hτ
  have h := hY τ hτ
  change ‖((f : UpperHalfPlane → ℂ) ∣[(n : ℤ) + 2] σ) τ‖ ≤
    C * ‖Real.exp (-a * τ.im)‖ at h
  rw [HeckeEis.jFactor_eq_denom, mul_comm]
  simpa only [ModularForm.SL_slash_apply, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)] using! h
theorem p02_es_177ebb5a_pcl_scaled_pullback_derivative :
    ∀ (n : ℕ) (f : UpperHalfPlane → ℂ)
      (F : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n)),
      HeckeEis.IsEichlerIntegral n f F →
      ∀ (σ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (d : Fin 2 →₀ ℕ)
        (τ : UpperHalfPlane),
        HasDerivAt (fun z : ℂ => MvPolynomial.coeff d
          (F (σ • UpperHalfPlane.ofComplex z)).val)
          ((HeckeEis.jFactor σ τ) ^ (-((n : ℤ) + 2)) * f (σ • τ) *
            MvPolynomial.coeff d ((HeckeEis.binaryFormRepSL ℂ n σ)
              (HeckeEis.linePow n (τ : ℂ))).val) (τ : ℂ) := by
  intro n f F hF σ d τ
  have hσ : HasDerivAt
      (fun z : ℂ => ((σ • UpperHalfPlane.ofComplex z : UpperHalfPlane) : ℂ))
      ((HeckeEis.jFactor σ τ) ^ (-2 : ℤ)) (τ : ℂ) := by
    simpa [HeckeEis.jFactor_eq_denom, zpow_neg, MulAction.compHom_smul_def,
      ← Int.cast_det] using
      (UpperHalfPlane.hasStrictDerivAt_smul
        (g := Matrix.SpecialLinearGroup.mapGL ℝ σ)
        (by simp [← Int.cast_det]) τ).hasDerivAt
  have houter : HasDerivAt
      (fun z : ℂ => MvPolynomial.coeff d (F (UpperHalfPlane.ofComplex z)).val)
      (f (σ • τ) * MvPolynomial.coeff d
        (HeckeEis.linePow n ((σ • τ : UpperHalfPlane) : ℂ)).val)
      ((σ • UpperHalfPlane.ofComplex (τ : ℂ) : UpperHalfPlane) : ℂ) := by
    simpa only [UpperHalfPlane.ofComplex_apply] using hF d (σ • τ)
  have hcomp := houter.comp (τ : ℂ) hσ
  simp only [Function.comp_def, UpperHalfPlane.ofComplex_apply] at hcomp
  apply hcomp.congr_deriv
  rw [HeckeEis.binaryFormRepSL_linePow, Submodule.coe_smul,
    MvPolynomial.coeff_smul, smul_eq_mul, ← zpow_natCast]
  have hp : (HeckeEis.jFactor σ τ) ^ (-((n : ℤ) + 2)) *
      (HeckeEis.jFactor σ τ) ^ (n : ℤ) =
      (HeckeEis.jFactor σ τ) ^ (-2 : ℤ) := by
    rw [← zpow_add₀ (HeckeEis.jFactor_ne_zero σ τ)]
    congr 1
    omega
  rw [← hp]
  ring

theorem p02_es_177ebb5a_pcl_linear_linepow_growth :
    ∀ (n : ℕ) (T : ↥(HeckeEis.BinaryForm ℂ n) →ₗ[ℂ] ↥(HeckeEis.BinaryForm ℂ n)),
      ∃ K : ℝ, 0 ≤ K ∧ ∀ (z : ℂ) (d : Fin 2 →₀ ℕ),
        ‖MvPolynomial.coeff d (T (HeckeEis.linePow n z)).val‖ ≤ K * (1 + ‖z‖) ^ n := by
  classical
  intro n T
  let b : Fin (n + 1) → ↥(HeckeEis.BinaryForm ℂ n) := fun r =>
    ⟨MvPolynomial.X 0 ^ (r : ℕ) * MvPolynomial.X 1 ^ (n - r), by
      apply (MvPolynomial.mem_homogeneousSubmodule n _).mpr
      simpa only [Nat.add_sub_of_le (Nat.le_of_lt_succ r.isLt)] using
        (MvPolynomial.isHomogeneous_X_pow (R := ℂ) (0 : Fin 2) (r : ℕ)).mul
          (MvPolynomial.isHomogeneous_X_pow (R := ℂ) (1 : Fin 2) (n - r))⟩
  let k : Fin (n + 1) → ℝ := fun r =>
    ∑ d ∈ (T (b r)).val.support, ‖MvPolynomial.coeff d (T (b r)).val‖
  have hk (r : Fin (n + 1)) : 0 ≤ k r :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hcoeff (r : Fin (n + 1)) (d : Fin 2 →₀ ℕ) :
      ‖MvPolynomial.coeff d (T (b r)).val‖ ≤ k r := by
    by_cases hd : d ∈ (T (b r)).val.support
    · exact Finset.single_le_sum (fun e _ => norm_nonneg
        (MvPolynomial.coeff e (T (b r)).val)) hd
    · rw [MvPolynomial.notMem_support_iff.mp hd, norm_zero]
      exact hk r
  have hexpand (z : ℂ) : HeckeEis.linePow n z =
      ∑ r : Fin (n + 1), ((n.choose r : ℂ) * z ^ (r : ℕ)) • b r := by
    apply Subtype.ext
    simp only [Submodule.coe_sum, Submodule.coe_smul, HeckeEis.coe_linePow]
    change (MvPolynomial.C z * MvPolynomial.X 0 + MvPolynomial.X 1) ^ n =
      ∑ r : Fin (n + 1), ((n.choose r : ℂ) * z ^ (r : ℕ)) •
        (MvPolynomial.X 0 ^ (r : ℕ) * MvPolynomial.X 1 ^ (n - r))
    rw [add_pow, ← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro r _
    simp only [mul_pow, MvPolynomial.smul_eq_C_mul, map_mul, map_pow, map_natCast]
    ring
  refine ⟨∑ r : Fin (n + 1), (n.choose r : ℝ) * k r,
    Finset.sum_nonneg (fun r _ => mul_nonneg (Nat.cast_nonneg _) (hk r)), ?_⟩
  intro z d
  have hpower (r : Fin (n + 1)) : ‖z‖ ^ (r : ℕ) ≤ (1 + ‖z‖) ^ n :=
    (pow_le_pow_left₀ (norm_nonneg z) (by linarith) _).trans
      (pow_le_pow_right₀ (by linarith [norm_nonneg z]) (Nat.le_of_lt_succ r.isLt))
  rw [hexpand, map_sum]
  simp only [map_smul, Submodule.coe_sum, Submodule.coe_smul, MvPolynomial.coeff_sum,
    MvPolynomial.coeff_smul, smul_eq_mul]
  calc
    ‖∑ r : Fin (n + 1), ((n.choose r : ℂ) * z ^ (r : ℕ)) *
        MvPolynomial.coeff d (T (b r)).val‖ ≤
        ∑ r : Fin (n + 1), ‖((n.choose r : ℂ) * z ^ (r : ℕ)) *
          MvPolynomial.coeff d (T (b r)).val‖ := norm_sum_le _ _
    _ = ∑ r : Fin (n + 1), (n.choose r : ℝ) * ‖z‖ ^ (r : ℕ) *
        ‖MvPolynomial.coeff d (T (b r)).val‖ := by
      simp only [norm_mul, norm_pow, Complex.norm_natCast]
    _ ≤ ∑ r : Fin (n + 1), (n.choose r : ℝ) * (1 + ‖z‖) ^ n * k r := by
      apply Finset.sum_le_sum
      intro r _
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hpower r) (Nat.cast_nonneg _))
        (hcoeff r d) (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (by positivity))
    _ = (∑ r : Fin (n + 1), (n.choose r : ℝ) * k r) * (1 + ‖z‖) ^ n := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro r _
      ring

theorem p02_es_177ebb5a_lcd_monomial_expansion
    (n : ℕ) (Q : ↥(HeckeEis.BinaryForm ℂ n)) :
    Q.val = ∑ r : Fin (n + 1),
      MvPolynomial.coeff
          (Finsupp.single (0 : Fin 2) r.val + Finsupp.single (1 : Fin 2) (n - r.val))
          Q.val •
        MvPolynomial.monomial
          (Finsupp.single (0 : Fin 2) r.val + Finsupp.single (1 : Fin 2) (n - r.val))
          (1 : ℂ) := by
  classical
  let e (r : Fin (n + 1)) : Fin 2 →₀ ℕ :=
    Finsupp.single 0 r.val + Finsupp.single 1 (n - r.val)
  have he (r : Fin (n + 1)) : (e r).degree = n := by
    simp [e, Finsupp.degree_eq_sum, Fin.sum_univ_two,
      Nat.add_sub_of_le (Nat.le_of_lt_succ r.isLt)]
  change Q.val = ∑ r, MvPolynomial.coeff (e r) Q.val •
    MvPolynomial.monomial (e r) (1 : ℂ)
  apply MvPolynomial.ext
  intro d
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_smul, MvPolynomial.coeff_monomial]
  by_cases hd : d.degree = n
  · have hsum : d 0 + d 1 = n := by
      simpa [Finsupp.degree_eq_sum, Fin.sum_univ_two] using hd
    let r : Fin (n + 1) := ⟨d 0, by omega⟩
    have hr : e r = d := by
      ext i
      fin_cases i <;> simp [e, r, ← hsum]
    have huniq (s : Fin (n + 1)) (hs : e s = d) : s = r := by
      apply Fin.ext
      have hzero := congrArg (fun t : Fin 2 →₀ ℕ => t 0) hs
      simpa [e, r] using hzero
    rw [Finset.sum_eq_single r]
    · simp [hr]
    · intro s _ hs
      have hne : e s ≠ d := fun h => hs (huniq s h)
      simp [hne]
    · simp
  · rw [MvPolynomial.IsHomogeneous.coeff_eq_zero Q.property hd]
    symm
    apply Finset.sum_eq_zero
    intro r _
    have hne : e r ≠ d := fun h => hd (h ▸ he r)
    simp [hne]

theorem p02_es_177ebb5a_crl_imaginary_ray_limit :
    ∀ (n : ℕ) (a : ℝ) (H G : ℂ → ℂ), 0 < a →
      ContinuousOn G {z : ℂ | 0 < z.im} →
      (∀ z : ℂ, 0 < z.im → HasDerivAt H (G z) z) →
      (∃ C Y : ℝ, 0 ≤ C ∧ 1 ≤ Y ∧ ∀ t : ℝ, Y ≤ t →
        ‖G ((t : ℂ) * Complex.I)‖ ≤ C * (1 + t) ^ n * Real.exp (-a * t)) →
      ∃ A : ℂ, Filter.Tendsto (fun y : ℝ => H ((y : ℂ) * Complex.I))
        Filter.atTop (nhds A) := by
  intro n a H G ha hG hH hbound
  obtain ⟨C, Y, hC, hY, hbound⟩ := hbound
  have hpos (t : ℝ) (ht : t ∈ Set.Ioi Y) : 0 < t := by
    have := ht.out
    linarith
  have hderiv (t : ℝ) (ht : t ∈ Set.Ioi Y) :
      HasDerivAt (fun y : ℝ => H ((y : ℂ) * Complex.I))
        (G ((t : ℂ) * Complex.I) * Complex.I) t := by
    have hz : 0 < ((t : ℂ) * Complex.I).im := by simpa using hpos t ht
    simpa using ((hH _ hz).comp (t : ℂ)
      ((hasDerivAt_id (t : ℂ)).mul_const Complex.I)).comp_ofReal
  have hcont : ContinuousOn (fun t : ℝ => G ((t : ℂ) * Complex.I) * Complex.I)
      (Set.Ioi Y) := by
    apply ContinuousOn.mul_const _ Complex.I
    apply hG.comp (Complex.continuous_ofReal.mul_const Complex.I).continuousOn
    intro t ht
    simpa using hpos t ht
  -- Pinned mathlib: Analysis/SpecialFunctions/Gaussian/GaussianIntegral.lean.
  -- Its exponential moment estimate applies with real power n and decay power 1.
  have hmoment : MeasureTheory.IntegrableOn
      (fun t : ℝ => t ^ n * Real.exp (-a * t)) (Set.Ioi (0 : ℝ)) := by
    simpa using integrableOn_rpow_mul_exp_neg_mul_rpow
      (s := (n : ℝ)) (p := (1 : ℝ)) (by linarith [Nat.cast_nonneg (α := ℝ) n])
      zero_lt_one ha
  have hmajorant : MeasureTheory.IntegrableOn
      (fun t : ℝ => (C * 2 ^ n) * (t ^ n * Real.exp (-a * t))) (Set.Ioi Y) :=
    (hmoment.mono_set (Set.Ioi_subset_Ioi (by linarith))).const_mul _
  have hint : MeasureTheory.IntegrableOn
      (fun t : ℝ => G ((t : ℂ) * Complex.I) * Complex.I) (Set.Ioi Y) := by
    apply hmajorant.mono' (hcont.aestronglyMeasurable measurableSet_Ioi)
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    have hpow : (1 + t) ^ n ≤ (2 * t) ^ n :=
      pow_le_pow_left₀ (by linarith [hpos t ht]) (by linarith [ht.out]) n
    calc
      ‖G ((t : ℂ) * Complex.I) * Complex.I‖ = ‖G ((t : ℂ) * Complex.I)‖ := by
        rw [norm_mul, Complex.norm_I, mul_one]
      _ ≤ C * (1 + t) ^ n * Real.exp (-a * t) := hbound t ht.out.le
      _ ≤ C * (2 * t) ^ n * Real.exp (-a * t) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hC) (Real.exp_pos _).le
      _ = (C * 2 ^ n) * (t ^ n * Real.exp (-a * t)) := by rw [mul_pow]; ring
  -- Pinned mathlib: MeasureTheory/Integral/IntegralEqImproper.lean packages the
  -- FTC tail estimate and completeness argument for an integrable derivative.
  exact ⟨_, MeasureTheory.tendsto_limUnder_of_hasDerivAt_of_integrableOn_Ioi hderiv hint⟩

end Submission
