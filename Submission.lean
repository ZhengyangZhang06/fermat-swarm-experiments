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
theorem p02_es_177ebb5a_crl_horizontal_difference_limit :
    ∀ (n : ℕ) (a : ℝ) (H G : ℂ → ℂ), 0 < a →
      ContinuousOn G {z : ℂ | 0 < z.im} →
      (∀ z : ℂ, 0 < z.im → HasDerivAt H (G z) z) →
      (∀ B : ℝ, 0 < B → ∃ C Y : ℝ, 0 ≤ C ∧ 1 ≤ Y ∧
        ∀ z : ℂ, |z.re| ≤ B → Y ≤ z.im →
          ‖G z‖ ≤ C * (1 + z.im) ^ n * Real.exp (-a * z.im)) →
      ∀ x : ℝ, Filter.Tendsto
        (fun y : ℝ => H ((x : ℂ) + (y : ℂ) * Complex.I) -
          H ((y : ℂ) * Complex.I)) Filter.atTop (nhds (0 : ℂ)) := by
  intro n a H G ha hG hH hstrip x
  have hdecay : Filter.Tendsto (fun t : ℝ => t ^ n * Real.exp (-a * t))
      Filter.atTop (nhds 0) := by
    simpa only [Real.rpow_natCast] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (n : ℝ) a ha
  have hweight : Filter.Tendsto (fun y : ℝ => (1 + y) ^ n * Real.exp (-a * y))
      Filter.atTop (nhds 0) := by
    convert (hdecay.comp (Filter.tendsto_atTop_add_const_left _ (1 : ℝ) Filter.tendsto_id)).mul_const
      (Real.exp a) using 1
    · ext y
      simp only [Function.comp_apply, id_eq, mul_assoc, ← Real.exp_add]
      congr 2
      ring
    · simp
  obtain ⟨C, Y, hC, hY, hbound⟩ := hstrip (|x| + 1) (by positivity)
  have hhorizontal (y : ℝ) (hy : Y ≤ y) :
      ‖H ((x : ℂ) + (y : ℂ) * Complex.I) - H ((y : ℂ) * Complex.I)‖ ≤
        |x| * C * ((1 + y) ^ n * Real.exp (-a * y)) := by
    have hypos : 0 < y := lt_of_lt_of_le (by linarith : 0 < Y) hy
    let z : ℝ → ℂ := fun s => (s : ℂ) * (x : ℂ) + (y : ℂ) * Complex.I
    have hzim (s : ℝ) : (z s).im = y := by simp [z]
    have hzcont : Continuous z :=
      (Complex.continuous_ofReal.mul continuous_const).add continuous_const
    have hderiv (s : ℝ) : HasDerivAt (fun t : ℝ => H (z t))
        (G (z s) * (x : ℂ)) s := by
      have hd := ((hasDerivAt_id (s : ℂ)).mul_const (x : ℂ)).add_const
        ((y : ℂ) * Complex.I)
      simpa only [Function.comp_apply, one_mul] using!
        ((hH (z s) (by rw [hzim]; exact hypos)).comp (s : ℂ) hd).comp_ofReal
    have hcont : ContinuousOn (fun s : ℝ => G (z s) * (x : ℂ)) (Set.uIcc 0 1) :=
      (hG.comp hzcont.continuousOn (by
        intro s _
        change 0 < (z s).im
        rw [hzim]
        exact hypos)).mul continuousOn_const
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s (_ : s ∈ Set.uIcc (0 : ℝ) 1) => hderiv s) hcont.intervalIntegrable
    have hnorm : ‖∫ s in (0 : ℝ)..1, G (z s) * (x : ℂ)‖ ≤
        |x| * C * ((1 + y) ^ n * Real.exp (-a * y)) := by
      have hb (s : ℝ) (hs : s ∈ Set.uIoc (0 : ℝ) 1) :
          ‖G (z s) * (x : ℂ)‖ ≤
            |x| * C * ((1 + y) ^ n * Real.exp (-a * y)) := by
        have hsIoc : 0 < s ∧ s ≤ 1 := by
          simpa only [Set.uIoc_of_le zero_le_one, Set.mem_Ioc] using hs
        have hs' : 0 ≤ s ∧ s ≤ 1 := ⟨hsIoc.1.le, hsIoc.2⟩
        have hzre : |(z s).re| ≤ |x| + 1 := by
          simp only [z, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
            Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
            sub_zero, add_zero, abs_mul, abs_of_nonneg hs'.1]
          nlinarith [abs_nonneg x]
        have hb := hbound (z s) hzre (by rwa [hzim])
        rw [hzim] at hb
        calc
          ‖G (z s) * (x : ℂ)‖ = ‖G (z s)‖ * |x| := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          _ ≤ (C * (1 + y) ^ n * Real.exp (-a * y)) * |x| :=
            mul_le_mul_of_nonneg_right hb (abs_nonneg x)
          _ = |x| * C * ((1 + y) ^ n * Real.exp (-a * y)) := by ring
      simpa using intervalIntegral.norm_integral_le_of_norm_le_const hb
    rw [hFTC] at hnorm
    simpa only [z, Complex.ofReal_one, Complex.ofReal_zero, one_mul, zero_mul,
      zero_add] using hnorm
  apply squeeze_zero_norm' (Filter.eventually_atTop.2 ⟨Y, hhorizontal⟩)
  simpa only [mul_zero] using hweight.const_mul (|x| * C)

theorem p02_es_177ebb5a_pcl_scalar_common_ray_limit :
    ∀ (n : ℕ) (a : ℝ) (H G : ℂ → ℂ), 0 < a →
      ContinuousOn G {z : ℂ | 0 < z.im} →
      (∀ z : ℂ, 0 < z.im → HasDerivAt H (G z) z) →
      (∀ B : ℝ, 0 < B → ∃ C Y : ℝ, 0 ≤ C ∧ 1 ≤ Y ∧
        ∀ z : ℂ, |z.re| ≤ B → Y ≤ z.im →
          ‖G z‖ ≤ C * (1 + z.im) ^ n * Real.exp (-a * z.im)) →
      ∃ A : ℂ, ∀ x : ℝ, Filter.Tendsto
        (fun y : ℝ => H ((x : ℂ) + (y : ℂ) * Complex.I))
        Filter.atTop (nhds A) := by
  intro n a H G ha hG hH hstrip
  obtain ⟨C, Y, hC, hY, hbound⟩ := hstrip 1 zero_lt_one
  have hray : ∀ t : ℝ, Y ≤ t →
      ‖G ((t : ℂ) * Complex.I)‖ ≤ C * (1 + t) ^ n * Real.exp (-a * t) := by
    intro t ht
    simpa using hbound ((t : ℂ) * Complex.I) (by simp) (by simpa using ht)
  obtain ⟨A, hA⟩ := p02_es_177ebb5a_crl_imaginary_ray_limit n a H G ha hG hH
    ⟨C, Y, hC, hY, hray⟩
  refine ⟨A, fun x => ?_⟩
  simpa only [sub_add_cancel, zero_add] using
    (p02_es_177ebb5a_crl_horizontal_difference_limit n a H G ha hG hH hstrip x).add hA
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


open scoped Pointwise in
theorem p02_es_177ebb5a_pp_primitive_cusp_limit :
    ∀ (N : ℕ) [NeZero N] (n : ℕ)
      (f : CuspForm (CongruenceSubgroup.Gamma0 N) ((n : ℤ) + 2))
      (F : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n)),
      HeckeEis.IsEichlerIntegral n (fun τ => f τ) F →
      ∀ σ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      ∃ A : ↥(HeckeEis.BinaryForm ℂ n), ∀ (x : ℝ) (d : Fin 2 →₀ ℕ),
        Filter.Tendsto (fun y : ℝ => MvPolynomial.coeff d
          (F (σ • UpperHalfPlane.ofComplex ((x : ℂ) + (y : ℂ) * Complex.I))).val)
          Filter.atTop (nhds (MvPolynomial.coeff d A.val)) := by
  classical
  intro N _ n f F hF σ
  -- Apply the pinned cusp-form estimate to the translate by σ.
  have hdecay : ∃ a C Y : ℝ, 0 < a ∧ 0 ≤ C ∧ ∀ τ : UpperHalfPlane,
      Y ≤ τ.im → ‖(HeckeEis.jFactor σ τ) ^ (-((n : ℤ) + 2)) * f (σ • τ)‖ ≤
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
    obtain ⟨a, ha, hbound⟩ := CuspFormClass.exp_decay_atImInfty' (CuspForm.translate f g)
    obtain ⟨C, hC, hbound⟩ := hbound.exists_nonneg
    obtain ⟨Y, hY⟩ := (UpperHalfPlane.atImInfty_mem _).mp hbound.bound
    refine ⟨a, C, Y, ha, hC, ?_⟩
    intro τ hτ
    have h := hY τ hτ
    change ‖((f : UpperHalfPlane → ℂ) ∣[(n : ℤ) + 2] σ) τ‖ ≤
      C * ‖Real.exp (-a * τ.im)‖ at h
    rw [HeckeEis.jFactor_eq_denom, mul_comm]
    simpa only [ModularForm.SL_slash_apply, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)] using! h
  obtain ⟨a, C, Y, ha, hC, hdecay⟩ := hdecay
  obtain ⟨K, hK, hgrowth⟩ := p02_es_177ebb5a_pcl_linear_linepow_growth n
    (HeckeEis.binaryFormRepSL ℂ n σ)
  let H (d : Fin 2 →₀ ℕ) (z : ℂ) :=
    MvPolynomial.coeff d (F (σ • UpperHalfPlane.ofComplex z)).val
  have hderiv (d : Fin 2 →₀ ℕ) (z : ℂ) (hz : 0 < z.im) :
      HasDerivAt (H d)
        ((HeckeEis.jFactor σ ⟨z, hz⟩) ^ (-((n : ℤ) + 2)) * f (σ • ⟨z, hz⟩) *
          MvPolynomial.coeff d ((HeckeEis.binaryFormRepSL ℂ n σ)
            (HeckeEis.linePow n z)).val) z :=
    p02_es_177ebb5a_pcl_scaled_pullback_derivative n _ F hF σ d ⟨z, hz⟩
  have hlimit (d : Fin 2 →₀ ℕ) : ∃ A : ℂ, ∀ x : ℝ,
      Filter.Tendsto (fun y : ℝ => H d ((x : ℂ) + (y : ℂ) * Complex.I))
        Filter.atTop (nhds A) := by
    have hhol : DifferentiableOn ℂ (H d) {z : ℂ | 0 < z.im} :=
      fun z hz => (hderiv d z hz).differentiableAt.differentiableWithinAt
    refine p02_es_177ebb5a_pcl_scalar_common_ray_limit n a (H d) (deriv (H d)) ha
      (hhol.deriv (isOpen_lt continuous_const Complex.continuous_im)).continuousOn
      (fun z hz => (hderiv d z hz).differentiableAt.hasDerivAt) ?_
    intro B hB
    refine ⟨C * K * (B + 2) ^ n, max 1 Y, by positivity, le_max_left _ _, ?_⟩
    intro z hzre hzim
    have hz1 : 1 ≤ z.im := (le_max_left _ _).trans hzim
    have hz : 0 < z.im := by linarith
    have hnorm : 1 + ‖z‖ ≤ (B + 2) * (1 + z.im) := by
      have hn := Complex.norm_le_abs_re_add_abs_im z
      rw [abs_of_pos hz] at hn
      nlinarith
    have hp : (1 + ‖z‖) ^ n ≤ (B + 2) ^ n * (1 + z.im) ^ n := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) hnorm n
    rw [(hderiv d z hz).deriv, norm_mul]
    calc
      _ ≤ (C * Real.exp (-a * z.im)) * (K * (1 + ‖z‖) ^ n) :=
        mul_le_mul (hdecay ⟨z, hz⟩ ((le_max_right _ _).trans hzim))
          (hgrowth z d) (norm_nonneg _) (by positivity)
      _ ≤ (C * Real.exp (-a * z.im)) *
          (K * ((B + 2) ^ n * (1 + z.im) ^ n)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp hK) (by positivity)
      _ = C * K * (B + 2) ^ n * (1 + z.im) ^ n * Real.exp (-a * z.im) := by ring
  choose A hA using hlimit
  -- Only degree-n coefficients can be nonzero; their index set is finite.
  let s := (Finsupp.finite_of_degree_eq (σ := Fin 2) n).toFinset
  have hs (d : Fin 2 →₀ ℕ) : d ∈ s ↔ d.degree = n := by simp [s]
  let P : MvPolynomial (Fin 2) ℂ := ∑ d ∈ s, MvPolynomial.monomial d (A d)
  have hP : P.IsHomogeneous n := by
    apply MvPolynomial.IsHomogeneous.sum
    intro d hd
    exact MvPolynomial.isHomogeneous_monomial _ ((hs d).mp hd)
  refine ⟨⟨P, hP⟩, ?_⟩
  intro x d
  by_cases hd : d ∈ s
  · have hc : MvPolynomial.coeff d P = A d := by
      simp [P, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, hd]
    change Filter.Tendsto (fun y : ℝ => H d ((x : ℂ) + (y : ℂ) * Complex.I))
      Filter.atTop (nhds (MvPolynomial.coeff d P))
    rw [hc]
    exact hA d x
  · have hdegree : d.degree ≠ n := fun h => hd ((hs d).mpr h)
    have hzero (τ : UpperHalfPlane) : MvPolynomial.coeff d (F τ).val = 0 :=
      MvPolynomial.IsHomogeneous.coeff_eq_zero (F τ).property hdegree
    simp only [hzero, MvPolynomial.IsHomogeneous.coeff_eq_zero hP hdegree]
    exact tendsto_const_nhds

end Submission
