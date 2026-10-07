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
theorem p02_es_177ebb5a_sm_slash :
    ∀ (n : ℕ) (E : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n))
      (σ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (τ : UpperHalfPlane),
      (SlashAction.map (-(n : ℤ)) σ (fun z : UpperHalfPlane =>
        MvPolynomial.eval (fun j : Fin 2 => if j = 0 then 1 else -(z : ℂ)) (E z).val)) τ =
      MvPolynomial.eval (fun j : Fin 2 => if j = 0 then 1 else -(τ : ℂ))
        (((HeckeEis.binaryFormRepSL ℂ n) σ⁻¹) (E (σ • τ))).val := by
  intro n E σ τ
  let R := HeckeEis.binaryFormRepSL ℂ n σ⁻¹ (E (σ • τ))
  let j : ℂ := UpperHalfPlane.denom σ τ
  have hj : j ≠ 0 := UpperHalfPlane.denom_ne_zero σ τ
  have hR : HeckeEis.binaryFormRepSL ℂ n σ R = E (σ • τ) := by
    change ((HeckeEis.binaryFormRepSL ℂ n σ) *
      (HeckeEis.binaryFormRepSL ℂ n σ⁻¹)) (E (σ • τ)) = _
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl
  have hdet : (σ 0 0 : ℂ) * (σ 1 1 : ℂ) - (σ 0 1 : ℂ) * (σ 1 0 : ℂ) = 1 := by
    exact_mod_cast (show σ 0 0 * σ 1 1 - σ 0 1 * σ 1 0 = 1 by
      simpa only [Matrix.det_fin_two] using σ.property)
  have hjdef : j = (σ 1 0 : ℂ) * (τ : ℂ) + (σ 1 1 : ℂ) := by
    simp [j, UpperHalfPlane.denom]
  have hw : ((σ • τ : UpperHalfPlane) : ℂ) =
      ((σ 0 0 : ℂ) * (τ : ℂ) + (σ 0 1 : ℂ)) / j := by
    simpa [hjdef] using UpperHalfPlane.coe_specialLinearGroup_apply σ τ
  have hcoords : (fun k : Fin 2 =>
      MvPolynomial.eval (fun i : Fin 2 => if i = 0 then 1 else -((σ • τ : UpperHalfPlane) : ℂ))
        (∑ i : Fin 2, MvPolynomial.C (σ i k : ℂ) * MvPolynomial.X i)) =
      j⁻¹ • (fun k : Fin 2 => if k = 0 then (1 : ℂ) else -(τ : ℂ)) := by
    rw [hw]
    funext k
    fin_cases k <;>
      simp [Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul] <;>
      field_simp [hj] <;> rw [hjdef]
    · linear_combination hdet
    · linear_combination -(τ : ℂ) * hdet
  have heval : MvPolynomial.eval
      (fun k : Fin 2 => if k = 0 then 1 else -((σ • τ : UpperHalfPlane) : ℂ))
      (E (σ • τ)).val = j⁻¹ ^ n *
      MvPolynomial.eval (fun k : Fin 2 => if k = 0 then 1 else -(τ : ℂ)) R.val := by
    rw [← hR, HeckeEis.binaryFormRepSL_apply_coe]
    change MvPolynomial.aeval _ (MvPolynomial.aeval _ R.val) = _
    rw [MvPolynomial.comp_aeval_apply]
    simp only [MvPolynomial.aeval_eq_eval]
    rw [hcoords, HeckeEis.eval_smul_of_isHomogeneous
      ((MvPolynomial.mem_homogeneousSubmodule _ _).mp R.property)]
  rw [ModularForm.SL_slash_apply, heval]
  simp only [neg_neg, zpow_natCast]
  change (j⁻¹ ^ n * _) * j ^ n = _
  rw [mul_right_comm, ← mul_pow, inv_mul_cancel₀ hj, one_pow, one_mul]

theorem p02_es_177ebb5a_sp_cayley_equivalence :
    (∀ w : ℂ, ‖w‖ < 1 → 0 < (Complex.I * (1 + w) / (1 - w)).im) ∧
    (∀ z : ℂ, 0 < z.im → ‖(z - Complex.I) / (z + Complex.I)‖ < 1) ∧
    (∀ z : ℂ, 0 < z.im →
      Complex.I * (1 + (z - Complex.I) / (z + Complex.I)) /
        (1 - (z - Complex.I) / (z + Complex.I)) = z) ∧
    (∀ w : ℂ, ‖w‖ < 1 →
      (Complex.I * (1 + w) / (1 - w) - Complex.I) /
        (Complex.I * (1 + w) / (1 - w) + Complex.I) = w) := by
  have disk_den (w : ℂ) (hw : ‖w‖ < 1) : 1 - w ≠ 0 := by
    intro h
    have : w = 1 := (sub_eq_zero.mp h).symm
    simp [this] at hw
  have half_plane_den (z : ℂ) (hz : 0 < z.im) : z + Complex.I ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp only [Complex.add_im, Complex.I_im, Complex.zero_im] at this
    linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro w hw
    have hsq : Complex.normSq w < 1 := by
      rw [Complex.normSq_eq_norm_sq, sq_lt_one_iff₀ (norm_nonneg w)]
      exact hw
    have hden := Complex.normSq_pos.mpr (disk_den w hw)
    rw [Complex.div_im, ← sub_div]
    apply div_pos _ hden
    simp only [Complex.mul_im, Complex.mul_re, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im, Complex.I_re, Complex.I_im,
      Complex.one_re, Complex.one_im, zero_mul, one_mul, zero_add, zero_sub]
    rw [Complex.normSq_apply] at hsq
    nlinarith
  · intro z hz
    rw [norm_div, div_lt_one (norm_pos_iff.mpr (half_plane_den z hz))]
    have hsq : Complex.normSq (z - Complex.I) < Complex.normSq (z + Complex.I) := by
      simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
        Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im, sub_zero, add_zero]
      nlinarith
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at hsq
    nlinarith [norm_nonneg (z - Complex.I), norm_nonneg (z + Complex.I)]
  · intro z hz
    have hs := half_plane_den z hz
    have hd : 1 - (z - Complex.I) / (z + Complex.I) ≠ 0 := by
      rw [sub_div' hs, div_ne_zero_iff]
      constructor
      · convert mul_ne_zero (two_ne_zero : (2 : ℂ) ≠ 0) Complex.I_ne_zero using 1
        ring
      · exact hs
    field_simp [hs, hd]
    ring
  · intro w hw
    have ht := disk_den w hw
    have hd : Complex.I * (1 + w) / (1 - w) + Complex.I ≠ 0 := by
      rw [div_add' _ _ _ ht, div_ne_zero_iff]
      constructor
      · convert mul_ne_zero (two_ne_zero : (2 : ℂ) ≠ 0) Complex.I_ne_zero using 1
        ring
      · exact ht
    field_simp [ht, hd]
    ring

theorem p02_es_177ebb5a_sp_cayley_derivatives :
    (∀ w : ℂ, ‖w‖ < 1 →
      HasDerivAt (fun u : ℂ => Complex.I * (1 + u) / (1 - u))
        (2 * Complex.I / (1 - w) ^ 2) w) ∧
    (∀ z : ℂ, 0 < z.im →
      HasDerivAt (fun u : ℂ => (u - Complex.I) / (u + Complex.I))
        (2 * Complex.I / (z + Complex.I) ^ 2) z) ∧
    (∀ z : ℂ, 0 < z.im →
      (2 * Complex.I / (1 - (z - Complex.I) / (z + Complex.I)) ^ 2) *
        (2 * Complex.I / (z + Complex.I) ^ 2) = 1) := by
  have hupper (z : ℂ) (hz : 0 < z.im) : z + Complex.I ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp only [Complex.add_im, Complex.I_im, Complex.zero_im] at hi
    linarith
  refine ⟨?_, ?_, ?_⟩
  · intro w hw
    have hden : 1 - w ≠ 0 := by
      intro h
      have hw1 : w = 1 := (sub_eq_zero.mp h).symm
      simp [hw1] at hw
    exact ((((hasDerivAt_id' w).const_add 1).const_mul Complex.I).fun_div
      ((hasDerivAt_id' w).const_sub 1) hden).congr_deriv (by ring)
  · intro z hz
    exact (((hasDerivAt_id' z).sub_const Complex.I).fun_div
      ((hasDerivAt_id' z).add_const Complex.I) (hupper z hz)).congr_deriv (by ring)
  · intro z hz
    have hden := hupper z hz
    have hchange : 1 - (z - Complex.I) / (z + Complex.I) =
        2 * Complex.I / (z + Complex.I) := by
      field_simp [hden]
      ring
    rw [hchange]
    field_simp [hden]

theorem p02_es_177ebb5a_sd_open_ladder :
    ∀ (U : Set ℂ) (n : ℕ) (Q : ℕ → ℂ → ℂ) (g : ℂ → ℂ), IsOpen U →
      (∀ (r : ℕ), r < n → ∀ z ∈ U, HasDerivAt (Q r) (-Q (r + 1) z) z) →
      (∀ z ∈ U, HasDerivAt (Q n) (g z) z) →
      ∀ z ∈ U, iteratedDeriv (n + 1) (Q 0) z = (-1 : ℂ) ^ n * g z := by
  intro U n Q g hU hQ hg
  have hiter : ∀ r ≤ n, ∀ z ∈ U,
      iteratedDeriv r (Q 0) z = (-1 : ℂ) ^ r * Q r z := by
    intro r
    induction r with
    | zero => intro _ z _; simp
    | succ r ih =>
      intro hr z hz
      have hrn : r < n := Nat.lt_of_succ_le hr
      have heq : iteratedDeriv r (Q 0) =ᶠ[nhds z]
          (fun w => (-1 : ℂ) ^ r * Q r w) :=
        Filter.eventually_of_mem (hU.mem_nhds hz)
          (fun w hw => ih (Nat.le_of_lt hrn) w hw)
      have hd := (hQ r hrn z hz).const_mul ((-1 : ℂ) ^ r)
      rw [iteratedDeriv_succ, (hd.congr_of_eventuallyEq heq).deriv]
      simp only [pow_succ, mul_neg, mul_one, neg_mul]
  intro z hz
  have heq : iteratedDeriv n (Q 0) =ᶠ[nhds z]
      (fun w => (-1 : ℂ) ^ n * Q n w) :=
    Filter.eventually_of_mem (hU.mem_nhds hz) (fun w hw => hiter n le_rfl w hw)
  rw [iteratedDeriv_succ]
  exact (((hg z hz).const_mul ((-1 : ℂ) ^ n)).congr_of_eventuallyEq heq).deriv

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

end Submission
