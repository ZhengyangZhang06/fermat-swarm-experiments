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

theorem p02_es_177ebb5a_pnf_primitive_eigenvector_triangular :
    ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (ε p q : ℤ),
      ε ^ 2 = 1 → IsCoprime p q →
      (γ : Matrix (Fin 2) (Fin 2) ℤ).mulVec ![p, q] = ![ε * p, ε * q] →
      ∃ (σ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (b : ℤ),
        (σ⁻¹ * γ * σ : Matrix.SpecialLinearGroup (Fin 2) ℤ).val =
          Matrix.of ![![ε, b], ![0, ε]] := by
  intro γ ε p q hε hpq hγ
  obtain ⟨σ, hσ₀, hσ₁⟩ := hpq.exists_SL2_col 0
  have hσ : σ.val.mulVec ![1, 0] = ![p, q] := by
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hσ₀, hσ₁]
  have heigen : γ.val.mulVec ![p, q] = ε • ![p, q] := by
    simpa using hγ
  let δ := σ⁻¹ * γ * σ
  have hδ : δ.val.mulVec ![1, 0] = ε • ![1, 0] := by
    change ((σ⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℤ).val * γ.val * σ.val).mulVec
      ![1, 0] = ε • ![1, 0]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hσ, heigen,
      Matrix.mulVec_smul, ← hσ, Matrix.mulVec_mulVec,
      ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
  have hδ₀ : δ.val 0 0 = ε := by
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun hδ 0
  have hδ₁ : δ.val 1 0 = 0 := by
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun hδ 1
  have hdet : ε * δ.val 1 1 = 1 := by
    simpa only [Matrix.det_fin_two, hδ₀, hδ₁, mul_zero, sub_zero] using δ.property
  have hdiag : δ.val 1 1 = ε := by
    calc
      δ.val 1 1 = ε ^ 2 * δ.val 1 1 := by rw [hε, one_mul]
      _ = ε * (ε * δ.val 1 1) := by rw [pow_two, mul_assoc]
      _ = ε := by rw [hdet, mul_one]
  refine ⟨σ, δ.val 0 1, ?_⟩
  change δ.val = Matrix.of ![![ε, δ.val 0 1], ![0, ε]]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hδ₀, hδ₁, hdiag]

/-- Coefficientwise derivative of an Eichler integral after a modular substitution. -/
theorem p02_es_177ebb5a_cd_modular_pullback_derivative
    (N : ℕ) [NeZero N] (n : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) ((n : ℤ) + 2))
    (F : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n))
    (hF : HeckeEis.IsEichlerIntegral n (fun τ => f τ) F)
    (γ : CongruenceSubgroup.Gamma0 N) (e : Fin 2 →₀ ℕ) (τ : UpperHalfPlane) :
    HasDerivAt
      (fun z : ℂ => MvPolynomial.coeff e
        (F ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) • UpperHalfPlane.ofComplex z)).val)
      (f τ * MvPolynomial.coeff e
        ((((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype) γ)
          (HeckeEis.linePow n (τ : ℂ))).val)
      (τ : ℂ) := by
  let g : Matrix.SpecialLinearGroup (Fin 2) ℤ := γ
  have hj := HeckeEis.jFactor_ne_zero g τ
  have hT : HasDerivAt
      (fun z : ℂ => ((g • UpperHalfPlane.ofComplex z : UpperHalfPlane) : ℂ))
      (1 / HeckeEis.jFactor g τ ^ 2) (τ : ℂ) := by
    have hdet : (Matrix.SpecialLinearGroup.mapGL ℝ g).val.det = 1 :=
      (g.map (algebraMap ℤ ℝ)).det_coe
    simpa only [MulAction.compHom_smul_def, hdet, Complex.ofReal_one,
      ← HeckeEis.jFactor_eq_denom] using
      (UpperHalfPlane.hasStrictDerivAt_smul
        (g := Matrix.SpecialLinearGroup.mapGL ℝ g) (by rw [hdet]; exact zero_lt_one) τ).hasDerivAt
  have hcomp := (hF e (g • τ)).comp_of_eq (τ : ℂ) hT (by
    simp only [UpperHalfPlane.ofComplex_apply])
  have hslash : f (g • τ) = HeckeEis.jFactor g τ ^ (n + 2) * f τ := by
    have h := SlashInvariantForm.slash_action_eqn_SL'' (Γ := CongruenceSubgroup.Gamma0 N)
      f (γ := g) γ.property τ
    change f (g • τ) = UpperHalfPlane.denom (Matrix.SpecialLinearGroup.mapGL ℝ g)
      (τ : ℂ) ^ ((n : ℤ) + 2) * f τ at h
    rw [← HeckeEis.jFactor_eq_denom] at h
    simpa only [show (n : ℤ) + 2 = ((n + 2 : ℕ) : ℤ) by simp, zpow_natCast] using h
  have hrep : MvPolynomial.coeff e
      ((((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype) γ)
        (HeckeEis.linePow n (τ : ℂ))).val =
      HeckeEis.jFactor g τ ^ n *
        MvPolynomial.coeff e (HeckeEis.linePow n ((g • τ : UpperHalfPlane) : ℂ)).val := by
    change MvPolynomial.coeff e ((HeckeEis.binaryFormRepSL ℂ n g)
      (HeckeEis.linePow n (τ : ℂ))).val = _
    rw [HeckeEis.binaryFormRepSL_linePow]
    simp only [Submodule.coe_smul, MvPolynomial.coeff_smul, smul_eq_mul]
  simp only [Function.comp_def, UpperHalfPlane.ofComplex_apply] at hcomp
  convert! hcomp using 1
  rw [hslash, hrep, pow_add]
  field_simp [hj]

theorem p02_es_177ebb5a_ic_inverse_linepow
    (n : ℕ) (σ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (τ : UpperHalfPlane) :
    (HeckeEis.binaryFormRepSL ℂ n) σ⁻¹
        (HeckeEis.linePow n ((σ • τ : UpperHalfPlane) : ℂ)) =
      ((HeckeEis.jFactor σ τ) ^ n)⁻¹ • HeckeEis.linePow n (τ : ℂ) := by
  have h := congrArg ((HeckeEis.binaryFormRepSL ℂ n) σ⁻¹)
    (HeckeEis.binaryFormRepSL_linePow n σ τ)
  rw [Representation.inv_self_apply, map_smul] at h
  have hj := pow_ne_zero n (HeckeEis.jFactor_ne_zero σ τ)
  simpa only [smul_smul, inv_mul_cancel₀ hj, one_smul] using
    congrArg (fun v => ((HeckeEis.jFactor σ τ) ^ n)⁻¹ • v) h.symm

/-- A bound on one period strip gives a uniform bound for sufficiently large imaginary part. -/
theorem p02_es_177ebb5a_tb_periodic_strip_bound
    (N : ℕ) [NeZero N] (q : UpperHalfPlane → ℂ)
    (hperiod : ∀ τ : UpperHalfPlane, q ((ModularGroup.T ^ N) • τ) = q τ)
    (hstrip : ∃ M Y : ℝ, ∀ τ : UpperHalfPlane,
      0 ≤ τ.re → τ.re ≤ (N : ℝ) → Y ≤ τ.im → ‖q τ‖ ≤ M) :
    UpperHalfPlane.IsBoundedAtImInfty q := by
  obtain ⟨M, Y, hstrip⟩ := hstrip
  have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  apply UpperHalfPlane.isBoundedAtImInfty_iff.mpr
  refine ⟨M, Y, ?_⟩
  intro τ hτ
  have hper : Function.Periodic (fun x : ℝ => q (x +ᵥ τ)) (N : ℝ) := by
    intro x
    simpa only [← zpow_natCast, UpperHalfPlane.modular_T_zpow_smul,
      Int.cast_natCast, ← add_vadd, add_comm] using hperiod (x +ᵥ τ)
  let m : ℤ := ⌊τ.re / (N : ℝ)⌋
  let τ' : UpperHalfPlane := (-(m : ℝ) * (N : ℝ)) +ᵥ τ
  have hre : τ'.re = τ.re - (m : ℝ) * N := by
    simp only [τ', UpperHalfPlane.vadd_re, neg_mul, sub_eq_add_neg, add_comm]
  have hq : q τ' = q τ := by
    simpa only [τ', Int.cast_neg, zero_vadd] using hper.int_mul_eq (-m)
  rw [← hq]
  apply hstrip τ'
  · rw [hre]
    exact Int.sub_floor_div_mul_nonneg τ.re hN
  · rw [hre]
    exact (Int.sub_floor_div_mul_lt τ.re hN).le
  · simpa only [τ', UpperHalfPlane.vadd_im] using hτ

theorem p02_es_177ebb5a_pnf_primitive_kernel :
    ∀ M : Matrix (Fin 2) (Fin 2) ℤ, M.det = 0 →
      ∃ p q : ℤ, IsCoprime p q ∧ M.mulVec ![p, q] = 0 := by
  intro M hdet
  by_cases hM : M = 0
  · subst M
    exact ⟨1, 0, ⟨1, 0, by norm_num⟩, by simp⟩
  rw [Matrix.det_fin_two] at hdet
  -- A vector perpendicular to a nonzero row lies in the kernel when the determinant vanishes.
  obtain ⟨x, y, hxy, hker⟩ :
      ∃ x y : ℤ, (x ≠ 0 ∨ y ≠ 0) ∧
        ∀ i : Fin 2, M i 0 * x + M i 1 * y = 0 := by
    by_cases hrow : M 0 0 = 0 ∧ M 0 1 = 0
    · refine ⟨M 1 1, -M 1 0, ?_, ?_⟩
      · by_contra! h
        apply hM
        ext i j
        fin_cases i <;> fin_cases j <;> simp_all
      · intro i
        fin_cases i
        · simp [hrow.1, hrow.2]
        · change M 1 0 * M 1 1 + M 1 1 * (-M 1 0) = 0
          ring
    · refine ⟨M 0 1, -M 0 0, ?_, ?_⟩
      · simpa only [not_and_or, neg_ne_zero, or_comm] using hrow
      · intro i
        fin_cases i
        · change M 0 0 * M 0 1 + M 0 1 * (-M 0 0) = 0
          ring
        · change M 1 0 * M 0 1 + M 1 1 * (-M 0 0) = 0
          nlinarith [hdet]
  -- Dividing by the positive gcd gives coprime coordinates; cancel it in the kernel equations.
  have hg : 0 < Int.gcd x y := Int.gcd_pos_iff.mpr hxy
  obtain ⟨p, q, hpq, hx, hy⟩ := Int.exists_gcd_one hg
  refine ⟨p, q, Int.isCoprime_iff_gcd_eq_one.mpr hpq, ?_⟩
  have hg' : (Int.gcd x y : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hg)
  ext i
  simp only [Matrix.mulVec_apply_eq_sum, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Pi.zero_apply]
  apply (mul_eq_zero_iff_right hg').mp
  calc
    (M i 0 * p + M i 1 * q) * (Int.gcd x y : ℤ) =
        M i 0 * (p * (Int.gcd x y : ℤ)) + M i 1 * (q * (Int.gcd x y : ℤ)) := by
          rw [add_mul, mul_assoc, mul_assoc]
    _ = 0 := by rw [← hx, ← hy]; exact hker i

theorem p02_es_177ebb5a_sd_jr_homogeneous_nilpotence
    (n : ℕ) (P : ↥(HeckeEis.BinaryForm ℂ n)) :
    ((fun p : MvPolynomial (Fin 2) ℂ => MvPolynomial.pderiv (1 : Fin 2) p)^[n + 1]
      P.val) = 0 := by
  classical
  let D : Module.End ℂ (MvPolynomial (Fin 2) ℂ) :=
    (MvPolynomial.pderiv (1 : Fin 2)).toLinearMap
  have hmon (k : ℕ) (d : Fin 2 →₀ ℕ) (a : ℂ) (hd : d 1 < k) :
      (D ^ k) (MvPolynomial.monomial d a) = 0 := by
    induction k generalizing d a with
    | zero => omega
    | succ k ih =>
      rw [pow_succ, Module.End.mul_apply]
      change (D ^ k) (MvPolynomial.pderiv 1 (MvPolynomial.monomial d a)) = 0
      rw [MvPolynomial.pderiv_monomial]
      by_cases hzero : d 1 = 0
      · simp [hzero]
      · apply ih
        simp only [Finsupp.tsub_apply, Finsupp.single_eq_same]
        omega
  change (D : MvPolynomial (Fin 2) ℂ → MvPolynomial (Fin 2) ℂ)^[n + 1] P.val = 0
  rw [← Module.End.pow_apply, ← P.val.support_sum_monomial_coeff, map_sum]
  apply Finset.sum_eq_zero
  intro d hd
  apply hmon
  have hdegree : d.degree = n := by
    simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using
      P.property (MvPolynomial.mem_support_iff.mp hd)
  exact lt_of_le_of_lt ((Finsupp.le_degree 1 d).trans_eq hdegree) (Nat.lt_succ_self n)

/-- A coefficient bound controls evaluation of a homogeneous binary form at `(1, -z)`. -/
theorem p02_es_177ebb5a_tb_eval_bound
    (n : ℕ) (R : ↥(HeckeEis.BinaryForm ℂ n)) (z : ℂ) (b : ℝ)
    (hb : 0 ≤ b)
    (hcoeff : ∀ d : Fin 2 →₀ ℕ, ‖MvPolynomial.coeff d R.val‖ ≤ b) :
    ‖MvPolynomial.eval (fun j : Fin 2 => if j = 0 then 1 else -z) R.val‖ ≤
      ((n + 1 : ℕ) : ℝ) * (max 1 ‖z‖) ^ n * b := by
  classical
  have hdeg (d : Fin 2 →₀ ℕ) (hd : d ∈ R.val.support) : d 0 + d 1 = n := by
    simpa only [Finsupp.weight_eq_sum, Fin.sum_univ_two, Pi.one_apply,
      smul_eq_mul, mul_one] using R.property (MvPolynomial.mem_support_iff.mp hd)
  have hcard : R.val.support.card ≤ n + 1 := by
    calc
      R.val.support.card ≤ (Finset.range (n + 1)).card := by
        apply Finset.card_le_card_of_injOn (fun d : Fin 2 →₀ ℕ => d 1)
        · intro d hd
          have := hdeg d hd
          exact Finset.mem_range.mpr (by change d 1 < n + 1; omega)
        · intro d hd e he hde
          change d 1 = e 1 at hde
          have hddeg := hdeg d hd
          have hedeg := hdeg e he
          ext j
          fin_cases j
          · change d 0 = e 0
            omega
          · exact hde
      _ = n + 1 := Finset.card_range _
  have hterm (d : Fin 2 →₀ ℕ) (hd : d ∈ R.val.support) :
      ‖MvPolynomial.coeff d R.val * (-z) ^ d 1‖ ≤ b * (max 1 ‖z‖) ^ n := by
    have hpow : ‖z‖ ^ d 1 ≤ (max 1 ‖z‖) ^ n := by
      calc
        ‖z‖ ^ d 1 ≤ (max 1 ‖z‖) ^ d 1 :=
          pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) _
        _ ≤ (max 1 ‖z‖) ^ n :=
          pow_le_pow_right₀ (le_max_left _ _) (by have := hdeg d hd; omega)
    simpa only [norm_mul, norm_pow, norm_neg] using
      mul_le_mul (hcoeff d) hpow (pow_nonneg (norm_nonneg _) _) hb
  rw [MvPolynomial.eval_eq']
  simp only [Fin.prod_univ_two, Fin.isValue, ite_true, one_pow, one_ne_zero,
    ite_false, one_mul]
  calc
    ‖∑ d ∈ R.val.support, MvPolynomial.coeff d R.val * (-z) ^ d 1‖ ≤
        ∑ d ∈ R.val.support, ‖MvPolynomial.coeff d R.val * (-z) ^ d 1‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _d ∈ R.val.support, b * (max 1 ‖z‖) ^ n := Finset.sum_le_sum hterm
    _ = (R.val.support.card : ℝ) * (b * (max 1 ‖z‖) ^ n) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((n + 1 : ℕ) : ℝ) * (b * (max 1 ‖z‖) ^ n) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcard)
        (mul_nonneg hb (pow_nonneg (le_trans (norm_nonneg _) (le_max_right _ _)) _))
    _ = ((n + 1 : ℕ) : ℝ) * (max 1 ‖z‖) ^ n * b := by ring

/-- A uniform coefficient bound for the homogeneous power `(z * X₀ + X₁) ^ n`. -/
theorem p02_es_177ebb5a_scl_linepow_coeff_bound :
    ∀ (n : ℕ) (z : ℂ) (d : Fin 2 →₀ ℕ),
      ‖MvPolynomial.coeff d (HeckeEis.linePow n z).val‖ ≤
        (2 : ℝ) ^ n * (max 1 ‖z‖) ^ n := by
  classical
  intro n z d
  have hsum : d.sum (fun _ m ↦ m) = d 0 + d 1 := by
    simp [Finsupp.sum_of_support_subset d (Finset.subset_univ d.support)]
  have hprod : d.prod (fun j m ↦ (if j = 0 then z else (1 : ℂ)) ^ m) =
      z ^ d 0 := by
    rw [d.prod_fintype _ (by simp)]
    simp
  have hmulti : d.multinomial = (d 0 + d 1).choose (d 0) := by
    rw [Finsupp.multinomial_eq_of_support_subset (Finset.subset_univ d.support),
      Finset.univ_fin2, Nat.binomial_eq_choose Fin.zero_ne_one]
  have hcoeff : MvPolynomial.coeff d (HeckeEis.linePow n z).val =
      if d 0 + d 1 = n then (n.choose (d 0) : ℂ) * z ^ d 0 else 0 := by
    have h := MvPolynomial.coeff_linearCombination_X_pow_of_fintype
      (fun j : Fin 2 ↦ if j = 0 then z else (1 : ℂ)) d n
    simp only [Fin.sum_univ_two, Fin.isValue, ite_true, one_ne_zero, ite_false,
      MvPolynomial.smul_eq_C_mul, map_one, one_mul] at h
    change MvPolynomial.coeff d
      ((MvPolynomial.C z * MvPolynomial.X 0 + MvPolynomial.X 1) ^ n) = _
    rw [h, hsum, hprod, hmulti]
    split_ifs with hd
    · rw [hd]
    · rfl
  rw [hcoeff]
  by_cases hd : d 0 + d 1 = n
  · rw [if_pos hd, norm_mul, Complex.norm_natCast, norm_pow]
    have hchoose : (n.choose (d 0) : ℝ) ≤ (2 : ℝ) ^ n := by
      exact_mod_cast Nat.choose_le_two_pow n (d 0)
    have hpow : ‖z‖ ^ d 0 ≤ (max 1 ‖z‖) ^ n := by
      exact (pow_le_pow_left₀ (norm_nonneg z) (le_max_right 1 ‖z‖) (d 0)).trans
        (pow_le_pow_right₀ (le_max_left 1 ‖z‖) (by omega))
    exact mul_le_mul hchoose hpow (pow_nonneg (norm_nonneg z) _) (by positivity)
  · rw [if_neg hd, norm_zero]
    positivity
/-- Pull back to the unit disk, apply `DifferentiableOn.isExactOn_ball` from
`Mathlib.Analysis.Complex.HasPrimitives`, and transport the primitive back by the Cayley map. -/
theorem p02_es_177ebb5a_primitive_exists_scalar_primitive :
    ∀ (a : ℂ → ℂ), DifferentiableOn ℂ a {z : ℂ | 0 < z.im} →
      ∃ A : ℂ → ℂ, ∀ z : ℂ, 0 < z.im → HasDerivAt A (a z) z := by
  intro a ha
  let φ := fun w : ℂ => Complex.I * (1 + w) / (1 - w)
  let ψ := fun z : ℂ => (z - Complex.I) / (z + Complex.I)
  obtain ⟨hφ, hψ, hφψ, _⟩ := p02_es_177ebb5a_sp_cayley_equivalence
  obtain ⟨hdφ, hdψ, hprod⟩ := p02_es_177ebb5a_sp_cayley_derivatives
  have hopen : IsOpen {z : ℂ | 0 < z.im} :=
    isOpen_lt continuous_const Complex.continuous_im
  have hb : DifferentiableOn ℂ
      (fun w => a (φ w) * (2 * Complex.I / (1 - w) ^ 2))
      (Metric.ball (0 : ℂ) 1) := by
    intro w hw
    have hw' : ‖w‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hw
    have hden : 1 - w ≠ 0 := by
      intro h
      have hw1 : w = 1 := (sub_eq_zero.mp h).symm
      simp [hw1] at hw'
    exact (((ha.differentiableAt (hopen.mem_nhds (hφ w hw'))).comp w
      (hdφ w hw').differentiableAt).mul
        ((differentiableAt_const (2 * Complex.I)).div
          ((differentiableAt_id.const_sub 1).pow 2)
          (pow_ne_zero 2 hden))).differentiableWithinAt
  obtain ⟨B, hB⟩ := hb.isExactOn_ball
  refine ⟨fun z => B (ψ z), ?_⟩
  intro z hz
  have hw : ψ z ∈ Metric.ball (0 : ℂ) 1 := by
    simpa only [Metric.mem_ball, dist_zero_right] using hψ z hz
  convert! (hB (ψ z) hw).comp z (hdψ z hz) using 1
  simp only [φ, ψ, hφψ z hz, mul_assoc, hprod z hz, mul_one]

/-- Expand a homogeneous binary form in the monomials with exponents `(r, n - r)`. -/
theorem p02_es_177ebb5a_ic_lct_monomial_expansion
    (n : ℕ) (Q : ↥(HeckeEis.BinaryForm ℂ n)) :
    Q.val = ∑ r : Fin (n + 1),
      MvPolynomial.coeff (Finsupp.single (0 : Fin 2) r.val +
        Finsupp.single (1 : Fin 2) (n - r.val)) Q.val •
      MvPolynomial.monomial (Finsupp.single (0 : Fin 2) r.val +
        Finsupp.single (1 : Fin 2) (n - r.val)) (1 : ℂ) := by
  classical
  let exponent (r : Fin (n + 1)) : Fin 2 →₀ ℕ :=
    Finsupp.single 0 r.val + Finsupp.single 1 (n - r.val)
  have hdegree (r : Fin (n + 1)) : (exponent r).degree = n := by
    simp only [exponent, map_add, Finsupp.degree_single]
    exact Nat.add_sub_of_le (Nat.le_of_lt_succ r.isLt)
  apply MvPolynomial.ext
  intro d
  rw [MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_smul, MvPolynomial.coeff_monomial, smul_eq_mul]
  change MvPolynomial.coeff d Q.val = ∑ r : Fin (n + 1),
    MvPolynomial.coeff (exponent r) Q.val * (if exponent r = d then 1 else 0)
  by_cases hd : d.degree = n
  · have hd01 : d 0 + d 1 = n := by
      simpa only [Finsupp.degree_eq_sum, Fin.sum_univ_two] using hd
    let r₀ : Fin (n + 1) := ⟨d 0, by omega⟩
    have hr₀ : exponent r₀ = d := by
      ext i
      fin_cases i <;> simp [exponent, r₀]
      omega
    rw [Finset.sum_eq_single r₀]
    · simp [hr₀]
    · intro r _ hne
      have hrd : exponent r ≠ d := by
        intro h
        apply hne
        apply Fin.ext
        have h0 := congrArg (fun e : Fin 2 →₀ ℕ => e 0) h
        simpa [exponent, r₀] using h0
      simp [hrd]
    · simp
  · have hQ : MvPolynomial.coeff d Q.val = 0 :=
      MvPolynomial.IsHomogeneous.coeff_eq_zero Q.property hd
    rw [hQ]
    symm
    apply Finset.sum_eq_zero
    intro r _
    have hrd : exponent r ≠ d := by
      intro h
      exact hd (h ▸ hdegree r)
    simp [hrd]

theorem p02_es_177ebb5a_ic_lmd_scalar_pullback
    (h : UpperHalfPlane → ℂ) (v : ℂ)
    (σ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (τ : UpperHalfPlane)
    (hh : HasDerivAt (fun z : ℂ => h (UpperHalfPlane.ofComplex z)) v
      ((σ • τ : UpperHalfPlane) : ℂ)) :
    HasDerivAt (fun z : ℂ => h (σ • UpperHalfPlane.ofComplex z))
      (v / (HeckeEis.jFactor σ τ) ^ 2) (τ : ℂ) := by
  have hdet : (Matrix.SpecialLinearGroup.mapGL ℝ σ).val.det = 1 :=
    (Matrix.SpecialLinearGroup.map (algebraMap ℤ ℝ) σ).property
  have hσ : HasDerivAt
      (fun z : ℂ => ((σ • UpperHalfPlane.ofComplex z : UpperHalfPlane) : ℂ))
      (1 / (HeckeEis.jFactor σ τ) ^ 2) (τ : ℂ) := by
    simpa only [hdet, Complex.ofReal_one, ← HeckeEis.jFactor_eq_denom] using!
      (UpperHalfPlane.hasStrictDerivAt_smul
        (g := Matrix.SpecialLinearGroup.mapGL ℝ σ) (by rw [hdet]; exact zero_lt_one) τ).hasDerivAt
  simpa only [Function.comp_def, UpperHalfPlane.ofComplex_apply, mul_one_div] using
    hh.comp_of_eq (τ : ℂ) hσ (by simp only [UpperHalfPlane.ofComplex_apply])

theorem p02_es_177ebb5a_sd_jr_linepow_eval :
    ∀ (n r : ℕ), r ≤ n → ∀ t : ℂ,
      MvPolynomial.eval (fun j : Fin 2 => if j = 0 then 1 else -t)
        ((fun p : MvPolynomial (Fin 2) ℂ => MvPolynomial.pderiv (1 : Fin 2) p)^[r]
          (HeckeEis.linePow n t).val) =
        (if r = n then (Nat.factorial n : ℂ) else 0) := by
  intro n r hr t
  let L : MvPolynomial (Fin 2) ℂ := MvPolynomial.C t * MvPolynomial.X 0 +
    MvPolynomial.X 1
  have hD : MvPolynomial.pderiv (1 : Fin 2) L = 1 := by
    simp [L]
  -- Each derivative lowers the power and contributes the next descending factor.
  have hiter (s : ℕ) (hs : s ≤ n) :
      (fun p : MvPolynomial (Fin 2) ℂ => MvPolynomial.pderiv (1 : Fin 2) p)^[s]
        (L ^ n) = MvPolynomial.C (n.descFactorial s : ℂ) * L ^ (n - s) := by
    induction s with
    | zero => simp
    | succ s ih =>
      rw [Function.iterate_succ_apply', ih (by omega), MvPolynomial.pderiv_C_mul,
        MvPolynomial.pderiv_pow, hD, mul_one]
      simp only [Nat.descFactorial_succ, Nat.cast_mul, map_mul, map_natCast,
        Nat.sub_sub]
      ac_rfl
  have hEval : MvPolynomial.eval (fun j : Fin 2 => if j = 0 then 1 else -t) L = 0 := by
    simp [L]
  change MvPolynomial.eval _
    ((fun p : MvPolynomial (Fin 2) ℂ => MvPolynomial.pderiv (1 : Fin 2) p)^[r]
      (L ^ n)) = _
  rw [hiter r hr, map_mul, MvPolynomial.eval_C, map_pow, hEval]
  by_cases h : r = n
  · subst r
    simp [Nat.descFactorial_self]
  · have hnr : n - r ≠ 0 := by omega
    simp [h, zero_pow hnr]

end Submission

theorem Submission.p02_es_177ebb5a_hi_prescribed_coefficients :
    ∀ (n : ℕ) (a : ℕ → ℂ), ∃ P : ↥(HeckeEis.BinaryForm ℂ n),
      ∀ d : Fin 2 →₀ ℕ, MvPolynomial.coeff d P.val =
        if d 0 + d 1 = n then a (d 0) else 0 := by
  classical
  intro n a
  let e (r : Fin (n + 1)) : Fin 2 →₀ ℕ :=
    Finsupp.single 0 r.val + Finsupp.single 1 (n - r.val)
  have he (r : Fin (n + 1)) : (e r).degree = n := by
    simp only [e, map_add, Finsupp.degree_single]
    exact Nat.add_sub_of_le (Nat.le_of_lt_succ r.isLt)
  let p : MvPolynomial (Fin 2) ℂ := ∑ r : Fin (n + 1),
    MvPolynomial.monomial (e r) (a r.val)
  have hp : p.IsHomogeneous n :=
    MvPolynomial.IsHomogeneous.sum _ _ _ fun r _ =>
      MvPolynomial.isHomogeneous_monomial _ (he r)
  refine ⟨⟨p, hp⟩, ?_⟩
  intro d
  change MvPolynomial.coeff d p = _
  simp only [p, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
  by_cases hd : d 0 + d 1 = n
  · rw [if_pos hd]
    let r₀ : Fin (n + 1) := ⟨d 0, by omega⟩
    have hr₀ : e r₀ = d := by
      ext i
      fin_cases i <;> simp [e, r₀, ← hd]
    rw [Finset.sum_eq_single r₀]
    · simp [hr₀, r₀]
    · intro r _ hne
      have hrd : e r ≠ d := by
        intro h
        apply hne
        apply Fin.ext
        have h0 := congrArg (fun t : Fin 2 →₀ ℕ => t 0) h
        simpa [e, r₀] using h0
      simp [hrd]
    · simp
  · rw [if_neg hd]
    apply Finset.sum_eq_zero
    intro r _
    have hrd : e r ≠ d := by
      intro h
      apply hd
      have hdegree : d.degree = n := h ▸ he r
      simpa only [Finsupp.degree_eq_sum, Fin.sum_univ_two] using hdegree
    simp [hrd]
theorem Submission.p02_es_177ebb5a_hi_linepow_coefficients :
    ∀ (n : ℕ) (z : ℂ) (d : Fin 2 →₀ ℕ),
      MvPolynomial.coeff d (HeckeEis.linePow n z).val =
        if d 0 + d 1 = n then (Nat.choose n (d 0) : ℂ) * z ^ (d 0) else 0 := by
  classical
  intro n z d
  have hsum : d.sum (fun _ m ↦ m) = d 0 + d 1 := by
    simp [Finsupp.sum_of_support_subset d (Finset.subset_univ d.support)]
  have hprod : d.prod (fun j m ↦ (if j = 0 then z else (1 : ℂ)) ^ m) =
      z ^ d 0 := by
    rw [d.prod_fintype _ (by simp)]
    simp
  have hmulti : d.multinomial = (d 0 + d 1).choose (d 0) := by
    rw [Finsupp.multinomial_eq_of_support_subset (Finset.subset_univ d.support),
      Finset.univ_fin2, Nat.binomial_eq_choose Fin.zero_ne_one]
  have h := MvPolynomial.coeff_linearCombination_X_pow_of_fintype
    (fun j : Fin 2 ↦ if j = 0 then z else (1 : ℂ)) d n
  simp only [Fin.sum_univ_two, Fin.isValue, ite_true, one_ne_zero, ite_false,
    MvPolynomial.smul_eq_C_mul, map_one, one_mul] at h
  change MvPolynomial.coeff d
    ((MvPolynomial.C z * MvPolynomial.X 0 + MvPolynomial.X 1) ^ n) = _
  rw [h, hsum, hprod, hmulti]
  split_ifs with hd
  · rw [hd]
  · rfl

namespace Submission

/-- Assemble scalar holomorphic primitives into a coefficientwise Eichler integral. -/
theorem p02_es_177ebb5a_primitive_exists_holomorphic_integral :
    ∀ (n : ℕ) (h : UpperHalfPlane → ℂ),
      DifferentiableOn ℂ (fun z : ℂ => h (UpperHalfPlane.ofComplex z))
        {z : ℂ | 0 < z.im} →
      ∃ F : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n),
        HeckeEis.IsEichlerIntegral n h F := by
  classical
  intro n h hh
  have hprimitives (r : ℕ) : ∃ A : ℂ → ℂ, ∀ z : ℂ, 0 < z.im →
      HasDerivAt A ((n.choose r : ℂ) * h (UpperHalfPlane.ofComplex z) * z ^ r) z :=
    p02_es_177ebb5a_primitive_exists_scalar_primitive _
      ((hh.const_mul (n.choose r : ℂ)).mul (differentiableOn_id.pow r))
  choose A hA using hprimitives
  choose F hF using fun τ : UpperHalfPlane =>
    p02_es_177ebb5a_hi_prescribed_coefficients n (fun r => A r (τ : ℂ))
  refine ⟨F, ?_⟩
  intro d τ
  change HasDerivAt (fun z : ℂ => MvPolynomial.coeff d (F (UpperHalfPlane.ofComplex z)).val)
    (h τ * MvPolynomial.coeff d (HeckeEis.linePow n (τ : ℂ)).val) (τ : ℂ)
  simp_rw [hF, p02_es_177ebb5a_hi_linepow_coefficients]
  by_cases hd : d 0 + d 1 = n
  · simp only [if_pos hd]
    have heq : (fun z : ℂ => A (d 0) (UpperHalfPlane.ofComplex z : ℂ)) =ᶠ[nhds (τ : ℂ)]
        A (d 0) :=
      (UpperHalfPlane.eventuallyEq_coe_comp_ofComplex τ.im_pos).fun_comp (A (d 0))
    have hderiv := (hA (d 0) (τ : ℂ) τ.im_pos).congr_of_eventuallyEq heq
    simpa only [UpperHalfPlane.ofComplex_apply, mul_left_comm, mul_assoc] using hderiv
  · simp only [if_neg hd, mul_zero]
    exact hasDerivAt_const (τ : ℂ) (0 : ℂ)
theorem p02_es_177ebb5a_lcd_coeff_linear_combination
    (n : ℕ)
    (A : ↥(HeckeEis.BinaryForm ℂ n) →ₗ[ℂ] ↥(HeckeEis.BinaryForm ℂ n))
    (e : Fin 2 →₀ ℕ) :
    ∃ c : Fin (n + 1) → ℂ, ∀ Q : ↥(HeckeEis.BinaryForm ℂ n),
      MvPolynomial.coeff e (A Q).val = ∑ r : Fin (n + 1),
        c r * MvPolynomial.coeff
          (Finsupp.single (0 : Fin 2) r.val + Finsupp.single (1 : Fin 2) (n - r.val))
          Q.val := by
  classical
  let d (r : Fin (n + 1)) : Fin 2 →₀ ℕ :=
    Finsupp.single 0 r.val + Finsupp.single 1 (n - r.val)
  have hd (r : Fin (n + 1)) : (d r).degree = n := by
    simp [d, Finsupp.degree_eq_sum, Fin.sum_univ_two,
      Nat.add_sub_of_le (Nat.le_of_lt_succ r.isLt)]
  let b (r : Fin (n + 1)) : ↥(HeckeEis.BinaryForm ℂ n) :=
    ⟨MvPolynomial.monomial (d r) 1, MvPolynomial.isHomogeneous_monomial 1 (hd r)⟩
  refine ⟨fun r => MvPolynomial.coeff e (A (b r)).val, ?_⟩
  intro Q
  have hexpand : Q = ∑ r, MvPolynomial.coeff (d r) Q.val • b r := by
    apply Subtype.ext
    simp only [Submodule.coe_sum, Submodule.coe_smul]
    apply MvPolynomial.ext
    intro t
    simp only [b, MvPolynomial.coeff_sum, MvPolynomial.coeff_smul,
      MvPolynomial.coeff_monomial]
    by_cases ht : t.degree = n
    · have hsum : t 0 + t 1 = n := by
        simpa [Finsupp.degree_eq_sum, Fin.sum_univ_two] using ht
      let r : Fin (n + 1) := ⟨t 0, by omega⟩
      have hr : d r = t := by
        ext i
        fin_cases i <;> simp [d, r, ← hsum]
      have huniq (s : Fin (n + 1)) (hs : d s = t) : s = r := by
        apply Fin.ext
        have hzero := congrArg (fun u : Fin 2 →₀ ℕ => u 0) hs
        simpa [d, r] using hzero
      rw [Finset.sum_eq_single r]
      · simp [hr]
      · intro s _ hs
        have hne : d s ≠ t := fun h => hs (huniq s h)
        simp [hne]
      · simp
    · rw [MvPolynomial.IsHomogeneous.coeff_eq_zero Q.property ht]
      symm
      apply Finset.sum_eq_zero
      intro r _
      have hne : d r ≠ t := fun h => ht (h ▸ hd r)
      simp [hne]
  calc
    MvPolynomial.coeff e (A Q).val =
        MvPolynomial.coeff e (A (∑ r, MvPolynomial.coeff (d r) Q.val • b r)).val :=
      congrArg (fun P => MvPolynomial.coeff e (A P).val) hexpand
    _ = ∑ r, MvPolynomial.coeff e (A (b r)).val * MvPolynomial.coeff (d r) Q.val := by
      simp [map_sum, MvPolynomial.coeff_sum, mul_comm]

theorem p02_es_177ebb5a_cd_linear_coeff_derivative
    (n : ℕ)
    (A : ↥(HeckeEis.BinaryForm ℂ n) →ₗ[ℂ] ↥(HeckeEis.BinaryForm ℂ n))
    (F : ℂ → ↥(HeckeEis.BinaryForm ℂ n))
    (P : ↥(HeckeEis.BinaryForm ℂ n)) (z : ℂ)
    (hF : ∀ e : Fin 2 →₀ ℕ,
      HasDerivAt (fun w : ℂ => MvPolynomial.coeff e (F w).val)
        (MvPolynomial.coeff e P.val) z) :
    ∀ e : Fin 2 →₀ ℕ,
      HasDerivAt (fun w : ℂ => MvPolynomial.coeff e (A (F w)).val)
        (MvPolynomial.coeff e (A P).val) z := by
  classical
  intro e
  obtain ⟨c, hc⟩ := p02_es_177ebb5a_lcd_coeff_linear_combination n A e
  simp_rw [hc]
  apply HasDerivAt.fun_sum
  intro r _
  exact (hF _).const_mul (c r)

/-- The modular defect of an Eichler integral is constant on the upper half-plane. -/
theorem p02_es_177ebb5a_primitive_exists_constant_defect
    (N : ℕ) [NeZero N] (n : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) ((n : ℤ) + 2))
    (F : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n))
    (hF : HeckeEis.IsEichlerIntegral n (fun τ => f τ) F) :
    HeckeEis.IsEquivariantPrimitiveWith
      ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype) F := by
  let ρ := (HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype
  intro γ
  let D (τ : UpperHalfPlane) := F ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) • τ) - ρ γ (F τ)
  refine ⟨D UpperHalfPlane.I, ?_⟩
  intro τ
  apply Subtype.ext
  apply MvPolynomial.ext
  intro e
  let q (z : ℂ) := MvPolynomial.coeff e (D (UpperHalfPlane.ofComplex z)).val
  have hq (υ : UpperHalfPlane) : HasDerivAt q 0 (υ : ℂ) := by
    have hlinear := p02_es_177ebb5a_cd_linear_coeff_derivative n (ρ γ)
      (fun z => F (UpperHalfPlane.ofComplex z)) (f υ • HeckeEis.linePow n (υ : ℂ))
      (υ : ℂ) (fun d => by
        simpa only [Submodule.coe_smul, MvPolynomial.coeff_smul, smul_eq_mul] using hF d υ) e
    have hpullback := p02_es_177ebb5a_cd_modular_pullback_derivative N n f F hF γ e υ
    convert! hpullback.sub hlinear using 1
    simp only [ρ, map_smul, Submodule.coe_smul, MvPolynomial.coeff_smul,
      smul_eq_mul, sub_self]
  have hconstant := UpperHalfPlane.isOpen_upperHalfPlaneSet.is_const_of_deriv_eq_zero
    (convex_halfSpace_im_gt (0 : ℝ)).isPreconnected
    (fun z hz => (hq ⟨z, hz⟩).differentiableAt.differentiableWithinAt)
    (fun z hz => (hq ⟨z, hz⟩).deriv) τ.im_pos UpperHalfPlane.I.im_pos
  simpa only [q, UpperHalfPlane.ofComplex_apply] using hconstant

theorem p02_es_177ebb5a_primitive_exists
    (N : ℕ) [NeZero N] (n : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) ((n : ℤ) + 2)) :
    ∃ F : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n),
      HeckeEis.IsEichlerIntegral n (fun τ => f τ) F ∧
      HeckeEis.IsEquivariantPrimitiveWith
        ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype) F := by
  obtain ⟨F, hF⟩ := p02_es_177ebb5a_primitive_exists_holomorphic_integral n
    (fun τ => f τ) (UpperHalfPlane.mdifferentiable_iff.mp f.holo')
  exact ⟨F, hF, p02_es_177ebb5a_primitive_exists_constant_defect N n f F hF⟩

end Submission
