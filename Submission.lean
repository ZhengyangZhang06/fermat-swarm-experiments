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
/-- Differentiate a finite jet sum using the descending-factorial recurrence. -/
theorem p02_es_177ebb5a_med_sum_derivative :
    ∀ (n r : ℕ) (a : Fin (n + 1) → ℂ → ℂ) (b : Fin (n + 1) → ℂ) (c t : ℂ),
      (∀ k : Fin (n + 1), HasDerivAt (a k) (c * b k) t) →
      HasDerivAt
        (fun z : ℂ => ∑ k : Fin (n + 1),
          a k z * (Nat.descFactorial k.val r : ℂ) * (-z) ^ (k.val - r))
        (c * (∑ k : Fin (n + 1),
          b k * (Nat.descFactorial k.val r : ℂ) * (-t) ^ (k.val - r)) -
          (∑ k : Fin (n + 1), a k t * (Nat.descFactorial k.val (r + 1) : ℂ) *
            (-t) ^ (k.val - (r + 1)))) t := by
  intro n r a b c t ha
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply HasDerivAt.fun_sum
  intro k _
  convert! (((ha k).mul_const (Nat.descFactorial k.val r : ℂ)).mul
    ((hasDerivAt_id' t).neg.pow (k.val - r))) using 1
  simp only [Nat.descFactorial_succ, Nat.cast_mul, Nat.sub_sub, Pi.pow_apply, Pi.neg_apply]
  ring
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

theorem p02_es_177ebb5a_tff_constant_dehomogenization
    (n : ℕ) (A : ↥(HeckeEis.BinaryForm ℂ n)) (α : ℂ)
    (hA : MvPolynomial.eval₂ Polynomial.C
      (fun j : Fin 2 => if j = 0 then 1 else Polynomial.X) A.val = Polynomial.C α) :
    A.val = MvPolynomial.C α * MvPolynomial.X (0 : Fin 2) ^ n := by
  classical
  have hdegree (d : Fin 2 →₀ ℕ) (hd : d ∈ A.val.support) : d 0 + d 1 = n := by
    simpa only [← Finsupp.degree_apply, Finsupp.degree_eq_sum, Fin.sum_univ_two] using
      (A.property.degree_eq_sum_deg_support hd).symm
  -- At fixed total degree, the exponent of X₁ uniquely determines the monomial.
  have hcoeff (d : Fin 2 →₀ ℕ) (hd : d 0 + d 1 = n) :
      (MvPolynomial.eval₂ Polynomial.C
        (fun j : Fin 2 => if j = 0 then 1 else Polynomial.X) A.val).coeff (d 1) =
        MvPolynomial.coeff d A.val := by
    rw [MvPolynomial.eval₂_eq']
    simp only [Fin.prod_univ_two, Fin.isValue, ite_true, one_pow, one_ne_zero,
      ite_false, one_mul, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single d]
    · simp
    · intro e he hne
      have hedeg := hdegree e he
      have hne1 : d 1 ≠ e 1 := by
        intro he1
        apply hne
        have he0 : e 0 = d 0 := by omega
        ext j
        fin_cases j
        · exact he0
        · exact he1.symm
      simp [hne1]
    · intro hnot
      simp [MvPolynomial.notMem_support_iff.mp hnot]
  apply MvPolynomial.ext
  intro d
  by_cases hd : d 0 + d 1 = n
  · have hc := hcoeff d hd
    rw [hA, Polynomial.coeff_C] at hc
    rw [← hc, MvPolynomial.C_mul_X_pow_eq_monomial, MvPolynomial.coeff_monomial]
    have heq : Finsupp.single (0 : Fin 2) n = d ↔ d 1 = 0 := by
      constructor
      · intro h
        rw [← h]
        simp
      · intro h
        ext j
        fin_cases j <;> simp at * <;> omega
    simp only [heq]
  · rw [A.property.coeff_eq_zero, (MvPolynomial.isHomogeneous_C_mul_X_pow α
      (0 : Fin 2) n).coeff_eq_zero]
    all_goals simpa [Finsupp.degree_eq_sum, Fin.sum_univ_two] using hd

open Filter MeasureTheory Set
open scoped Topology

/-- The polynomial-exponential weight has a finite nonnegative integral, controls its
translated interval integrals, and tends to zero at infinity. -/
open Filter MeasureTheory Set
open scoped Topology

/-- The polynomial-exponential weight has a finite nonnegative integral, controls its
translated interval integrals, and tends to zero at infinity. -/
theorem p02_es_177ebb5a_scl_polynomial_exp_tail :
    ∀ (n : ℕ) (a : ℝ), 0 < a →
      IntegrableOn (fun s : ℝ => (1 + s) ^ n * Real.exp (-a * s)) (Ioi 0) ∧
      0 ≤ (∫ s in Ioi (0 : ℝ), (1 + s) ^ n * Real.exp (-a * s)) ∧
      (∀ (y t : ℝ), 0 ≤ y → y ≤ t →
        (∫ s in y..t, (1 + s) ^ n * Real.exp (-a * s)) ≤
          (∫ s in Ioi (0 : ℝ), (1 + s) ^ n * Real.exp (-a * s)) *
            (1 + y) ^ n * Real.exp (-a * y)) ∧
      Tendsto (fun y : ℝ => (1 + y) ^ n * Real.exp (-a * y)) atTop (𝓝 0) := by
  intro n a ha
  -- Polynomial growth is dominated by every positive exponential rate.
  have hdecay (b : ℝ) (hb : 0 < b) :
      Tendsto (fun y : ℝ => (1 + y) ^ n * Real.exp (-b * y)) atTop (𝓝 0) := by
    -- Shift the library's polynomial/exponential ratio by 1 and cancel the shift by exp b.
    have h := ((isLittleO_pow_exp_pos_mul_atTop n hb).tendsto_div_nhds_zero.comp
      (tendsto_atTop_add_const_left atTop 1 tendsto_id)).mul_const (Real.exp b)
    simp only [zero_mul] at h
    convert h using 1
    ext y
    simp only [Function.comp_apply, id_eq]
    rw [div_eq_mul_inv, ← Real.exp_neg, mul_assoc, ← Real.exp_add]
    congr 2
    ring
  let w : ℝ → ℝ := fun s => (1 + s) ^ n * Real.exp (-a * s)
  have hw : Continuous w := by fun_prop
  have hw_nonneg (s : ℝ) (hs : 0 ≤ s) : 0 ≤ w s := by
    dsimp [w]
    positivity
  -- Comparison with the exponential of half the rate gives integrability.
  have hint : IntegrableOn w (Ioi 0) := by
    apply integrable_of_isBigO_exp_neg (half_pos ha) hw.continuousOn
    -- Dividing w by exp (-(a / 2) * s) leaves the same weight at the positive half-rate.
    apply Asymptotics.IsLittleO.isBigO
    apply Asymptotics.isLittleO_of_tendsto (fun x hx => (Real.exp_ne_zero _ hx).elim)
    convert hdecay (a / 2) (half_pos ha) using 1
    ext s
    dsimp [w]
    rw [div_eq_mul_inv, ← Real.exp_neg, mul_assoc, ← Real.exp_add]
    congr 2
    ring
  refine ⟨hint, setIntegral_nonneg measurableSet_Ioi (fun s hs => hw_nonneg s hs.le),
    ?_, hdecay a ha⟩
  intro y t hy hyt
  have hty : 0 ≤ t - y := sub_nonneg.mpr hyt
  -- Translation reduces the tail estimate to submultiplicativity on [0, ∞).
  have hsub (v : ℝ) (hv : 0 ≤ v) : w (y + v) ≤ w y * w v := by
    have hp : (1 + (y + v)) ^ n ≤ ((1 + y) * (1 + v)) ^ n :=
      pow_le_pow_left₀ (by positivity) (by nlinarith [mul_nonneg hy hv]) n
    dsimp [w]
    calc
      (1 + (y + v)) ^ n * Real.exp (-a * (y + v)) ≤
          ((1 + y) * (1 + v)) ^ n * Real.exp (-a * (y + v)) :=
        mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
      _ = ((1 + y) ^ n * Real.exp (-a * y)) *
          ((1 + v) ^ n * Real.exp (-a * v)) := by
        rw [mul_pow, show -a * (y + v) = -a * y + -a * v by ring, Real.exp_add]
        ring
  have hfinite : (∫ v in (0 : ℝ)..t - y, w v) ≤ ∫ v in Ioi (0 : ℝ), w v := by
    rw [intervalIntegral.integral_of_le hty]
    apply setIntegral_mono_set hint
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv using hw_nonneg v hv.le
    · exact Filter.Eventually.of_forall (fun v hv => hv.1)
  change (∫ s in y..t, w s) ≤ (∫ s in Ioi (0 : ℝ), w s) *
    (1 + y) ^ n * Real.exp (-a * y)
  calc
    (∫ s in y..t, w s) = ∫ v in (0 : ℝ)..t - y, w (y + v) := by
      rw [intervalIntegral.integral_comp_add_left]
      simp
    _ ≤ ∫ v in (0 : ℝ)..t - y, w y * w v := by
      apply intervalIntegral.integral_mono_on hty
        ((hw.comp (continuous_const.add continuous_id)).intervalIntegrable _ _)
        ((continuous_const.mul hw).intervalIntegrable _ _)
      intro v hv
      exact hsub v hv.1
    _ = w y * ∫ v in (0 : ℝ)..t - y, w v := intervalIntegral.integral_const_mul _ _
    _ ≤ w y * ∫ v in Ioi (0 : ℝ), w v :=
      mul_le_mul_of_nonneg_left hfinite (hw_nonneg y hy)
    _ = (∫ s in Ioi (0 : ℝ), w s) * (1 + y) ^ n * Real.exp (-a * y) := by
      dsimp [w]
      ring

/-- A complex polynomial fixed by a nonzero translation is constant.
For positive degree `d + 1`, its `d`th Hasse derivative is linear; the Taylor
coefficient identity makes translation invariance contradict its nonzero slope. -/
theorem p02_es_177ebb5a_tff_periodic_polynomial_constant
    (p : Polynomial ℂ) (c : ℂ) (hc : c ≠ 0)
    (hperiod : p.comp (Polynomial.X + Polynomial.C c) = p) :
    p = Polynomial.C (p.coeff 0) := by
  apply Polynomial.eq_C_of_natDegree_eq_zero
  by_contra hdegree
  obtain ⟨d, hd⟩ := Nat.exists_eq_succ_of_ne_zero hdegree
  have hp : p ≠ 0 := Polynomial.ne_zero_of_natDegree_gt (Nat.pos_of_ne_zero hdegree)
  have hlinear : (Polynomial.hasseDeriv d p).natDegree ≤ 1 := by
    simpa [hd] using Polynomial.natDegree_hasseDeriv_le p d
  -- The degree-d coefficient of the translate is (d + 1) * p.coeff (d + 1) * c
  -- plus p.coeff d; invariance forces the first summand to vanish.
  have hcoeff := congrArg (fun q : Polynomial ℂ => q.coeff d) hperiod
  rw [← Polynomial.taylor_apply, Polynomial.taylor_coeff,
    Polynomial.eq_X_add_C_of_natDegree_le_one hlinear] at hcoeff
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.hasseDeriv_coeff, Nat.zero_add, Nat.choose_self,
    Nat.cast_one, one_mul, Nat.add_comm 1 d, Nat.choose_succ_self_right] at hcoeff
  have hlead : p.coeff (d + 1) ≠ 0 := by
    simpa only [Polynomial.leadingCoeff, hd, Nat.succ_eq_add_one] using
      Polynomial.leadingCoeff_ne_zero.mpr hp
  have hcast : ((d + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero d)
  exact (mul_ne_zero (mul_ne_zero hcast hlead) hc)
    (add_right_cancel (hcoeff.trans (zero_add _).symm))
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

theorem p02_es_177ebb5a_pp_integral_parabolic_normal_form :
    ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      (γ : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4 →
      ∃ (σ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (m : ℤ),
        σ⁻¹ * γ * σ = ModularGroup.T ^ m ∨ σ⁻¹ * γ * σ = -(ModularGroup.T ^ m) := by
  intro γ htrace
  obtain ⟨ε, hε, htr⟩ :
      ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ γ.val.trace = 2 * ε := by
    have ht : γ.val.trace ^ 2 = (2 : ℤ) ^ 2 := by simpa using htrace
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp ht with ht | ht
    · exact ⟨1, Or.inl rfl, by simpa using ht⟩
    · exact ⟨-1, Or.inr rfl, by simpa using ht⟩
  have hεsq : ε ^ 2 = 1 := by rcases hε with rfl | rfl <;> norm_num
  -- The primitive-kernel dependency also handles the central case γ = εI.
  have hsing : (γ.val - ε • (1 : Matrix (Fin 2) (Fin 2) ℤ)).det = 0 := by
    have hdet := γ.property
    have htr' : γ.val 0 0 + γ.val 1 1 = 2 * ε := by
      simpa [Matrix.trace, Matrix.diag, Fin.sum_univ_two] using htr
    simp only [Matrix.det_fin_two] at hdet ⊢
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    norm_num
    nlinarith only [hdet, hεsq, congrArg (ε * ·) htr']
  obtain ⟨p, q, hpq, hker⟩ :=
    p02_es_177ebb5a_pnf_primitive_kernel _ hsing
  have heigen : γ.val.mulVec ![p, q] = ![ε * p, ε * q] := by
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hker
    simpa using hker
  obtain ⟨σ, b, hσ⟩ :=
    p02_es_177ebb5a_pnf_primitive_eigenvector_triangular γ ε p q hεsq hpq heigen
  rcases hε with rfl | rfl
  · refine ⟨σ, b, Or.inl ?_⟩
    apply Subtype.ext
    exact hσ.trans (ModularGroup.coe_T_zpow b).symm
  · refine ⟨σ, -b, Or.inr ?_⟩
    apply Subtype.ext
    change (σ⁻¹ * γ * σ).val = -((ModularGroup.T ^ (-b)).val)
    rw [hσ, ModularGroup.coe_T_zpow]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
/-- A homogeneous binary form fixed by a nonzero integral translation is a power of X₀. -/
theorem p02_es_177ebb5a_tb_fixed_form
    (N : ℕ) [NeZero N] (n : ℕ) (A : ↥(HeckeEis.BinaryForm ℂ n))
    (hA : HeckeEis.binaryFormRepSL ℂ n (ModularGroup.T ^ N) A = A) :
    ∃ α : ℂ, A.val = MvPolynomial.C α * MvPolynomial.X (0 : Fin 2) ^ n := by
  classical
  let d : MvPolynomial (Fin 2) ℂ →+* Polynomial ℂ :=
    MvPolynomial.eval₂Hom Polynomial.C (fun j => if j = 0 then 1 else Polynomial.X)
  let t := Polynomial.compRingHom (Polynomial.X + Polynomial.C (N : ℂ))
  have hmatrix : ((ModularGroup.T ^ N : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      !![1, (N : ℤ); 0, 1] := by
    simpa only [zpow_natCast] using ModularGroup.coe_T_zpow (N : ℤ)
  -- Dehomogenizing the column substitution is translation of the univariate polynomial.
  have hcomm : d.comp (HeckeEis.binarySubst ℂ (ModularGroup.T ^ N : SL(2, ℤ))).toRingHom =
      t.comp d := by
    apply MvPolynomial.ringHom_ext
    · intro a
      change d (HeckeEis.binarySubst ℂ (ModularGroup.T ^ N : SL(2, ℤ)) (MvPolynomial.C a)) =
        t (d (MvPolynomial.C a))
      rw [HeckeEis.binarySubst_C]
      simp [d, t]
    · intro a
      change d (HeckeEis.binarySubst ℂ (ModularGroup.T ^ N : SL(2, ℤ)) (MvPolynomial.X a)) =
        t (d (MvPolynomial.X a))
      rw [HeckeEis.binarySubst_X, hmatrix]
      fin_cases a <;> simp [d, t, Fin.sum_univ_two, add_comm]
  have hfixed : HeckeEis.binarySubst ℂ (ModularGroup.T ^ N : SL(2, ℤ)) A.val = A.val :=
    congrArg Subtype.val hA
  have hperiod : (d A.val).comp (Polynomial.X + Polynomial.C (N : ℂ)) = d A.val := by
    calc
      _ = d (HeckeEis.binarySubst ℂ (ModularGroup.T ^ N : SL(2, ℤ)) A.val) :=
        (congrArg (fun f : MvPolynomial (Fin 2) ℂ →+* Polynomial ℂ => f A.val) hcomm).symm
      _ = d A.val := congrArg d hfixed
  refine ⟨(d A.val).coeff 0, p02_es_177ebb5a_tff_constant_dehomogenization n A _ ?_⟩
  exact p02_es_177ebb5a_tff_periodic_polynomial_constant (d A.val) (N : ℂ)
    (Nat.cast_ne_zero.mpr (NeZero.ne N)) hperiod

end Submission

theorem Submission.p02_es_177ebb5a_med_js_iterated_monomial :
    ∀ (d : Fin 2 →₀ ℕ) (a : ℂ) (r : ℕ),
      ((fun p : MvPolynomial (Fin 2) ℂ => MvPolynomial.pderiv (1 : Fin 2) p)^[r]
        (MvPolynomial.monomial d a)) =
      MvPolynomial.monomial (d - Finsupp.single (1 : Fin 2) r)
        (a * (Nat.descFactorial (d 1) r : ℂ)) := by
  intro d a r
  induction r with
  | zero => simp
  | succ r ih =>
      rw [Function.iterate_succ_apply', ih, MvPolynomial.pderiv_monomial]
      have hexponent :
          d - Finsupp.single (1 : Fin 2) r - Finsupp.single (1 : Fin 2) 1 =
            d - Finsupp.single (1 : Fin 2) (r + 1) := by
        ext i
        by_cases hi : i = 1
        · subst i
          simp [Finsupp.tsub_apply, Nat.sub_sub]
        · simp [Finsupp.tsub_apply, Finsupp.single_eq_of_ne hi]
      rw [hexponent]
      simp only [Finsupp.tsub_apply, Finsupp.single_eq_same,
        Nat.descFactorial_succ, Nat.cast_mul]
      congr 1
      ring

/-- Each output coefficient of a linear map is a fixed linear combination of input coefficients. -/
theorem Submission.p02_es_177ebb5a_ic_lct_coeff_linear_combination
    (n : ℕ) (A : ↥(HeckeEis.BinaryForm ℂ n) →ₗ[ℂ] ↥(HeckeEis.BinaryForm ℂ n))
    (e : Fin 2 →₀ ℕ) :
    ∃ c : Fin (n + 1) → ℂ, ∀ Q : ↥(HeckeEis.BinaryForm ℂ n),
      MvPolynomial.coeff e (A Q).val = ∑ r : Fin (n + 1), c r *
        MvPolynomial.coeff (Finsupp.single (0 : Fin 2) r.val +
          Finsupp.single (1 : Fin 2) (n - r.val)) Q.val := by
  classical
  let exponent (r : Fin (n + 1)) : Fin 2 →₀ ℕ :=
    Finsupp.single 0 r.val + Finsupp.single 1 (n - r.val)
  have hdegree (r : Fin (n + 1)) : (exponent r).degree = n := by
    simp only [exponent, map_add, Finsupp.degree_single]
    exact Nat.add_sub_of_le (Nat.le_of_lt_succ r.isLt)
  let b (r : Fin (n + 1)) : ↥(HeckeEis.BinaryForm ℂ n) :=
    ⟨MvPolynomial.monomial (exponent r) (1 : ℂ),
      MvPolynomial.isHomogeneous_monomial 1 (hdegree r)⟩
  refine ⟨fun r => MvPolynomial.coeff e (A (b r)).val, ?_⟩
  intro Q
  have hQ : Q = ∑ r : Fin (n + 1), MvPolynomial.coeff (exponent r) Q.val • b r := by
    apply Subtype.ext
    simpa [b, exponent] using Submission.p02_es_177ebb5a_ic_lct_monomial_expansion n Q
  let L : ↥(HeckeEis.BinaryForm ℂ n) →ₗ[ℂ] ℂ :=
    (MvPolynomial.lcoeff ℂ e).comp ((HeckeEis.BinaryForm ℂ n).subtype.comp A)
  change L Q = ∑ r : Fin (n + 1), L (b r) * MvPolynomial.coeff (exponent r) Q.val
  calc
    L Q = L (∑ r : Fin (n + 1), MvPolynomial.coeff (exponent r) Q.val • b r) :=
      congrArg L hQ
    _ = ∑ r : Fin (n + 1), L (b r) * MvPolynomial.coeff (exponent r) Q.val := by
      simp only [map_sum, map_smul, smul_eq_mul, mul_comm]

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

namespace Submission

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

end Submission


theorem Submission.p02_es_177ebb5a_ssl_tail_limit :
    ∀ (f : ℝ → ℂ) (e : ℝ → ℝ) (y₀ : ℝ),
      Filter.Tendsto e Filter.atTop (nhds (0 : ℝ)) →
      (∀ (y t : ℝ), y₀ ≤ y → y ≤ t → ‖f t - f y‖ ≤ e y) →
      ∃ b : ℂ, Filter.Tendsto f Filter.atTop (nhds b) ∧
        ∀ y : ℝ, y₀ ≤ y → ‖f y - b‖ ≤ e y := by
  intro f e y₀ he hbound
  have hcauchy : CauchySeq f := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp (he.eventually (gt_mem_nhds hε))
    refine ⟨max y₀ T, ?_⟩
    intro s hs t ht
    have hsy : y₀ ≤ s := (le_max_left _ _).trans hs
    have hty : y₀ ≤ t := (le_max_left _ _).trans ht
    have hsT : T ≤ s := (le_max_right _ _).trans hs
    have htT : T ≤ t := (le_max_right _ _).trans ht
    rcases le_total s t with hst | hts
    · rw [dist_eq_norm, norm_sub_rev]
      exact (hbound s t hsy hst).trans_lt (hT s hsT)
    · rw [dist_eq_norm]
      exact (hbound t s hty hts).trans_lt (hT t htT)
  obtain ⟨b, hb⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨b, hb, ?_⟩
  intro y hy
  rw [norm_sub_rev]
  apply le_of_tendsto (hb.sub_const (f y)).norm
  exact (Filter.eventually_ge_atTop y).mono fun t ht => hbound y t hy ht

theorem Submission.p02_es_177ebb5a_med_jet_sum :
    ∀ (n : ℕ) (P : ↥(HeckeEis.BinaryForm ℂ n)) (r : ℕ) (z : ℂ),
      MvPolynomial.eval (fun j : Fin 2 => if j = 0 then 1 else -z)
        ((fun p : MvPolynomial (Fin 2) ℂ => MvPolynomial.pderiv (1 : Fin 2) p)^[r]
          P.val) =
        ∑ k : Fin (n + 1),
          MvPolynomial.coeff
              (Finsupp.single (0 : Fin 2) (n - k.val) + Finsupp.single (1 : Fin 2) k.val)
              P.val *
            (Nat.descFactorial k.val r : ℂ) * (-z) ^ (k.val - r) := by
  classical
  intro n P r z
  let d (k : Fin (n + 1)) : Fin 2 →₀ ℕ :=
    Finsupp.single 0 (n - k.val) + Finsupp.single 1 k.val
  have hexpand : P.val = ∑ k : Fin (n + 1),
      MvPolynomial.monomial (d k) (MvPolynomial.coeff (d k) P.val) := by
    conv_lhs => rw [Submission.p02_es_177ebb5a_lcd_monomial_expansion n P]
    refine Fintype.sum_equiv Fin.revPerm _ _ ?_
    intro k
    simp only [d, Fin.revPerm_apply, Fin.val_rev, Nat.add_sub_add_right,
      Nat.sub_sub_self (Nat.le_of_lt_succ k.isLt),
      MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  let D : Module.End ℂ (MvPolynomial (Fin 2) ℂ) :=
    (MvPolynomial.pderiv (1 : Fin 2)).toLinearMap
  change MvPolynomial.eval _ ((D : MvPolynomial (Fin 2) ℂ →
    MvPolynomial (Fin 2) ℂ)^[r] P.val) = _
  rw [← Module.End.pow_apply]
  conv_lhs => rw [hexpand, map_sum]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [Module.End.pow_apply]
  change MvPolynomial.eval _
    ((fun p : MvPolynomial (Fin 2) ℂ => MvPolynomial.pderiv (1 : Fin 2) p)^[r]
      (MvPolynomial.monomial (d k) (MvPolynomial.coeff (d k) P.val))) = _
  rw [Submission.p02_es_177ebb5a_med_js_iterated_monomial, MvPolynomial.eval_monomial,
    Finsupp.prod_fintype _ _ (by intro j; simp)]
  simp [d, Fin.prod_univ_two, Finsupp.tsub_apply]

/-- A linear map of binary forms preserves coefficientwise derivatives. -/
theorem Submission.p02_es_177ebb5a_ic_lmd_linear_coeff
    (n : ℕ) (A : ↥(HeckeEis.BinaryForm ℂ n) →ₗ[ℂ] ↥(HeckeEis.BinaryForm ℂ n))
    (F : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n))
    (P : ↥(HeckeEis.BinaryForm ℂ n)) (τ : UpperHalfPlane) :
    (∀ d : Fin 2 →₀ ℕ,
      HasDerivAt (fun z : ℂ => MvPolynomial.coeff d (F (UpperHalfPlane.ofComplex z)).val)
        (MvPolynomial.coeff d P.val) (τ : ℂ)) →
    ∀ e : Fin 2 →₀ ℕ,
      HasDerivAt (fun z : ℂ => MvPolynomial.coeff e (A (F (UpperHalfPlane.ofComplex z))).val)
        (MvPolynomial.coeff e (A P).val) (τ : ℂ) := by
  intro h e
  obtain ⟨c, hc⟩ := Submission.p02_es_177ebb5a_ic_lct_coeff_linear_combination n A e
  simp_rw [hc]
  exact HasDerivAt.fun_sum fun r _ => (h _).const_mul (c r)
theorem Submission.p02_es_177ebb5a_ssl_segment_estimates :
    ∀ (F H : ℂ → ℂ) (w : ℝ → ℝ) (L y₀ : ℝ),
      0 ≤ L → 0 < y₀ → ContinuousOn H {z : ℂ | 0 < z.im} →
      (∀ z : ℂ, 0 < z.im → HasDerivAt F (H z) z) →
      ContinuousOn w (Set.Ici y₀) →
      (∀ z : ℂ, 0 ≤ z.re → z.re ≤ L → y₀ ≤ z.im → ‖H z‖ ≤ w z.im) →
      (∀ (x y t : ℝ), 0 ≤ x → x ≤ L → y₀ ≤ y → y ≤ t →
        ‖F ((x : ℂ) + (t : ℂ) * Complex.I) -
          F ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤ ∫ s in y..t, w s) ∧
      (∀ (x y : ℝ), 0 ≤ x → x ≤ L → y₀ ≤ y →
        ‖F ((x : ℂ) + (y : ℂ) * Complex.I) - F ((y : ℂ) * Complex.I)‖ ≤
          x * w y) := by
  intro F H w L y₀ _hL hy₀ hH hF hw hbound
  constructor
  · intro x y t hx hxL hy hyt
    have hpath : Continuous (fun s : ℝ => (x : ℂ) + (s : ℂ) * Complex.I) := by
      fun_prop
    have hupper (s : ℝ) (hs : s ∈ Set.uIcc y t) :
        0 < ((x : ℂ) + (s : ℂ) * Complex.I).im := by
      have hys : y ≤ s := (Set.uIcc_of_le hyt ▸ hs).1
      simpa using hy₀.trans_le (hy.trans hys)
    have hderiv (s : ℝ) (hs : s ∈ Set.uIcc y t) :
        HasDerivAt (fun u : ℝ => F ((x : ℂ) + (u : ℂ) * Complex.I))
          (H ((x : ℂ) + (s : ℂ) * Complex.I) * Complex.I) s := by
      have hp : HasDerivAt (fun z : ℂ => (x : ℂ) + z * Complex.I) Complex.I
          (s : ℂ) := by
        simpa using ((hasDerivAt_id (s : ℂ)).mul_const Complex.I).const_add (x : ℂ)
      exact ((hF _ (hupper s hs)).comp (s : ℂ) hp).comp_ofReal
    have hint : IntervalIntegrable
        (fun s : ℝ => H ((x : ℂ) + (s : ℂ) * Complex.I) * Complex.I)
        MeasureTheory.volume y t :=
      ((hH.comp hpath.continuousOn (fun s hs => hupper s hs)).mul_const
        Complex.I).intervalIntegrable
    rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
    apply intervalIntegral.norm_integral_le_of_norm_le hyt
    · apply Filter.Eventually.of_forall
      intro s hs
      have hys : y₀ ≤ s := hy.trans hs.1.le
      simpa using hbound ((x : ℂ) + (s : ℂ) * Complex.I)
        (by simpa using hx) (by simpa using hxL) (by simpa using hys)
    · apply (hw.mono ?_).intervalIntegrable
      intro s hs
      exact hy.trans (Set.uIcc_of_le hyt ▸ hs).1
  · intro x y hx hxL hy
    have hpath : Continuous (fun s : ℝ => (s : ℂ) + (y : ℂ) * Complex.I) := by
      fun_prop
    have hupper (s : ℝ) : 0 < ((s : ℂ) + (y : ℂ) * Complex.I).im := by
      simpa using hy₀.trans_le hy
    have hderiv (s : ℝ) (_hs : s ∈ Set.uIcc 0 x) :
        HasDerivAt (fun u : ℝ => F ((u : ℂ) + (y : ℂ) * Complex.I))
          (H ((s : ℂ) + (y : ℂ) * Complex.I)) s := by
      simpa only [mul_one] using!
        ((hF _ (hupper s)).comp (s : ℂ)
          ((hasDerivAt_id (s : ℂ)).add_const ((y : ℂ) * Complex.I))).comp_ofReal
    have hint : IntervalIntegrable
        (fun s : ℝ => H ((s : ℂ) + (y : ℂ) * Complex.I))
        MeasureTheory.volume 0 x :=
      (hH.comp hpath.continuousOn (fun s _ => hupper s)).intervalIntegrable
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
    simp only [Complex.ofReal_zero, zero_add] at hFTC
    rw [← hFTC]
    calc
      _ ≤ w y * |x - 0| := intervalIntegral.norm_integral_le_of_norm_le_const (by
        intro s hs
        have hs' : s ∈ Set.Ioc 0 x := Set.uIoc_of_le hx ▸ hs
        simpa using hbound ((s : ℂ) + (y : ℂ) * Complex.I)
          (by simpa using hs'.1.le) (by simpa using hs'.2.trans hxL)
          (by simpa using hy))
      _ = x * w y := by rw [sub_zero, abs_of_nonneg hx, mul_comm]
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

/-- Differentiate an iterated partial evaluated at the moving point `(1, -z)`. -/
theorem Submission.p02_es_177ebb5a_sd_jr_moving_eval_derivative :
    ∀ (n : ℕ) (F : ℂ → ↥(HeckeEis.BinaryForm ℂ n))
      (G : ↥(HeckeEis.BinaryForm ℂ n)) (c t : ℂ),
      (∀ d : Fin 2 →₀ ℕ,
        HasDerivAt (fun z : ℂ => MvPolynomial.coeff d (F z).val)
          (c * MvPolynomial.coeff d G.val) t) →
      ∀ r : ℕ, r ≤ n →
        HasDerivAt
          (fun z : ℂ => MvPolynomial.eval (fun j : Fin 2 => if j = 0 then 1 else -z)
            ((fun p : MvPolynomial (Fin 2) ℂ => MvPolynomial.pderiv (1 : Fin 2) p)^[r]
              (F z).val))
          (c * MvPolynomial.eval (fun j : Fin 2 => if j = 0 then 1 else -t)
              ((fun p : MvPolynomial (Fin 2) ℂ => MvPolynomial.pderiv (1 : Fin 2) p)^[r]
                G.val) -
            MvPolynomial.eval (fun j : Fin 2 => if j = 0 then 1 else -t)
              ((fun p : MvPolynomial (Fin 2) ℂ => MvPolynomial.pderiv (1 : Fin 2) p)^[r + 1]
                (F t).val)) t := by
  intro n F G c t hcoeff r _hr
  simp_rw [Submission.p02_es_177ebb5a_med_jet_sum]
  exact Submission.p02_es_177ebb5a_med_sum_derivative n r _ _ c t
    (fun k => hcoeff
      (Finsupp.single (0 : Fin 2) (n - k.val) + Finsupp.single (1 : Fin 2) k.val))

namespace Submission

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

theorem p02_es_177ebb5a_ic_linear_mobius_derivative
    (n : ℕ)
    (A : ↥(HeckeEis.BinaryForm ℂ n) →ₗ[ℂ] ↥(HeckeEis.BinaryForm ℂ n))
    (F : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n))
    (P : ↥(HeckeEis.BinaryForm ℂ n))
    (σ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (τ : UpperHalfPlane)
    (hF : ∀ d : Fin 2 →₀ ℕ,
      HasDerivAt (fun z : ℂ => MvPolynomial.coeff d (F (UpperHalfPlane.ofComplex z)).val)
        (MvPolynomial.coeff d P.val) ((σ • τ : UpperHalfPlane) : ℂ)) :
    ∀ e : Fin 2 →₀ ℕ,
      HasDerivAt
        (fun z : ℂ => MvPolynomial.coeff e (A (F (σ • UpperHalfPlane.ofComplex z))).val)
        (MvPolynomial.coeff e (A P).val / (HeckeEis.jFactor σ τ) ^ 2) (τ : ℂ) := by
  intro e
  exact p02_es_177ebb5a_ic_lmd_scalar_pullback
    (fun w => MvPolynomial.coeff e (A (F w)).val)
    (MvPolynomial.coeff e (A P).val) σ τ
    (Submission.p02_es_177ebb5a_ic_lmd_linear_coeff n A F P (σ • τ) hF e)

theorem p02_es_177ebb5a_primitive_parabolic :
    ∀ (N : ℕ) [NeZero N] (n : ℕ)
      (f : CuspForm (CongruenceSubgroup.Gamma0 N) ((n : ℤ) + 2))
      (F : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n)),
      HeckeEis.IsEichlerIntegral n (fun τ => f τ) F →
      ∀ hF : HeckeEis.IsEquivariantPrimitiveWith
        ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype) F,
      HeckeEis.IsParabolicCocycle
        ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype)
        hF.cocycle := by
  classical
  intro N _ n f F hEI hF γ hγ
  obtain ⟨σ, m, hσ⟩ := p02_es_177ebb5a_pp_integral_parabolic_normal_form γ hγ
  obtain ⟨A, hA⟩ := p02_es_177ebb5a_pp_primitive_cusp_limit N n f F hEI σ
  let ρ := (HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype
  let ray (x y : ℝ) := UpperHalfPlane.ofComplex ((x : ℂ) + (y : ℂ) * Complex.I)
  -- Both signs of the normal form act by the same real translation.
  have hmove (y : ℝ) (hy : 0 < y) :
      (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) • (σ • ray 0 y) =
        σ • ray (m : ℝ) y := by
    have hconj : (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) • (σ • ray 0 y) =
        σ • ((σ⁻¹ * γ * σ) • ray 0 y) := by
      simp only [mul_smul, smul_inv_smul]
    rw [hconj]
    have htrans : (σ⁻¹ * γ * σ) • ray 0 y = (m : ℝ) +ᵥ ray 0 y := by
      rcases hσ with hσ | hσ
      · rw [hσ, UpperHalfPlane.modular_T_zpow_smul]
      · rw [hσ, ModularGroup.SL_neg_smul, UpperHalfPlane.modular_T_zpow_smul]
    rw [htrans]
    congr 1
    have hpos (x : ℝ) : 0 < ((x : ℂ) + (y : ℂ) * Complex.I).im := by simpa using hy
    apply UpperHalfPlane.ext
    simp [ray, UpperHalfPlane.ofComplex_apply_of_im_pos (hpos _), UpperHalfPlane.coe_vadd]
  -- A fixed finite coefficient expansion allows the representation to pass through the limit.
  let s := (Finsupp.finite_of_degree_eq (σ := Fin 2) n).toFinset
  have hexpand (Q : ↥(HeckeEis.BinaryForm ℂ n)) :
      Q.val = ∑ e ∈ s, MvPolynomial.coeff e Q.val • MvPolynomial.monomial e (1 : ℂ) := by
    calc
      Q.val = ∑ e ∈ Q.val.support, MvPolynomial.coeff e Q.val •
          MvPolynomial.monomial e (1 : ℂ) := by
        simpa only [MvPolynomial.smul_monomial, smul_eq_mul, mul_one] using Q.val.as_sum
      _ = ∑ e ∈ s, MvPolynomial.coeff e Q.val • MvPolynomial.monomial e (1 : ℂ) := by
        apply Finset.sum_subset
        · intro e he
          have hdeg := Q.property (MvPolynomial.mem_support_iff.mp he)
          simpa [s, Finsupp.degree_eq_weight_one, Pi.one_def] using hdeg
        · intro e _ he
          simp [MvPolynomial.notMem_support_iff.mp he]
  have hcoeff (Q : ↥(HeckeEis.BinaryForm ℂ n)) (d : Fin 2 →₀ ℕ) :
      MvPolynomial.coeff d (ρ γ Q).val =
        ∑ e ∈ s, MvPolynomial.coeff e Q.val *
          MvPolynomial.coeff d (HeckeEis.binarySubst ℂ γ
            (MvPolynomial.monomial e (1 : ℂ))) := by
    change MvPolynomial.coeff d (HeckeEis.binarySubst ℂ γ Q.val) = _
    conv_lhs => rw [hexpand Q]
    simp only [map_sum, map_smul, MvPolynomial.coeff_sum,
      MvPolynomial.coeff_smul, smul_eq_mul]
  have hrep (d : Fin 2 →₀ ℕ) : Filter.Tendsto
      (fun y : ℝ => MvPolynomial.coeff d (ρ γ (F (σ • ray 0 y))).val)
      Filter.atTop (nhds (MvPolynomial.coeff d (ρ γ A).val)) := by
    simp_rw [hcoeff]
    apply tendsto_finsetSum
    intro e _
    exact (hA 0 e).mul_const _
  have hdefect : A - ρ γ A = hF.cocycle γ := by
    apply Subtype.ext
    apply MvPolynomial.ext
    intro d
    have hlim := (hA (m : ℝ) d).sub (hrep d)
    have heq : (fun y : ℝ =>
        MvPolynomial.coeff d (F (σ • ray (m : ℝ) y)).val -
        MvPolynomial.coeff d (ρ γ (F (σ • ray 0 y))).val) =ᶠ[Filter.atTop]
        (fun _ => MvPolynomial.coeff d (hF.cocycle γ).val) := by
      filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with y hy
      have h := hF.sub_eq_cocycle γ (σ • ray 0 y)
      rw [hmove y hy] at h
      simpa only [Submodule.coe_sub, MvPolynomial.coeff_sub] using
        congrArg (fun Q : ↥(HeckeEis.BinaryForm ℂ n) => MvPolynomial.coeff d Q.val) h
    simpa only [Submodule.coe_sub, MvPolynomial.coeff_sub] using
      (tendsto_nhds_unique hlim (tendsto_const_nhds.congr' heq.symm))
  refine ⟨-A, ?_⟩
  change ρ γ (-A) - (-A) = hF.cocycle γ
  rw [map_neg, neg_sub_neg]
  exact hdefect

open Filter MeasureTheory Set
open scoped Topology

end Submission

/-- A primitive whose derivative decays on a vertical strip has one common limit,
with the polynomial-exponential tail bound throughout the strip. -/
theorem Submission.p02_es_177ebb5a_scl_scalar_strip_limit :
    ∀ (n : ℕ) (a D L y₀ : ℝ) (F H : ℂ → ℂ),
      0 < a → 0 ≤ D → 0 ≤ L → 1 ≤ y₀ →
      ContinuousOn H {z : ℂ | 0 < z.im} →
      (∀ z : ℂ, 0 < z.im → HasDerivAt F (H z) z) →
      (∀ z : ℂ, 0 ≤ z.re → z.re ≤ L → y₀ ≤ z.im →
        ‖H z‖ ≤ D * (1 + z.im) ^ n * Real.exp (-a * z.im)) →
      ∃ b : ℂ, ∀ z : ℂ, 0 ≤ z.re → z.re ≤ L → y₀ ≤ z.im →
        ‖F z - b‖ ≤
          (D * (∫ s in Set.Ioi (0 : ℝ), (1 + s) ^ n * Real.exp (-a * s))) *
            (1 + z.im) ^ n * Real.exp (-a * z.im) := by
  intro n a D L y₀ F H ha hD hL hy₀ hH hF hbound
  let w : ℝ → ℝ := fun y => (1 + y) ^ n * Real.exp (-a * y)
  let J : ℝ := ∫ s in Set.Ioi (0 : ℝ), w s
  -- Keep the weight estimates local to the approved dependency boundary.
  -- Pinned mathlib: Pow/Asymptotics.isLittleO_pow_exp_pos_mul_atTop and
  -- Integral/ExpDecay.integrable_of_isBigO_exp_neg supply decay and integrability.
  have hdecay_rate (b : ℝ) (hb : 0 < b) :
      Filter.Tendsto (fun y : ℝ => (1 + y) ^ n * Real.exp (-b * y))
        Filter.atTop (nhds 0) := by
    have h := ((isLittleO_pow_exp_pos_mul_atTop n hb).tendsto_div_nhds_zero.comp
      (Filter.tendsto_atTop_add_const_left Filter.atTop 1 Filter.tendsto_id)).mul_const
        (Real.exp b)
    simp only [zero_mul] at h
    convert h using 1
    ext y
    simp only [Function.comp_apply, id_eq]
    rw [div_eq_mul_inv, ← Real.exp_neg, mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have hdecay := hdecay_rate a ha
  have hw_cont : Continuous w := by fun_prop
  have hw_nonneg (s : ℝ) (hs : 0 ≤ s) : 0 ≤ w s := by
    dsimp [w]
    positivity
  have hint : MeasureTheory.IntegrableOn w (Set.Ioi 0) := by
    apply integrable_of_isBigO_exp_neg (half_pos ha) hw_cont.continuousOn
    apply Asymptotics.IsLittleO.isBigO
    apply Asymptotics.isLittleO_of_tendsto (fun x hx => (Real.exp_ne_zero _ hx).elim)
    convert hdecay_rate (a / 2) (half_pos ha) using 1
    ext s
    dsimp [w]
    rw [div_eq_mul_inv, ← Real.exp_neg, mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have htail (y t : ℝ) (hy : 0 ≤ y) (hyt : y ≤ t) :
      (∫ s in y..t, w s) ≤ J * w y := by
    have hty : 0 ≤ t - y := sub_nonneg.mpr hyt
    have hsub (v : ℝ) (hv : 0 ≤ v) : w (y + v) ≤ w y * w v := by
      have hp : (1 + (y + v)) ^ n ≤ ((1 + y) * (1 + v)) ^ n :=
        pow_le_pow_left₀ (by positivity) (by nlinarith [mul_nonneg hy hv]) n
      dsimp [w]
      calc
        (1 + (y + v)) ^ n * Real.exp (-a * (y + v)) ≤
            ((1 + y) * (1 + v)) ^ n * Real.exp (-a * (y + v)) :=
          mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
        _ = ((1 + y) ^ n * Real.exp (-a * y)) *
            ((1 + v) ^ n * Real.exp (-a * v)) := by
          rw [mul_pow, show -a * (y + v) = -a * y + -a * v by ring, Real.exp_add]
          ring
    have hfinite : (∫ v in (0 : ℝ)..t - y, w v) ≤ J := by
      rw [intervalIntegral.integral_of_le hty]
      apply MeasureTheory.setIntegral_mono_set hint
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with v hv
        exact hw_nonneg v hv.le
      · exact Filter.Eventually.of_forall (fun v hv => hv.1)
    calc
      (∫ s in y..t, w s) = ∫ v in (0 : ℝ)..t - y, w (y + v) := by
        rw [intervalIntegral.integral_comp_add_left]
        simp
      _ ≤ ∫ v in (0 : ℝ)..t - y, w y * w v := by
        apply intervalIntegral.integral_mono_on hty
          ((hw_cont.comp (continuous_const.add continuous_id)).intervalIntegrable _ _)
          ((continuous_const.mul hw_cont).intervalIntegrable _ _)
        intro v hv
        exact hsub v hv.1
      _ = w y * ∫ v in (0 : ℝ)..t - y, w v := intervalIntegral.integral_const_mul _ _
      _ ≤ w y * J := mul_le_mul_of_nonneg_left hfinite (hw_nonneg y hy)
      _ = J * w y := mul_comm _ _
  have hw : Continuous (fun y => D * w y) := continuous_const.mul hw_cont
  obtain ⟨hvertical, hhorizontal⟩ :=
    Submission.p02_es_177ebb5a_ssl_segment_estimates F H (fun y => D * w y) L y₀
      hL (by linarith) hH hF hw.continuousOn (by
        intro z hx hxL hy
        simpa only [w, mul_assoc] using hbound z hx hxL hy)
  have herror : Filter.Tendsto (fun y => (D * J) * w y) Filter.atTop (nhds 0) := by
    simpa only [mul_zero] using hdecay.const_mul (D * J)
  -- The vertical segment estimate gives a limit and its tail bound on each vertical line.
  have hlimit (x : ℝ) (hx : 0 ≤ x) (hxL : x ≤ L) :
      ∃ b : ℂ,
        Filter.Tendsto (fun y : ℝ => F ((x : ℂ) + (y : ℂ) * Complex.I))
          Filter.atTop (nhds b) ∧
        ∀ y : ℝ, y₀ ≤ y →
          ‖F ((x : ℂ) + (y : ℂ) * Complex.I) - b‖ ≤ (D * J) * w y := by
    apply Submission.p02_es_177ebb5a_ssl_tail_limit _ _ y₀ herror
    intro y t hy hyt
    calc
      ‖F ((x : ℂ) + (t : ℂ) * Complex.I) -
          F ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤
          ∫ s in y..t, D * w s := hvertical x y t hx hxL hy hyt
      _ = D * ∫ s in y..t, w s := intervalIntegral.integral_const_mul _ _
      _ ≤ D * (J * w y) :=
        mul_le_mul_of_nonneg_left (htail y t (by linarith) hyt) hD
      _ = (D * J) * w y := (mul_assoc _ _ _).symm
  obtain ⟨b, hb, _⟩ := hlimit 0 le_rfl hL
  refine ⟨b, ?_⟩
  intro z hx hxL hy
  obtain ⟨bx, hbx, hbx_bound⟩ := hlimit z.re hx hxL
  -- Horizontal differences vanish, so every vertical limit agrees with that at x = 0.
  have hbzero : Filter.Tendsto (fun y : ℝ => F ((y : ℂ) * Complex.I))
      Filter.atTop (nhds b) := by simpa only [Complex.ofReal_zero, zero_add] using hb
  have hhorizontal_decay : Filter.Tendsto (fun y => z.re * (D * w y))
      Filter.atTop (nhds 0) := by
    simpa only [mul_zero] using (hdecay.const_mul D).const_mul z.re
  have hnorm : ‖bx - b‖ ≤ 0 :=
    le_of_tendsto_of_tendsto (hbx.sub hbzero).norm hhorizontal_decay
      ((Filter.eventually_ge_atTop y₀).mono fun y hy => hhorizontal z.re y hx hxL hy)
  have heq : bx = b := sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hnorm (norm_nonneg _)))
  have hz := hbx_bound z.im hy
  rw [heq, Complex.re_add_im] at hz
  simpa only [w, J, mul_assoc] using hz
namespace Submission

theorem p02_es_177ebb5a_sm_transformed_integral
    (n : ℕ) (h : UpperHalfPlane → ℂ)
    (E : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n))
    (σ : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (hE : HeckeEis.IsEichlerIntegral n h E) :
    HeckeEis.IsEichlerIntegral n (SlashAction.map ((n : ℤ) + 2) σ h)
      (fun τ : UpperHalfPlane =>
        ((HeckeEis.binaryFormRepSL ℂ n) σ⁻¹) (E (σ • τ))) := by
  intro e τ
  have hderiv := p02_es_177ebb5a_ic_linear_mobius_derivative n
    ((HeckeEis.binaryFormRepSL ℂ n) σ⁻¹) E
    (h (σ • τ) • HeckeEis.linePow n ((σ • τ : UpperHalfPlane) : ℂ)) σ τ
    (fun d => by
      simpa only [Submodule.coe_smul, MvPolynomial.coeff_smul, smul_eq_mul] using
        hE d (σ • τ)) e
  rw [map_smul, p02_es_177ebb5a_ic_inverse_linepow, Submodule.coe_smul,
    MvPolynomial.coeff_smul, Submodule.coe_smul, MvPolynomial.coeff_smul,
    smul_eq_mul, smul_eq_mul] at hderiv
  convert hderiv using 1
  have hdenom := HeckeEis.jFactor_eq_denom σ τ
  rw [Matrix.SpecialLinearGroup.mapGL, MonoidHom.comp_apply,
    show algebraMap ℤ ℝ = Int.castRingHom ℝ from rfl] at hdenom
  rw [ModularForm.SL_slash_apply, ← hdenom]
  rw [show (n : ℤ) + 2 = ((n + 2 : ℕ) : ℤ) by norm_cast,
    zpow_neg, zpow_natCast, pow_add, mul_inv_rev, div_eq_mul_inv]
  ring

theorem p02_es_177ebb5a_sd_jet_recurrence :
    ∀ (n : ℕ) (h : UpperHalfPlane → ℂ)
      (E : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n)),
      HeckeEis.IsEichlerIntegral n h E → ∀ (r : ℕ), r ≤ n → ∀ τ : UpperHalfPlane,
      HasDerivAt
        (fun z : ℂ => MvPolynomial.eval (fun j : Fin 2 => if j = 0 then 1 else -z)
          ((fun p : MvPolynomial (Fin 2) ℂ => MvPolynomial.pderiv (1 : Fin 2) p)^[r]
            (E (UpperHalfPlane.ofComplex z)).val))
        (if r = n then (Nat.factorial n : ℂ) * h τ
          else -MvPolynomial.eval (fun j : Fin 2 => if j = 0 then 1 else -(τ : ℂ))
            ((fun p : MvPolynomial (Fin 2) ℂ => MvPolynomial.pderiv (1 : Fin 2) p)^[r + 1]
              (E τ).val))
        (τ : ℂ) := by
  intro n h E hE r hr τ
  have hderiv := Submission.p02_es_177ebb5a_sd_jr_moving_eval_derivative n
    (fun z : ℂ => E (UpperHalfPlane.ofComplex z)) (HeckeEis.linePow n (τ : ℂ))
    (h τ) (τ : ℂ) (fun d => hE d τ) r hr
  rw [UpperHalfPlane.ofComplex_apply,
    p02_es_177ebb5a_sd_jr_linepow_eval n r hr (τ : ℂ)] at hderiv
  by_cases htop : r = n
  · subst r
    simpa [p02_es_177ebb5a_sd_jr_homogeneous_nilpotence, mul_comm] using hderiv
  · simpa only [if_neg htop, mul_zero, zero_sub] using hderiv


end Submission

namespace Submission

/-- The coefficients of an Eichler integral have a common limit on a finite strip,
with a uniform polynomial-exponential error bound. -/
theorem p02_es_177ebb5a_tb_strip_coefficient_limit :
    ∀ (n : ℕ) (u : UpperHalfPlane → ℂ)
      (G : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n)) (a C Y L : ℝ),
      0 < a → 0 ≤ C → 0 ≤ L → Continuous u → HeckeEis.IsEichlerIntegral n u G →
      (∀ τ : UpperHalfPlane, Y ≤ τ.im → ‖u τ‖ ≤ C * Real.exp (-a * τ.im)) →
      ∃ (A : ↥(HeckeEis.BinaryForm ℂ n)) (K : ℝ), 0 ≤ K ∧
        ∀ τ : UpperHalfPlane, 0 ≤ τ.re → τ.re ≤ L → max 1 Y ≤ τ.im →
          ∀ d : Fin 2 →₀ ℕ,
            ‖MvPolynomial.coeff d ((G τ).val - A.val)‖ ≤
              K * (1 + τ.im) ^ n * Real.exp (-a * τ.im) := by
  classical
  intro n u G a C Y L ha hC hL hu hG hubound
  let D := C * (2 : ℝ) ^ n * (L + 1) ^ n
  let J := ∫ s in Set.Ioi (0 : ℝ), (1 + s) ^ n * Real.exp (-a * s)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hJ : 0 ≤ J := (p02_es_177ebb5a_scl_polynomial_exp_tail n a ha).2.1
  -- Each coefficient of the line power is a scalar polynomial in z.
  have hline_cont (d : Fin 2 →₀ ℕ) :
      Continuous (fun z : ℂ => MvPolynomial.coeff d (HeckeEis.linePow n z).val) := by
    have hformula (z : ℂ) :
        MvPolynomial.coeff d (HeckeEis.linePow n z).val =
          if d.sum (fun _ m ↦ m) = n then (d.multinomial : ℂ) * z ^ d 0 else 0 := by
      have h := MvPolynomial.coeff_linearCombination_X_pow_of_fintype
        (fun j : Fin 2 ↦ if j = 0 then z else (1 : ℂ)) d n
      simp only [Fin.sum_univ_two, Fin.isValue, ite_true, one_ne_zero, ite_false,
        MvPolynomial.smul_eq_C_mul, map_one, one_mul] at h
      change MvPolynomial.coeff d
        ((MvPolynomial.C z * MvPolynomial.X 0 + MvPolynomial.X 1) ^ n) = _
      rw [h, d.prod_fintype _ (by simp)]
      simp
    simp_rw [hformula]
    split_ifs <;> fun_prop
  -- Apply the scalar strip theorem with the same majorant for every coefficient.
  have hscalar (d : Fin 2 →₀ ℕ) : ∃ b : ℂ,
      ∀ z : ℂ, 0 ≤ z.re → z.re ≤ L → max 1 Y ≤ z.im →
        ‖MvPolynomial.coeff d (G (UpperHalfPlane.ofComplex z)).val - b‖ ≤
          (D * J) * (1 + z.im) ^ n * Real.exp (-a * z.im) := by
    apply p02_es_177ebb5a_scl_scalar_strip_limit n a D L (max 1 Y)
      (fun z => MvPolynomial.coeff d (G (UpperHalfPlane.ofComplex z)).val)
      (fun z => u (UpperHalfPlane.ofComplex z) *
        MvPolynomial.coeff d (HeckeEis.linePow n z).val)
      ha hD hL (le_max_left 1 Y)
    · intro z hz
      exact ((hu.continuousAt.comp
        (UpperHalfPlane.mdifferentiableAt_ofComplex hz).continuousAt).mul
          (hline_cont d).continuousAt).continuousWithinAt
    · intro z hz
      simpa only [UpperHalfPlane.ofComplex_apply_of_im_pos hz] using hG d ⟨z, hz⟩
    · intro z hx hxL hy
      have hy1 : 1 ≤ z.im := (le_max_left 1 Y).trans hy
      have hy0 : 0 ≤ z.im := by linarith
      have hz : 0 < z.im := by linarith
      have hum : ‖u (UpperHalfPlane.ofComplex z)‖ ≤ C * Real.exp (-a * z.im) := by
        simpa only [UpperHalfPlane.ofComplex_apply_of_im_pos hz, UpperHalfPlane.im] using
          hubound ⟨z, hz⟩ ((le_max_right 1 Y).trans hy)
      have hnorm : max 1 ‖z‖ ≤ (L + 1) * (1 + z.im) := by
        apply max_le
        · nlinarith [mul_nonneg hL hy0]
        · have hzbound := Complex.norm_le_abs_re_add_abs_im z
          rw [abs_of_nonneg hx, abs_of_nonneg hy0] at hzbound
          nlinarith [mul_nonneg hL hy0]
      calc
        ‖u (UpperHalfPlane.ofComplex z) *
            MvPolynomial.coeff d (HeckeEis.linePow n z).val‖ =
            ‖u (UpperHalfPlane.ofComplex z)‖ *
              ‖MvPolynomial.coeff d (HeckeEis.linePow n z).val‖ := norm_mul _ _
        _ ≤ (C * Real.exp (-a * z.im)) * ((2 : ℝ) ^ n * (max 1 ‖z‖) ^ n) :=
          mul_le_mul hum (p02_es_177ebb5a_scl_linepow_coeff_bound n z d)
            (norm_nonneg _) (by positivity)
        _ ≤ (C * Real.exp (-a * z.im)) *
            ((2 : ℝ) ^ n * ((L + 1) * (1 + z.im)) ^ n) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀ (by positivity) hnorm n) (by positivity)) (by positivity)
        _ = D * (1 + z.im) ^ n * Real.exp (-a * z.im) := by
          dsimp [D]
          rw [mul_pow]
          ring
  choose b hb using hscalar
  -- Only degree-n exponents are used in the limiting homogeneous polynomial.
  let s := (Finsupp.finite_of_degree_eq (σ := Fin 2) n).toFinset
  have hs (d : Fin 2 →₀ ℕ) : d ∈ s ↔ d.degree = n := by simp [s]
  let A : ↥(HeckeEis.BinaryForm ℂ n) :=
    ⟨∑ d ∈ s, MvPolynomial.monomial d (b d), by
      apply MvPolynomial.IsHomogeneous.sum
      intro d hd
      exact MvPolynomial.isHomogeneous_monomial (b d) ((hs d).mp hd)⟩
  have hA (d : Fin 2 →₀ ℕ) (hd : d ∈ s) : MvPolynomial.coeff d A.val = b d := by
    simp [A, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, hd]
  refine ⟨A, D * J, mul_nonneg hD hJ, ?_⟩
  intro τ hx hxL hy d
  rw [MvPolynomial.coeff_sub]
  by_cases hd : d ∈ s
  · rw [hA d hd]
    simpa only [UpperHalfPlane.ofComplex_apply, UpperHalfPlane.im] using
      hb d (τ : ℂ) hx hxL hy
  · have hdeg : d.degree ≠ n := by simpa only [hs d] using hd
    rw [(G τ).property.coeff_eq_zero hdeg, A.property.coeff_eq_zero hdeg,
      sub_self, norm_zero]
    have hy0 : 0 ≤ τ.im := τ.im_pos.le
    positivity

end Submission

namespace Submission

theorem p02_es_177ebb5a_scalarization_derivative :
    ∀ (n : ℕ) (h : UpperHalfPlane → ℂ)
      (E : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n)),
      DifferentiableOn ℂ (fun z : ℂ => h (UpperHalfPlane.ofComplex z))
        {z : ℂ | 0 < z.im} →
      HeckeEis.IsEichlerIntegral n h E → ∀ τ : UpperHalfPlane,
      iteratedDeriv (n + 1)
          (fun z : ℂ => MvPolynomial.eval (fun j : Fin 2 => if j = 0 then 1 else -z)
            (E (UpperHalfPlane.ofComplex z)).val) (τ : ℂ) =
        ((-1 : ℂ) ^ n * (Nat.factorial n : ℂ)) * h τ := by
  intro n h E _hh hE τ
  let Q : ℕ → ℂ → ℂ := fun r z =>
    MvPolynomial.eval (fun j : Fin 2 => if j = 0 then 1 else -z)
      ((fun p : MvPolynomial (Fin 2) ℂ => MvPolynomial.pderiv (1 : Fin 2) p)^[r]
        (E (UpperHalfPlane.ofComplex z)).val)
  have hrec : ∀ r < n, ∀ z ∈ {z : ℂ | 0 < z.im},
      HasDerivAt (Q r) (-Q (r + 1) z) z := by
    intro r hr z hz
    simpa only [Q, if_neg (Nat.ne_of_lt hr), UpperHalfPlane.ofComplex_apply_of_im_pos hz]
      using p02_es_177ebb5a_sd_jet_recurrence n h E hE r (Nat.le_of_lt hr) ⟨z, hz⟩
  have htop : ∀ z ∈ {z : ℂ | 0 < z.im},
      HasDerivAt (Q n) ((Nat.factorial n : ℂ) * h (UpperHalfPlane.ofComplex z)) z := by
    intro z hz
    simpa [Q, UpperHalfPlane.ofComplex_apply_of_im_pos hz]
      using p02_es_177ebb5a_sd_jet_recurrence n h E hE n le_rfl ⟨z, hz⟩
  have hresult := p02_es_177ebb5a_sd_open_ladder {z : ℂ | 0 < z.im} n Q
    (fun z => (Nat.factorial n : ℂ) * h (UpperHalfPlane.ofComplex z))
    UpperHalfPlane.isOpen_upperHalfPlaneSet hrec htop (τ : ℂ) τ.im_pos
  simpa [Q, mul_assoc] using hresult

end Submission

theorem Submission.p02_es_177ebb5a_ssl_segment_estimates :
    ∀ (F H : ℂ → ℂ) (w : ℝ → ℝ) (L y₀ : ℝ),
      0 ≤ L → 0 < y₀ → ContinuousOn H {z : ℂ | 0 < z.im} →
      (∀ z : ℂ, 0 < z.im → HasDerivAt F (H z) z) →
      ContinuousOn w (Set.Ici y₀) →
      (∀ z : ℂ, 0 ≤ z.re → z.re ≤ L → y₀ ≤ z.im → ‖H z‖ ≤ w z.im) →
      (∀ (x y t : ℝ), 0 ≤ x → x ≤ L → y₀ ≤ y → y ≤ t →
        ‖F ((x : ℂ) + (t : ℂ) * Complex.I) -
          F ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤ ∫ s in y..t, w s) ∧
      (∀ (x y : ℝ), 0 ≤ x → x ≤ L → y₀ ≤ y →
        ‖F ((x : ℂ) + (y : ℂ) * Complex.I) - F ((y : ℂ) * Complex.I)‖ ≤
          x * w y) := by
  intro F H w L y₀ _hL hy₀ hH hF hw hbound
  constructor
  · intro x y t hx hxL hy hyt
    have hpath : Continuous (fun s : ℝ => (x : ℂ) + (s : ℂ) * Complex.I) := by
      fun_prop
    have hupper (s : ℝ) (hs : s ∈ Set.uIcc y t) :
        0 < ((x : ℂ) + (s : ℂ) * Complex.I).im := by
      have hys : y ≤ s := (Set.uIcc_of_le hyt ▸ hs).1
      simpa using hy₀.trans_le (hy.trans hys)
    have hderiv (s : ℝ) (hs : s ∈ Set.uIcc y t) :
        HasDerivAt (fun u : ℝ => F ((x : ℂ) + (u : ℂ) * Complex.I))
          (H ((x : ℂ) + (s : ℂ) * Complex.I) * Complex.I) s := by
      have hp : HasDerivAt (fun z : ℂ => (x : ℂ) + z * Complex.I) Complex.I
          (s : ℂ) := by
        simpa using ((hasDerivAt_id (s : ℂ)).mul_const Complex.I).const_add (x : ℂ)
      exact ((hF _ (hupper s hs)).comp (s : ℂ) hp).comp_ofReal
    have hint : IntervalIntegrable
        (fun s : ℝ => H ((x : ℂ) + (s : ℂ) * Complex.I) * Complex.I)
        MeasureTheory.volume y t :=
      ((hH.comp hpath.continuousOn (fun s hs => hupper s hs)).mul_const
        Complex.I).intervalIntegrable
    rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
    apply intervalIntegral.norm_integral_le_of_norm_le hyt
    · apply Filter.Eventually.of_forall
      intro s hs
      have hys : y₀ ≤ s := hy.trans hs.1.le
      simpa using hbound ((x : ℂ) + (s : ℂ) * Complex.I)
        (by simpa using hx) (by simpa using hxL) (by simpa using hys)
    · apply (hw.mono ?_).intervalIntegrable
      intro s hs
      exact hy.trans (Set.uIcc_of_le hyt ▸ hs).1
  · intro x y hx hxL hy
    have hpath : Continuous (fun s : ℝ => (s : ℂ) + (y : ℂ) * Complex.I) := by
      fun_prop
    have hupper (s : ℝ) : 0 < ((s : ℂ) + (y : ℂ) * Complex.I).im := by
      simpa using hy₀.trans_le hy
    have hderiv (s : ℝ) (_hs : s ∈ Set.uIcc 0 x) :
        HasDerivAt (fun u : ℝ => F ((u : ℂ) + (y : ℂ) * Complex.I))
          (H ((s : ℂ) + (y : ℂ) * Complex.I)) s := by
      simpa only [mul_one] using!
        ((hF _ (hupper s)).comp (s : ℂ)
          ((hasDerivAt_id (s : ℂ)).add_const ((y : ℂ) * Complex.I))).comp_ofReal
    have hint : IntervalIntegrable
        (fun s : ℝ => H ((s : ℂ) + (y : ℂ) * Complex.I))
        MeasureTheory.volume 0 x :=
      (hH.comp hpath.continuousOn (fun s _ => hupper s)).intervalIntegrable
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
    simp only [Complex.ofReal_zero, zero_add] at hFTC
    rw [← hFTC]
    calc
      _ ≤ w y * |x - 0| := intervalIntegral.norm_integral_le_of_norm_le_const (by
        intro s hs
        have hs' : s ∈ Set.Ioc 0 x := Set.uIoc_of_le hx ▸ hs
        simpa using hbound ((s : ℂ) + (y : ℂ) * Complex.I)
          (by simpa using hs'.1.le) (by simpa using hs'.2.trans hxL)
          (by simpa using hy))
      _ = x * w y := by rw [sub_zero, abs_of_nonneg hx, mul_comm]
