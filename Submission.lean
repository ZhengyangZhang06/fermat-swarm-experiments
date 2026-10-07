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

end Submission
