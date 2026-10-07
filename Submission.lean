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

end Submission
