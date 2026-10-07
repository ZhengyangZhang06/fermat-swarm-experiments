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

end Submission
