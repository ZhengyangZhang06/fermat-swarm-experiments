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

/-- A bound on one period strip gives a uniform bound for sufficiently large imaginary part. -/
theorem p02_es_177ebb5a_tb_periodic_strip_bound
    (N : ℕ) [NeZero N] (q : UpperHalfPlane → ℂ)
    (hperiod : ∀ τ : UpperHalfPlane, q ((ModularGroup.T ^ N) • τ) = q τ)
    (hstrip : ∃ M Y : ℝ, ∀ τ : UpperHalfPlane,
      0 ≤ τ.re → τ.re ≤ (N : ℝ) → Y ≤ τ.im → ‖q τ‖ ≤ M) :
    UpperHalfPlane.IsBoundedAtImInfty q := by
  obtain ⟨M, Y, hstrip⟩ := hstrip
  have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have htranslate (τ : UpperHalfPlane) : q ((N : ℝ) +ᵥ τ) = q τ := by
    simpa only [← zpow_natCast, UpperHalfPlane.modular_T_zpow_smul,
      Int.cast_natCast] using hperiod τ
  apply UpperHalfPlane.isBoundedAtImInfty_iff.mpr
  refine ⟨M, Y, ?_⟩
  intro τ hτ
  have hper : Function.Periodic (fun x : ℝ => q (x +ᵥ τ)) (N : ℝ) := by
    intro x
    simpa only [← add_vadd, add_comm] using htranslate (x +ᵥ τ)
  let m : ℤ := ⌊τ.re / (N : ℝ)⌋
  let τ' : UpperHalfPlane := (-(m : ℝ) * (N : ℝ)) +ᵥ τ
  have hre : τ'.re = τ.re - (m : ℝ) * N := by
    simp [τ', sub_eq_add_neg, add_comm]
  have hq : q τ' = q τ := by
    simpa only [τ', Int.cast_neg, zero_vadd] using hper.int_mul_eq (-m)
  rw [← hq]
  apply hstrip τ'
  · rw [hre]
    exact Int.sub_floor_div_mul_nonneg τ.re hN
  · rw [hre]
    exact (Int.sub_floor_div_mul_lt τ.re hN).le
  · simpa only [τ', UpperHalfPlane.vadd_im] using hτ

end Submission
