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

theorem p02_es_177ebb5a_pnf_primitive_kernel :
    ∀ M : Matrix (Fin 2) (Fin 2) ℤ, M.det = 0 →
      ∃ p q : ℤ, IsCoprime p q ∧ M.mulVec ![p, q] = 0 := by
  intro M hdet
  by_cases hM : M = 0
  · subst M
    exact ⟨1, 0, ⟨1, 0, by norm_num⟩, by simp⟩
  rw [Matrix.det_fin_two] at hdet
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
  have hg : 0 < Int.gcd x y := Int.gcd_pos_iff.mpr hxy
  obtain ⟨p, q, hpq, hx, hy⟩ := Int.exists_gcd_one hg
  refine ⟨p, q, Int.isCoprime_iff_gcd_eq_one.mpr hpq, ?_⟩
  have hg' : (Int.gcd x y : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hg)
  ext i
  simp only [Matrix.mulVec_apply_eq_sum, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Pi.zero_apply]
  apply (mul_eq_zero.mp (show
    (M i 0 * p + M i 1 * q) * (Int.gcd x y : ℤ) = 0 from ?_)).resolve_right hg'
  calc
    (M i 0 * p + M i 1 * q) * (Int.gcd x y : ℤ) =
        M i 0 * (p * (Int.gcd x y : ℤ)) + M i 1 * (q * (Int.gcd x y : ℤ)) := by ring
    _ = 0 := by rw [← hx, ← hy]; exact hker i

end Submission
