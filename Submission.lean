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
