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

end Submission
