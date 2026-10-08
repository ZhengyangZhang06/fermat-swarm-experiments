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
  have hp : p ≠ 0 := by
    intro hp
    simp [hp] at hdegree
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

end Submission
