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

theorem p02_es_177ebb5a_tff_constant_dehomogenization
    (n : ℕ) (A : ↥(HeckeEis.BinaryForm ℂ n)) (α : ℂ)
    (hA : MvPolynomial.eval₂ Polynomial.C
      (fun j : Fin 2 => if j = 0 then 1 else Polynomial.X) A.val = Polynomial.C α) :
    A.val = MvPolynomial.C α * MvPolynomial.X (0 : Fin 2) ^ n := by
  classical
  have hdegree (d : Fin 2 →₀ ℕ) (hd : d ∈ A.val.support) : d 0 + d 1 = n := by
    have h := A.property (MvPolynomial.mem_support_iff.mp hd)
    have hdeg : d.degree = n := by
      simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using h
    simpa only [Finsupp.degree_eq_sum, Fin.sum_univ_two] using hdeg
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

end Submission
