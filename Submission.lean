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

end Submission
