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

/-- Each output coefficient of a linear map is a fixed linear combination of input coefficients. -/
theorem Submission.p02_es_177ebb5a_ic_lct_coeff_linear_combination
    (n : ℕ) (A : ↥(HeckeEis.BinaryForm ℂ n) →ₗ[ℂ] ↥(HeckeEis.BinaryForm ℂ n))
    (e : Fin 2 →₀ ℕ) :
    ∃ c : Fin (n + 1) → ℂ, ∀ Q : ↥(HeckeEis.BinaryForm ℂ n),
      MvPolynomial.coeff e (A Q).val = ∑ r : Fin (n + 1), c r *
        MvPolynomial.coeff (Finsupp.single (0 : Fin 2) r.val +
          Finsupp.single (1 : Fin 2) (n - r.val)) Q.val := by
  classical
  let exponent (r : Fin (n + 1)) : Fin 2 →₀ ℕ :=
    Finsupp.single 0 r.val + Finsupp.single 1 (n - r.val)
  have hdegree (r : Fin (n + 1)) : (exponent r).degree = n := by
    simp only [exponent, map_add, Finsupp.degree_single]
    exact Nat.add_sub_of_le (Nat.le_of_lt_succ r.isLt)
  let b (r : Fin (n + 1)) : ↥(HeckeEis.BinaryForm ℂ n) :=
    ⟨MvPolynomial.monomial (exponent r) (1 : ℂ),
      MvPolynomial.isHomogeneous_monomial 1 (hdegree r)⟩
  refine ⟨fun r => MvPolynomial.coeff e (A (b r)).val, ?_⟩
  intro Q
  have hQ : Q = ∑ r : Fin (n + 1), MvPolynomial.coeff (exponent r) Q.val • b r := by
    apply Subtype.ext
    simpa [b, exponent] using Submission.p02_es_177ebb5a_ic_lct_monomial_expansion n Q
  let L : ↥(HeckeEis.BinaryForm ℂ n) →ₗ[ℂ] ℂ :=
    (MvPolynomial.lcoeff ℂ e).comp ((HeckeEis.BinaryForm ℂ n).subtype.comp A)
  change L Q = ∑ r : Fin (n + 1), L (b r) * MvPolynomial.coeff (exponent r) Q.val
  calc
    L Q = L (∑ r : Fin (n + 1), MvPolynomial.coeff (exponent r) Q.val • b r) :=
      congrArg L hQ
    _ = ∑ r : Fin (n + 1), L (b r) * MvPolynomial.coeff (exponent r) Q.val := by
      simp only [map_sum, map_smul, smul_eq_mul, mul_comm]

/-- A linear map of binary forms preserves coefficientwise derivatives. -/
theorem Submission.p02_es_177ebb5a_ic_lmd_linear_coeff
    (n : ℕ) (A : ↥(HeckeEis.BinaryForm ℂ n) →ₗ[ℂ] ↥(HeckeEis.BinaryForm ℂ n))
    (F : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n))
    (P : ↥(HeckeEis.BinaryForm ℂ n)) (τ : UpperHalfPlane) :
    (∀ d : Fin 2 →₀ ℕ,
      HasDerivAt (fun z : ℂ => MvPolynomial.coeff d (F (UpperHalfPlane.ofComplex z)).val)
        (MvPolynomial.coeff d P.val) (τ : ℂ)) →
    ∀ e : Fin 2 →₀ ℕ,
      HasDerivAt (fun z : ℂ => MvPolynomial.coeff e (A (F (UpperHalfPlane.ofComplex z))).val)
        (MvPolynomial.coeff e (A P).val) (τ : ℂ) := by
  intro h e
  obtain ⟨c, hc⟩ := Submission.p02_es_177ebb5a_ic_lct_coeff_linear_combination n A e
  simp_rw [hc]
  exact HasDerivAt.fun_sum fun r _ => (h _).const_mul (c r)
