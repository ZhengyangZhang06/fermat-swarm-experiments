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

theorem p02_es_177ebb5a_lcd_monomial_expansion
    (n : ℕ) (Q : ↥(HeckeEis.BinaryForm ℂ n)) :
    Q.val = ∑ r : Fin (n + 1),
      MvPolynomial.coeff
          (Finsupp.single (0 : Fin 2) r.val + Finsupp.single (1 : Fin 2) (n - r.val))
          Q.val •
        MvPolynomial.monomial
          (Finsupp.single (0 : Fin 2) r.val + Finsupp.single (1 : Fin 2) (n - r.val))
          (1 : ℂ) := by
  classical
  let e (r : Fin (n + 1)) : Fin 2 →₀ ℕ :=
    Finsupp.single 0 r.val + Finsupp.single 1 (n - r.val)
  have he (r : Fin (n + 1)) : (e r).degree = n := by
    simp [e, Finsupp.degree_eq_sum, Fin.sum_univ_two,
      Nat.add_sub_of_le (Nat.le_of_lt_succ r.isLt)]
  change Q.val = ∑ r, MvPolynomial.coeff (e r) Q.val •
    MvPolynomial.monomial (e r) (1 : ℂ)
  apply MvPolynomial.ext
  intro d
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_smul, MvPolynomial.coeff_monomial]
  by_cases hd : d.degree = n
  · have hsum : d 0 + d 1 = n := by
      simpa [Finsupp.degree_eq_sum, Fin.sum_univ_two] using hd
    let r : Fin (n + 1) := ⟨d 0, by omega⟩
    have hr : e r = d := by
      ext i
      fin_cases i <;> simp [e, r, ← hsum]
    have huniq (s : Fin (n + 1)) (hs : e s = d) : s = r := by
      apply Fin.ext
      have hzero := congrArg (fun t : Fin 2 →₀ ℕ => t 0) hs
      simpa [e, r] using hzero
    rw [Finset.sum_eq_single r]
    · simp [hr]
    · intro s _ hs
      have hne : e s ≠ d := fun h => hs (huniq s h)
      simp [hne]
    · simp
  · rw [MvPolynomial.IsHomogeneous.coeff_eq_zero Q.property hd]
    symm
    apply Finset.sum_eq_zero
    intro r _
    have hne : e r ≠ d := fun h => hd (h ▸ he r)
    simp [hne]

theorem p02_es_177ebb5a_lcd_coeff_linear_combination
    (n : ℕ)
    (A : ↥(HeckeEis.BinaryForm ℂ n) →ₗ[ℂ] ↥(HeckeEis.BinaryForm ℂ n))
    (e : Fin 2 →₀ ℕ) :
    ∃ c : Fin (n + 1) → ℂ, ∀ Q : ↥(HeckeEis.BinaryForm ℂ n),
      MvPolynomial.coeff e (A Q).val = ∑ r : Fin (n + 1),
        c r * MvPolynomial.coeff
          (Finsupp.single (0 : Fin 2) r.val + Finsupp.single (1 : Fin 2) (n - r.val))
          Q.val := by
  classical
  let d (r : Fin (n + 1)) : Fin 2 →₀ ℕ :=
    Finsupp.single 0 r.val + Finsupp.single 1 (n - r.val)
  have hd (r : Fin (n + 1)) : (d r).degree = n := by
    simp [d, Finsupp.degree_eq_sum, Fin.sum_univ_two,
      Nat.add_sub_of_le (Nat.le_of_lt_succ r.isLt)]
  let b (r : Fin (n + 1)) : ↥(HeckeEis.BinaryForm ℂ n) :=
    ⟨MvPolynomial.monomial (d r) 1, MvPolynomial.isHomogeneous_monomial 1 (hd r)⟩
  refine ⟨fun r => MvPolynomial.coeff e (A (b r)).val, ?_⟩
  intro Q
  have hexpand : Q = ∑ r, MvPolynomial.coeff (d r) Q.val • b r := by
    apply Subtype.ext
    simp only [Submodule.coe_sum, Submodule.coe_smul]
    apply MvPolynomial.ext
    intro t
    simp only [b, MvPolynomial.coeff_sum, MvPolynomial.coeff_smul,
      MvPolynomial.coeff_monomial]
    by_cases ht : t.degree = n
    · have hsum : t 0 + t 1 = n := by
        simpa [Finsupp.degree_eq_sum, Fin.sum_univ_two] using ht
      let r : Fin (n + 1) := ⟨t 0, by omega⟩
      have hr : d r = t := by
        ext i
        fin_cases i <;> simp [d, r, ← hsum]
      have huniq (s : Fin (n + 1)) (hs : d s = t) : s = r := by
        apply Fin.ext
        have hzero := congrArg (fun u : Fin 2 →₀ ℕ => u 0) hs
        simpa [d, r] using hzero
      rw [Finset.sum_eq_single r]
      · simp [hr]
      · intro s _ hs
        have hne : d s ≠ t := fun h => hs (huniq s h)
        simp [hne]
      · simp
    · rw [MvPolynomial.IsHomogeneous.coeff_eq_zero Q.property ht]
      symm
      apply Finset.sum_eq_zero
      intro r _
      have hne : d r ≠ t := fun h => ht (h ▸ hd r)
      simp [hne]
  calc
    MvPolynomial.coeff e (A Q).val =
        MvPolynomial.coeff e (A (∑ r, MvPolynomial.coeff (d r) Q.val • b r)).val :=
      congrArg (fun P => MvPolynomial.coeff e (A P).val) hexpand
    _ = ∑ r, MvPolynomial.coeff e (A (b r)).val * MvPolynomial.coeff (d r) Q.val := by
      simp [map_sum, MvPolynomial.coeff_sum, mul_comm]

end Submission
