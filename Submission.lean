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

theorem p02_es_177ebb5a_sd_jr_homogeneous_nilpotence
    (n : ℕ) (P : ↥(HeckeEis.BinaryForm ℂ n)) :
    ((fun p : MvPolynomial (Fin 2) ℂ => MvPolynomial.pderiv (1 : Fin 2) p)^[n + 1]
      P.val) = 0 := by
  classical
  let D : Module.End ℂ (MvPolynomial (Fin 2) ℂ) :=
    (MvPolynomial.pderiv (1 : Fin 2)).toLinearMap
  have hmon (k : ℕ) (d : Fin 2 →₀ ℕ) (a : ℂ) (hd : d 1 < k) :
      (D ^ k) (MvPolynomial.monomial d a) = 0 := by
    induction k generalizing d a with
    | zero => omega
    | succ k ih =>
      rw [pow_succ, Module.End.mul_apply]
      change (D ^ k) (MvPolynomial.pderiv 1 (MvPolynomial.monomial d a)) = 0
      rw [MvPolynomial.pderiv_monomial]
      by_cases hzero : d 1 = 0
      · simp [hzero]
      · apply ih
        simp only [Finsupp.tsub_apply, Finsupp.single_eq_same]
        omega
  change (D : MvPolynomial (Fin 2) ℂ → MvPolynomial (Fin 2) ℂ)^[n + 1] P.val = 0
  rw [← Module.End.pow_apply, ← P.val.support_sum_monomial_coeff, map_sum]
  apply Finset.sum_eq_zero
  intro d hd
  apply hmon
  have hdegree : d.degree = n := by
    simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using
      P.property (MvPolynomial.mem_support_iff.mp hd)
  exact lt_of_le_of_lt ((Finsupp.le_degree 1 d).trans_eq hdegree) (Nat.lt_succ_self n)
theorem p02_es_177ebb5a_sd_jr_linepow_eval :
    ∀ (n r : ℕ), r ≤ n → ∀ t : ℂ,
      MvPolynomial.eval (fun j : Fin 2 => if j = 0 then 1 else -t)
        ((fun p : MvPolynomial (Fin 2) ℂ => MvPolynomial.pderiv (1 : Fin 2) p)^[r]
          (HeckeEis.linePow n t).val) =
        (if r = n then (Nat.factorial n : ℂ) else 0) := by
  intro n r hr t
  let L : MvPolynomial (Fin 2) ℂ := MvPolynomial.C t * MvPolynomial.X 0 +
    MvPolynomial.X 1
  have hD : MvPolynomial.pderiv (1 : Fin 2) L = 1 := by
    simp [L]
  -- Each derivative lowers the power and contributes the next descending factor.
  have hiter (s : ℕ) (hs : s ≤ n) :
      (fun p : MvPolynomial (Fin 2) ℂ => MvPolynomial.pderiv (1 : Fin 2) p)^[s]
        (L ^ n) = MvPolynomial.C (n.descFactorial s : ℂ) * L ^ (n - s) := by
    induction s with
    | zero => simp
    | succ s ih =>
      rw [Function.iterate_succ_apply', ih (by omega), MvPolynomial.pderiv_C_mul,
        MvPolynomial.pderiv_pow, hD, mul_one]
      simp only [Nat.descFactorial_succ, Nat.cast_mul, map_mul, map_natCast,
        Nat.sub_sub]
      ac_rfl
  have hEval : MvPolynomial.eval (fun j : Fin 2 => if j = 0 then 1 else -t) L = 0 := by
    simp [L]
  change MvPolynomial.eval _
    ((fun p : MvPolynomial (Fin 2) ℂ => MvPolynomial.pderiv (1 : Fin 2) p)^[r]
      (L ^ n)) = _
  rw [hiter r hr, map_mul, MvPolynomial.eval_C, map_pow, hEval]
  by_cases h : r = n
  · subst r
    simp [Nat.descFactorial_self]
  · have hnr : n - r ≠ 0 := by omega
    simp [h, zero_pow hnr]

end Submission

theorem Submission.p02_es_177ebb5a_med_js_iterated_monomial :
    ∀ (d : Fin 2 →₀ ℕ) (a : ℂ) (r : ℕ),
      ((fun p : MvPolynomial (Fin 2) ℂ => MvPolynomial.pderiv (1 : Fin 2) p)^[r]
        (MvPolynomial.monomial d a)) =
      MvPolynomial.monomial (d - Finsupp.single (1 : Fin 2) r)
        (a * (Nat.descFactorial (d 1) r : ℂ)) := by
  intro d a r
  induction r with
  | zero => simp
  | succ r ih =>
      rw [Function.iterate_succ_apply', ih, MvPolynomial.pderiv_monomial]
      have hexponent :
          d - Finsupp.single (1 : Fin 2) r - Finsupp.single (1 : Fin 2) 1 =
            d - Finsupp.single (1 : Fin 2) (r + 1) := by
        ext i
        by_cases hi : i = 1
        · subst i
          simp [Finsupp.tsub_apply, Nat.sub_sub]
        · simp [Finsupp.tsub_apply, Finsupp.single_eq_of_ne hi]
      rw [hexponent]
      simp only [Finsupp.tsub_apply, Finsupp.single_eq_same,
        Nat.descFactorial_succ, Nat.cast_mul]
      congr 1
      ring

theorem Submission.p02_es_177ebb5a_med_jet_sum :
    ∀ (n : ℕ) (P : ↥(HeckeEis.BinaryForm ℂ n)) (r : ℕ) (z : ℂ),
      MvPolynomial.eval (fun j : Fin 2 => if j = 0 then 1 else -z)
        ((fun p : MvPolynomial (Fin 2) ℂ => MvPolynomial.pderiv (1 : Fin 2) p)^[r]
          P.val) =
        ∑ k : Fin (n + 1),
          MvPolynomial.coeff
              (Finsupp.single (0 : Fin 2) (n - k.val) + Finsupp.single (1 : Fin 2) k.val)
              P.val *
            (Nat.descFactorial k.val r : ℂ) * (-z) ^ (k.val - r) := by
  classical
  intro n P r z
  let d (k : Fin (n + 1)) : Fin 2 →₀ ℕ :=
    Finsupp.single 0 (n - k.val) + Finsupp.single 1 k.val
  have hexpand : P.val = ∑ k : Fin (n + 1),
      MvPolynomial.monomial (d k) (MvPolynomial.coeff (d k) P.val) := by
    conv_lhs => rw [Submission.p02_es_177ebb5a_lcd_monomial_expansion n P]
    refine Fintype.sum_equiv Fin.revPerm _ _ ?_
    intro k
    simp only [d, Fin.revPerm_apply, Fin.val_rev, Nat.add_sub_add_right,
      Nat.sub_sub_self (Nat.le_of_lt_succ k.isLt),
      MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  let D : Module.End ℂ (MvPolynomial (Fin 2) ℂ) :=
    (MvPolynomial.pderiv (1 : Fin 2)).toLinearMap
  change MvPolynomial.eval _ ((D : MvPolynomial (Fin 2) ℂ →
    MvPolynomial (Fin 2) ℂ)^[r] P.val) = _
  rw [← Module.End.pow_apply]
  conv_lhs => rw [hexpand, map_sum]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [Module.End.pow_apply]
  change MvPolynomial.eval _
    ((fun p : MvPolynomial (Fin 2) ℂ => MvPolynomial.pderiv (1 : Fin 2) p)^[r]
      (MvPolynomial.monomial (d k) (MvPolynomial.coeff (d k) P.val))) = _
  rw [Submission.p02_es_177ebb5a_med_js_iterated_monomial, MvPolynomial.eval_monomial,
    Finsupp.prod_fintype _ _ (by intro j; simp)]
  simp [d, Fin.prod_univ_two, Finsupp.tsub_apply]
