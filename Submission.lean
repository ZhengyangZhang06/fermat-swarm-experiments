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
