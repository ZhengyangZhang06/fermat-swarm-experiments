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

theorem Submission.p02_es_177ebb5a_ssl_segment_estimates :
    ∀ (F H : ℂ → ℂ) (w : ℝ → ℝ) (L y₀ : ℝ),
      0 ≤ L → 0 < y₀ → ContinuousOn H {z : ℂ | 0 < z.im} →
      (∀ z : ℂ, 0 < z.im → HasDerivAt F (H z) z) →
      ContinuousOn w (Set.Ici y₀) →
      (∀ z : ℂ, 0 ≤ z.re → z.re ≤ L → y₀ ≤ z.im → ‖H z‖ ≤ w z.im) →
      (∀ (x y t : ℝ), 0 ≤ x → x ≤ L → y₀ ≤ y → y ≤ t →
        ‖F ((x : ℂ) + (t : ℂ) * Complex.I) -
          F ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤ ∫ s in y..t, w s) ∧
      (∀ (x y : ℝ), 0 ≤ x → x ≤ L → y₀ ≤ y →
        ‖F ((x : ℂ) + (y : ℂ) * Complex.I) - F ((y : ℂ) * Complex.I)‖ ≤
          x * w y) := by
  intro F H w L y₀ _hL hy₀ hH hF hw hbound
  constructor
  · intro x y t hx hxL hy hyt
    have hpath : Continuous (fun s : ℝ => (x : ℂ) + (s : ℂ) * Complex.I) := by
      fun_prop
    have hupper (s : ℝ) (hs : s ∈ Set.uIcc y t) :
        0 < ((x : ℂ) + (s : ℂ) * Complex.I).im := by
      have hys : y ≤ s := (Set.uIcc_of_le hyt ▸ hs).1
      simpa using hy₀.trans_le (hy.trans hys)
    have hderiv (s : ℝ) (hs : s ∈ Set.uIcc y t) :
        HasDerivAt (fun u : ℝ => F ((x : ℂ) + (u : ℂ) * Complex.I))
          (H ((x : ℂ) + (s : ℂ) * Complex.I) * Complex.I) s := by
      have hp : HasDerivAt (fun z : ℂ => (x : ℂ) + z * Complex.I) Complex.I
          (s : ℂ) := by
        simpa using ((hasDerivAt_id (s : ℂ)).mul_const Complex.I).const_add (x : ℂ)
      exact ((hF _ (hupper s hs)).comp (s : ℂ) hp).comp_ofReal
    have hint : IntervalIntegrable
        (fun s : ℝ => H ((x : ℂ) + (s : ℂ) * Complex.I) * Complex.I)
        MeasureTheory.volume y t :=
      ((hH.comp hpath.continuousOn (fun s hs => hupper s hs)).mul_const
        Complex.I).intervalIntegrable
    rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
    apply intervalIntegral.norm_integral_le_of_norm_le hyt
    · apply Filter.Eventually.of_forall
      intro s hs
      have hys : y₀ ≤ s := hy.trans hs.1.le
      simpa using hbound ((x : ℂ) + (s : ℂ) * Complex.I)
        (by simpa using hx) (by simpa using hxL) (by simpa using hys)
    · apply (hw.mono ?_).intervalIntegrable
      intro s hs
      exact hy.trans (Set.uIcc_of_le hyt ▸ hs).1
  · intro x y hx hxL hy
    have hpath : Continuous (fun s : ℝ => (s : ℂ) + (y : ℂ) * Complex.I) := by
      fun_prop
    have hupper (s : ℝ) : 0 < ((s : ℂ) + (y : ℂ) * Complex.I).im := by
      simpa using hy₀.trans_le hy
    have hderiv (s : ℝ) (_hs : s ∈ Set.uIcc 0 x) :
        HasDerivAt (fun u : ℝ => F ((u : ℂ) + (y : ℂ) * Complex.I))
          (H ((s : ℂ) + (y : ℂ) * Complex.I)) s := by
      simpa only [mul_one] using!
        ((hF _ (hupper s)).comp (s : ℂ)
          ((hasDerivAt_id (s : ℂ)).add_const ((y : ℂ) * Complex.I))).comp_ofReal
    have hint : IntervalIntegrable
        (fun s : ℝ => H ((s : ℂ) + (y : ℂ) * Complex.I))
        MeasureTheory.volume 0 x :=
      (hH.comp hpath.continuousOn (fun s _ => hupper s)).intervalIntegrable
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
    simp only [Complex.ofReal_zero, zero_add] at hFTC
    rw [← hFTC]
    calc
      _ ≤ w y * |x - 0| := intervalIntegral.norm_integral_le_of_norm_le_const (by
        intro s hs
        have hs' : s ∈ Set.Ioc 0 x := Set.uIoc_of_le hx ▸ hs
        simpa using hbound ((s : ℂ) + (y : ℂ) * Complex.I)
          (by simpa using hs'.1.le) (by simpa using hs'.2.trans hxL)
          (by simpa using hy))
      _ = x * w y := by rw [sub_zero, abs_of_nonneg hx, mul_comm]
