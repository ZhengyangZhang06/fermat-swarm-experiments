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

open Filter MeasureTheory Set
open scoped Topology

/-- The polynomial-exponential weight has a finite nonnegative integral, controls its
translated interval integrals, and tends to zero at infinity. -/
theorem p02_es_177ebb5a_scl_polynomial_exp_tail :
    ∀ (n : ℕ) (a : ℝ), 0 < a →
      IntegrableOn (fun s : ℝ => (1 + s) ^ n * Real.exp (-a * s)) (Ioi 0) ∧
      0 ≤ (∫ s in Ioi (0 : ℝ), (1 + s) ^ n * Real.exp (-a * s)) ∧
      (∀ (y t : ℝ), 0 ≤ y → y ≤ t →
        (∫ s in y..t, (1 + s) ^ n * Real.exp (-a * s)) ≤
          (∫ s in Ioi (0 : ℝ), (1 + s) ^ n * Real.exp (-a * s)) *
            (1 + y) ^ n * Real.exp (-a * y)) ∧
      Tendsto (fun y : ℝ => (1 + y) ^ n * Real.exp (-a * y)) atTop (𝓝 0) := by
  intro n a ha
  -- Polynomial growth is dominated by every positive exponential rate.
  have hdecay (b : ℝ) (hb : 0 < b) :
      Tendsto (fun y : ℝ => (1 + y) ^ n * Real.exp (-b * y)) atTop (𝓝 0) := by
    -- Shift the library's polynomial/exponential ratio by 1 and cancel the shift by exp b.
    have h := ((isLittleO_pow_exp_pos_mul_atTop n hb).tendsto_div_nhds_zero.comp
      (tendsto_atTop_add_const_left atTop 1 tendsto_id)).mul_const (Real.exp b)
    simp only [zero_mul] at h
    convert h using 1
    ext y
    simp only [Function.comp_apply, id_eq]
    rw [div_eq_mul_inv, ← Real.exp_neg, mul_assoc, ← Real.exp_add]
    congr 2
    ring
  let w : ℝ → ℝ := fun s => (1 + s) ^ n * Real.exp (-a * s)
  have hw : Continuous w := by fun_prop
  have hw_nonneg (s : ℝ) (hs : 0 ≤ s) : 0 ≤ w s := by
    dsimp [w]
    positivity
  -- Comparison with the exponential of half the rate gives integrability.
  have hint : IntegrableOn w (Ioi 0) := by
    apply integrable_of_isBigO_exp_neg (half_pos ha) hw.continuousOn
    -- Dividing w by exp (-(a / 2) * s) leaves the same weight at the positive half-rate.
    apply Asymptotics.IsLittleO.isBigO
    apply Asymptotics.isLittleO_of_tendsto (fun x hx => (Real.exp_ne_zero _ hx).elim)
    convert hdecay (a / 2) (half_pos ha) using 1
    ext s
    dsimp [w]
    rw [div_eq_mul_inv, ← Real.exp_neg, mul_assoc, ← Real.exp_add]
    congr 2
    ring
  refine ⟨hint, setIntegral_nonneg measurableSet_Ioi (fun s hs => hw_nonneg s hs.le),
    ?_, hdecay a ha⟩
  intro y t hy hyt
  have hty : 0 ≤ t - y := sub_nonneg.mpr hyt
  -- Translation reduces the tail estimate to submultiplicativity on [0, ∞).
  have hsub (v : ℝ) (hv : 0 ≤ v) : w (y + v) ≤ w y * w v := by
    have hp : (1 + (y + v)) ^ n ≤ ((1 + y) * (1 + v)) ^ n :=
      pow_le_pow_left₀ (by positivity) (by nlinarith [mul_nonneg hy hv]) n
    dsimp [w]
    calc
      (1 + (y + v)) ^ n * Real.exp (-a * (y + v)) ≤
          ((1 + y) * (1 + v)) ^ n * Real.exp (-a * (y + v)) :=
        mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
      _ = ((1 + y) ^ n * Real.exp (-a * y)) *
          ((1 + v) ^ n * Real.exp (-a * v)) := by
        rw [mul_pow, show -a * (y + v) = -a * y + -a * v by ring, Real.exp_add]
        ring
  have hfinite : (∫ v in (0 : ℝ)..t - y, w v) ≤ ∫ v in Ioi (0 : ℝ), w v := by
    rw [intervalIntegral.integral_of_le hty]
    apply setIntegral_mono_set hint
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv using hw_nonneg v hv.le
    · exact Filter.Eventually.of_forall (fun v hv => hv.1)
  change (∫ s in y..t, w s) ≤ (∫ s in Ioi (0 : ℝ), w s) *
    (1 + y) ^ n * Real.exp (-a * y)
  calc
    (∫ s in y..t, w s) = ∫ v in (0 : ℝ)..t - y, w (y + v) := by
      rw [intervalIntegral.integral_comp_add_left]
      simp
    _ ≤ ∫ v in (0 : ℝ)..t - y, w y * w v := by
      apply intervalIntegral.integral_mono_on hty
        ((hw.comp (continuous_const.add continuous_id)).intervalIntegrable _ _)
        ((continuous_const.mul hw).intervalIntegrable _ _)
      intro v hv
      exact hsub v hv.1
    _ = w y * ∫ v in (0 : ℝ)..t - y, w v := intervalIntegral.integral_const_mul _ _
    _ ≤ w y * ∫ v in Ioi (0 : ℝ), w v :=
      mul_le_mul_of_nonneg_left hfinite (hw_nonneg y hy)
    _ = (∫ s in Ioi (0 : ℝ), w s) * (1 + y) ^ n * Real.exp (-a * y) := by
      dsimp [w]
      ring

end Submission
