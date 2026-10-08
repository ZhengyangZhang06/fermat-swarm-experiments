/-
Copyright 2026 Anthropic, PBC. Licensed under Apache-2.0; see LICENSE.
Source: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_CuspForm_gamma0_weight_two_eq_zero_of_genusFormula_eq_zero.lean
Modified: replaced the proof with sorry and removed P2M proof imports.
Requires the upstream Definitions modules and their dependencies.
-/

import Mathlib
import Definitions.Def_ModularCurve_GenusNumerics
attribute [-instance] HeckeEis.instFiniteIndexHeckeUpper ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite
attribute [-simp] ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one ModularCurve.Period.jConjMat_apply_zero_one ModularCurve.Period.jConjSL_coe ModularCurve.Period.jConjMat_apply_one_zero ModularCurve.Period.jConjMat_apply_one_one ModularCurve.Period.jConjGamma0_coe ModularCurve.Period.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_zero HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.CuspSpace.cuspDenomAux_infty
attribute [-simp] ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one

set_option autoImplicit false

theorem CuspForm.gamma0_weight_two_eq_zero_of_genusFormula_eq_zero (N : ℕ) [NeZero N]
    (hg : ModularCurve.genusFormula N = 0) (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) : f = 0 := by
  sorry


theorem Submission.p10_17ae7b7d_pde_decay_zero :
    ∀ (w : ℝ) (g A : ℂ → ℂ), 0 < w → ContinuousAt A 0 →
      (∀ z : ℂ, 0 < z.im →
        g z = A (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * z / (w : ℂ)))) →
      (∀ ε : ℝ, 0 < ε → ∃ Y : ℝ, ∀ z : ℂ,
        0 < z.im → Y ≤ z.im → ‖g z‖ ≤ ε) → A 0 = 0 := by
  intro w g A hw hA hfactor hdecay
  have hbound : ∀ ε : ℝ, 0 < ε →
      ∃ r : ℝ, 0 < r ∧ ∀ q : ℂ, q ≠ 0 → ‖q‖ < r → ‖A q‖ ≤ ε := by
    intro ε hε
    obtain ⟨Y, hY⟩ := hdecay ε hε
    refine ⟨Real.exp (-2 * Real.pi * max 1 Y / w), Real.exp_pos _, ?_⟩
    intro q hq hqr
    let z := Function.Periodic.invQParam w q
    have heq : Function.Periodic.qParam w z = q :=
      Function.Periodic.qParam_right_inv hw.ne' hq
    have him : max 1 Y < z.im :=
      (Function.Periodic.norm_qParam_lt_iff hw (max 1 Y) z).mp (by rwa [heq])
    have hz : 0 < z.im := lt_trans (lt_of_lt_of_le zero_lt_one (le_max_left 1 Y)) him
    have hgz : g z = A q := by
      have h := hfactor z hz
      change g z = A (Function.Periodic.qParam w z) at h
      rwa [heq] at h
    rw [← hgz]
    exact hY z hz (le_trans (le_max_right 1 Y) him.le)
  by_contra hzero
  have ha : 0 < ‖A 0‖ := norm_pos_iff.mpr hzero
  have hε : 0 < ‖A 0‖ / 3 := by positivity
  obtain ⟨r, hr, hbound⟩ := hbound (‖A 0‖ / 3) hε
  obtain ⟨δ, hδ, hclose⟩ := Metric.continuousAt_iff.mp hA (‖A 0‖ / 3) hε
  let q : ℂ := (min r δ / 2 : ℝ)
  have hqpos : 0 < min r δ / 2 := half_pos (lt_min hr hδ)
  have hqnorm : ‖q‖ = min r δ / 2 := Complex.norm_of_nonneg hqpos.le
  have hqr : ‖q‖ < r := by
    rw [hqnorm]
    linarith [min_le_left r δ]
  have hqδ : ‖q‖ < δ := by
    rw [hqnorm]
    linarith [min_le_right r δ]
  have hqne : q ≠ 0 := norm_pos_iff.mp (by rwa [hqnorm])
  have hsmall : ‖A q‖ ≤ ‖A 0‖ / 3 := hbound q hqne hqr
  have hnear : ‖A q - A 0‖ < ‖A 0‖ / 3 := by
    simpa only [dist_eq_norm] using hclose (by simpa only [dist_zero_right] using hqδ)
  have htriangle : ‖A 0‖ ≤ ‖A q - A 0‖ + ‖A q‖ := by
    calc
      ‖A 0‖ = ‖(A 0 - A q) + A q‖ := by rw [sub_add_cancel]
      _ ≤ ‖A 0 - A q‖ + ‖A q‖ := norm_add_le _ _
      _ = ‖A q - A 0‖ + ‖A q‖ := by rw [norm_sub_rev]
  linarith
theorem Submission.p10_17ae7b7d_pde_finite_order :
    ∀ A : ℂ → ℂ, DifferentiableOn ℂ A (Metric.ball (0 : ℂ) 1) →
      (∃ q : ℂ, q ∈ Metric.ball (0 : ℂ) 1 ∧ A q ≠ 0) →
      analyticOrderAt A 0 ≠ ⊤ ∧ (A 0 = 0 → 1 ≤ analyticOrderNatAt A 0) := by
  intro A hA ⟨q, hq, hAq⟩
  have h0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by simp
  have hAn : AnalyticOnNhd ℂ A (Metric.ball (0 : ℂ) 1) :=
    hA.analyticOnNhd Metric.isOpen_ball
  have hfinite : analyticOrderAt A 0 ≠ ⊤ := by
    intro htop
    have hzero := hAn.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_ball (0 : ℂ) (1 : ℝ)).isPreconnected h0
      (analyticOrderAt_eq_top.mp htop)
    exact hAq (hzero hq)
  refine ⟨hfinite, fun hzero => Nat.one_le_iff_ne_zero.mpr ?_⟩
  intro horder
  have hz : analyticOrderAt A 0 = 0 := by
    simpa only [horder, Nat.cast_zero] using (Nat.cast_analyticOrderNatAt hfinite).symm
  exact ((hAn 0 h0).analyticOrderAt_eq_zero.mp hz) hzero
theorem Submission.p10_17ae7b7d_cc_lift_unimodular_row :
    ∀ (N : ℕ) [NeZero N] (r s : ZMod N),
      (∃ x y : ZMod N, x * r + y * s = 1) →
      ∃ A : Matrix.SpecialLinearGroup (Fin 2) ℤ,
        (A 1 0 : ZMod N) = r ∧ (A 1 1 : ZMod N) = s := by
  intro N _ r s h
  classical
  by_cases hN : N = 1
  · subst N
    exact ⟨1, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  let D : ℕ := if s.val = 0 then N else s.val
  have hD : D ≠ 0 := by
    dsimp [D]
    split_ifs with hs
    · exact NeZero.ne N
    · exact hs
  have hDs : (D : ZMod N) = s := by
    dsimp [D]
    split_ifs with hs
    · have hs' : s = 0 := by
        simpa using congrArg (fun k : ℕ => (k : ZMod N)) hs
      simp [hs']
    · exact ZMod.natCast_zmod_val s
  let P := D.primeFactors.filter (fun p => ¬ p ∣ N)
  let M := ∏ p ∈ P, p
  have hNM : N.Coprime M := by
    apply Nat.coprime_prod_right_iff.mpr
    intro p hp
    obtain ⟨hpD, hpN⟩ := Finset.mem_filter.mp hp
    exact ((Nat.prime_of_mem_primeFactors hpD).coprime_iff_not_dvd.mpr hpN).symm
  obtain ⟨C, hCN, hCM⟩ := Nat.chineseRemainder hNM r.val 1
  have hCr : (C : ZMod N) = r := by
    rw [← ZMod.natCast_zmod_val r]
    exact (ZMod.natCast_eq_natCast_iff C r.val N).mpr hCN
  have hCD : C.Coprime D := by
    apply Nat.coprime_of_dvd'
    intro p hp hpC hpD
    by_cases hpN : p ∣ N
    · let f : ZMod N →+* ZMod p := ZMod.castHom hpN (ZMod p)
      have hrp : f r = 0 := by
        rw [← hCr, map_natCast]
        exact (ZMod.natCast_eq_zero_iff C p).mpr hpC
      have hsp : f s = 0 := by
        rw [← hDs, map_natCast]
        exact (ZMod.natCast_eq_zero_iff D p).mpr hpD
      obtain ⟨x, y, hxy⟩ := h
      have hz := congrArg f hxy
      simp only [map_add, map_mul, map_one, hrp, hsp, mul_zero, add_zero] at hz
      exact (ZMod.natCast_eq_zero_iff 1 p).mp (by simpa using hz.symm)
    · have hpP : p ∈ P := Finset.mem_filter.mpr ⟨hp.mem_primeFactors hpD hD, hpN⟩
      have hpM : p ∣ M := Finset.dvd_prod_of_mem (fun q : ℕ => q) hpP
      exact (hCM.dvd_iff hpM).mp hpC
  obtain ⟨A, hAC, hAD⟩ := hCD.isCoprime.exists_SL2_row (1 : Fin 2)
  refine ⟨A, ?_, ?_⟩
  · simpa only [hAC, Int.cast_natCast] using hCr
  · simpa only [hAD, Int.cast_natCast] using hDs
theorem Submission.p10_17ae7b7d_pde_holomorphic_extension :
    ∀ (w : ℝ) (g : ℂ → ℂ), 0 < w →
      DifferentiableOn ℂ g {z : ℂ | 0 < z.im} →
      (∀ z : ℂ, 0 < z.im → g (z + (w : ℂ)) = g z) →
      (∃ C Y : ℝ, ∀ z : ℂ, 0 < z.im → Y ≤ z.im → ‖g z‖ ≤ C) →
      ∃ A : ℂ → ℂ, DifferentiableOn ℂ A (Metric.ball (0 : ℂ) 1) ∧
        (∀ z : ℂ, 0 < z.im →
          g z = A (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * z / (w : ℂ)))) := by
  classical
  intro w g hw hg hp hb
  let f : ℂ → ℂ := fun z => if 0 < z.im then g z else 0
  have hf : Function.Periodic f (w : ℂ) := by
    intro z
    by_cases hz : 0 < z.im
    · simpa [f, Complex.add_im, hz] using hp z hz
    · simp [f, Complex.add_im, hz]
  have hU : IsOpen {z : ℂ | 0 < z.im} :=
    isOpen_lt continuous_const Complex.continuous_im
  have hdiff : ∀ z : ℂ, 0 < z.im → DifferentiableAt ℂ f z := by
    intro z hz
    apply (hg.differentiableAt (hU.mem_nhds hz)).congr_of_eventuallyEq
    filter_upwards [hU.mem_nhds hz] with y hy
    simp [f, hy]
  have hhol : ∀ᶠ z in Filter.comap Complex.im Filter.atTop,
      DifferentiableAt ℂ f z := by
    apply Filter.eventually_comap.mpr
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with y hy
    intro z hz
    exact hdiff z (hz ▸ hy)
  have hbd : Filter.BoundedAtFilter (Filter.comap Complex.im Filter.atTop) f := by
    obtain ⟨C, Y, hCY⟩ := hb
    apply Asymptotics.IsBigO.of_bound C
    apply Filter.eventually_comap.mpr
    filter_upwards [Filter.eventually_gt_atTop (max 0 Y)] with y hy
    intro z hz
    have hz0 : 0 < z.im := hz ▸ lt_of_le_of_lt (le_max_left 0 Y) hy
    have hzY : Y ≤ z.im := hz ▸ le_of_lt (lt_of_le_of_lt (le_max_right 0 Y) hy)
    simpa [f, hz0] using hCY z hz0 hzY
  refine ⟨Function.Periodic.cuspFunction w f, ?_, ?_⟩
  · intro q hq
    by_cases hq0 : q = 0
    · subst q
      exact (Function.Periodic.differentiableAt_cuspFunction_zero hw hf hhol hbd).differentiableWithinAt
    · have hqn : ‖q‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hq
      have hqi : 0 < (Function.Periodic.invQParam w q).im := by
        rw [Function.Periodic.im_invQParam]
        exact mul_pos_of_neg_of_neg
          (div_neg_of_neg_of_pos (neg_lt_zero.mpr hw) (by positivity))
          (Real.log_neg (norm_pos_iff.mpr hq0) hqn)
      have hd := Function.Periodic.differentiableAt_cuspFunction hw.ne' hf
        (hdiff _ hqi)
      rw [Function.Periodic.qParam_right_inv hw.ne' hq0] at hd
      exact hd.differentiableWithinAt
  · intro z hz
    simpa [Function.Periodic.qParam, f, hz] using
      (Function.Periodic.eq_cuspFunction hw.ne' hf z).symm
theorem Submission.p10_17ae7b7d_norm_local_multiplier_order :
    ∀ (g ψ J : ℂ → ℂ) (v : ℂ), AnalyticAt ℂ g v → analyticOrderAt g v ≠ ⊤ →
      AnalyticAt ℂ ψ v → ψ v = v → deriv ψ v ≠ 0 → AnalyticAt ℂ J v →
      (∃ r : ℝ, 0 < r ∧ ∀ z : ℂ, ‖z - v‖ < r → g (ψ z) = J z * g z) →
      (deriv ψ v) ^ analyticOrderNatAt g v = J v := by
  intro g ψ J v hg hgfin hψ hfix _hderiv hJ hequiv
  let m := analyticOrderNatAt g v
  obtain ⟨b, hb, hbne, hfactor⟩ := (hg.analyticOrderNatAt_eq_iff hgfin).mp rfl
  have hfactor' : ∀ᶠ z in nhds v, g z = (z - v) ^ m * b z := by
    simpa only [smul_eq_mul] using hfactor
  have hψt : Filter.Tendsto ψ (nhds v) (nhds v) := by
    simpa only [hfix] using hψ.continuousAt.tendsto
  have hfactorψ : ∀ᶠ z in nhds v, g (ψ z) = (ψ z - v) ^ m * b (ψ z) :=
    hψt.eventually hfactor'
  obtain ⟨r, hr, hequiv⟩ := hequiv
  have hequiv' : ∀ᶠ z in nhds v, g (ψ z) = J z * g z := by
    apply Metric.eventually_nhds_iff.mpr
    exact ⟨r, hr, fun z hz => hequiv z (by simpa only [dist_eq_norm] using hz)⟩
  have hcancel : (fun z => dslope ψ v z ^ m * b (ψ z)) =ᶠ[nhdsWithin v {v}ᶜ]
      (fun z => J z * b z) := by
    filter_upwards [hfactor'.filter_mono nhdsWithin_le_nhds,
      hfactorψ.filter_mono nhdsWithin_le_nhds,
      hequiv'.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz hzψ heq hzne
    apply mul_left_cancel₀ (pow_ne_zero m (sub_ne_zero.mpr hzne))
    calc
      (z - v) ^ m * (dslope ψ v z ^ m * b (ψ z)) =
          ((z - v) * dslope ψ v z) ^ m * b (ψ z) := by rw [mul_pow, mul_assoc]
      _ = (ψ z - v) ^ m * b (ψ z) := by
        rw [show (z - v) * dslope ψ v z = ψ z - v from by
          simpa only [smul_eq_mul, hfix] using sub_smul_dslope ψ v z]
      _ = g (ψ z) := hzψ.symm
      _ = J z * g z := heq
      _ = (z - v) ^ m * (J z * b z) := by rw [hz]; ring
  have hd : Filter.Tendsto (fun z => dslope ψ v z ^ m) (nhds v) (nhds (deriv ψ v ^ m)) := by
    simpa only [dslope_same] using
      (continuousAt_dslope_same.mpr hψ.differentiableAt).tendsto.pow m
  have hleft : Filter.Tendsto (fun z => dslope ψ v z ^ m * b (ψ z))
      (nhds v) (nhds (deriv ψ v ^ m * b v)) :=
    hd.mul (hb.continuousAt.tendsto.comp hψt)
  have hright : Filter.Tendsto (fun z => J z * b z) (nhds v) (nhds (J v * b v)) :=
    hJ.continuousAt.tendsto.mul hb.continuousAt.tendsto
  exact mul_right_cancel₀ hbne (tendsto_nhds_unique_of_eventuallyEq
    (hleft.mono_left nhdsWithin_le_nhds) (hright.mono_left nhdsWithin_le_nhds) hcancel)


theorem Submission.p10_17ae7b7d_efp_unimodular_eigenrow_iff :
    ∀ (R : Type) [CommRing R] (k r s : R),
      (∃ x y : R, x * r + y * s = 1) →
      ((∃ u : Rˣ, s = (u : R) * r ∧ k * s - r = (u : R) * s) ↔
        IsUnit r ∧ ∃! t : R, s = r * t ∧ t ^ 2 - k * t + 1 = 0) := by
  intro R _ k r s ⟨x, y, hxy⟩
  constructor
  · rintro ⟨u, hs, heigen⟩
    have hinv : (x + y * (u : R)) * r = 1 := by
      calc
        (x + y * (u : R)) * r = x * r + y * s := by rw [hs]; ring
        _ = 1 := hxy
    have hr : IsUnit r := isUnit_iff_exists.mpr
      ⟨x + y * (u : R), by rw [mul_comm]; exact hinv, hinv⟩
    refine ⟨hr, (u : R), ⟨?_, ?_⟩, ?_⟩
    · exact hs.trans (mul_comm _ _)
    · apply hr.mul_left_cancel
      calc
        r * ((u : R) ^ 2 - k * (u : R) + 1) =
            (u : R) * s - (k * s - r) := by rw [hs]; ring
        _ = r * 0 := by rw [heigen, sub_self, mul_zero]
    · intro t ht
      apply hr.mul_left_cancel
      calc
        r * t = s := ht.1.symm
        _ = r * (u : R) := hs.trans (mul_comm _ _)
  · rintro ⟨_, t, ⟨hs, hpoly⟩, _⟩
    have hinv : t * (k - t) = 1 := by
      calc
        t * (k - t) = 1 - (t ^ 2 - k * t + 1) := by ring
        _ = 1 := by rw [hpoly, sub_zero]
    let u : Rˣ := ⟨t, k - t, hinv, by rw [mul_comm]; exact hinv⟩
    refine ⟨u, ?_, ?_⟩
    · change s = t * r
      exact hs.trans (mul_comm _ _)
    · change k * s - r = t * s
      calc
        k * s - r = t * s - r * (t ^ 2 - k * t + 1) := by rw [hs]; ring
        _ = t * s := by rw [hpoly, mul_zero, sub_zero]

namespace Submission

theorem p10_17ae7b7d_periodic_disk_extension :
    ∀ (w : ℝ) (g : ℂ → ℂ), 0 < w →
      DifferentiableOn ℂ g {z : ℂ | 0 < z.im} →
      (∃ z : ℂ, 0 < z.im ∧ g z ≠ 0) →
      (∀ z : ℂ, 0 < z.im → g (z + (w : ℂ)) = g z) →
      (∃ C Y : ℝ, ∀ z : ℂ, 0 < z.im → Y ≤ z.im → ‖g z‖ ≤ C) →
      ∃ A : ℂ → ℂ, DifferentiableOn ℂ A (Metric.ball (0 : ℂ) 1) ∧
        (∀ z : ℂ, 0 < z.im →
          g z = A (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * z / (w : ℂ)))) ∧
        analyticOrderAt A 0 ≠ ⊤ ∧
        ((∀ ε : ℝ, 0 < ε → ∃ Y : ℝ, ∀ z : ℂ,
          0 < z.im → Y ≤ z.im → ‖g z‖ ≤ ε) → 1 ≤ analyticOrderNatAt A 0) := by
  intro w g hw hg hnonzero hperiodic hbounded
  obtain ⟨A, hA, hAg⟩ :=
    p10_17ae7b7d_pde_holomorphic_extension w g hw hg hperiodic hbounded
  obtain ⟨z, hz, hgz⟩ := hnonzero
  have hq : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * z / (w : ℂ)) ∈
      Metric.ball (0 : ℂ) 1 := by
    rw [Metric.mem_ball, dist_zero_right, Complex.norm_exp, Real.exp_lt_one_iff]
    have hheight : 0 < 2 * Real.pi * z.im :=
      mul_pos (mul_pos (by norm_num) Real.pi_pos) hz
    simpa [Complex.mul_re, Complex.mul_im] using
      div_neg_of_neg_of_pos (neg_neg_of_pos hheight) hw
  obtain ⟨hfinite, hpositive⟩ := p10_17ae7b7d_pde_finite_order A hA
    ⟨_, hq, by simpa only [← hAg z hz] using hgz⟩
  refine ⟨A, hA, hAg, hfinite, ?_⟩
  intro hdecay
  apply hpositive
  exact p10_17ae7b7d_pde_decay_zero w g A hw
    (hA.differentiableAt (Metric.ball_mem_nhds _ (by norm_num))).continuousAt
    hAg hdecay

end Submission
theorem Submission.p10_17ae7b7d_valence_modular_log_derivative :
    ∀ (k : ℕ) (F : ℂ → ℂ),
      DifferentiableOn ℂ F {z : ℂ | 0 < z.im} →
      (∀ z : ℂ, 0 < z.im → F (z + 1) = F z) →
      (∀ z : ℂ, 0 < z.im → F (-1 / z) = z ^ k * F z) →
      ∀ z : ℂ, 0 < z.im →
        analyticOrderNatAt F (z + 1) = analyticOrderNatAt F z ∧
        analyticOrderNatAt F (-1 / z) = analyticOrderNatAt F z ∧
        (F z ≠ 0 →
          deriv F (z + 1) / F (z + 1) = deriv F z / F z ∧
          (deriv F (-1 / z) / F (-1 / z)) / z ^ 2 =
            (k : ℂ) / z + deriv F z / F z) := by
  intro k F hF hT hS z hz
  have hU : IsOpen {w : ℂ | 0 < w.im} :=
    isOpen_lt continuous_const Complex.continuous_im
  have hA (w : ℂ) (hw : 0 < w.im) : AnalyticAt ℂ F w :=
    hF.analyticAt (hU.mem_nhds hw)
  have hz0 : z ≠ 0 := by
    intro h
    simp [h] at hz
  have hzT : 0 < (z + 1).im := by simpa using hz
  have hzS : 0 < (-1 / z).im := by
    simpa [Complex.div_im, neg_div] using div_pos hz (Complex.normSq_pos.mpr hz0)
  have aT : AnalyticAt ℂ (fun w : ℂ => w + 1) z := by fun_prop
  have aS : AnalyticAt ℂ (fun w : ℂ => -1 / w) z := by fun_prop
  have dT : deriv (fun w : ℂ => w + 1) z = 1 := by simp
  have dS : deriv (fun w : ℂ => -1 / w) z = 1 / z ^ 2 := by simp
  have eT : Filter.EventuallyEq (nhds z) (F ∘ fun w : ℂ => w + 1) F :=
    Filter.eventually_of_mem (hU.mem_nhds hz) fun w hw => hT w hw
  have eS : Filter.EventuallyEq (nhds z) (F ∘ fun w : ℂ => -1 / w)
      (fun w => w ^ k * F w) :=
    Filter.eventually_of_mem (hU.mem_nhds hz) fun w hw => hS w hw
  have oT : analyticOrderAt F (z + 1) = analyticOrderAt F z := by
    calc
      analyticOrderAt F (z + 1) =
          analyticOrderAt (F ∘ fun w : ℂ => w + 1) z :=
        (analyticOrderAt_comp_of_deriv_ne_zero aT (by simp [dT])).symm
      _ = analyticOrderAt F z := analyticOrderAt_congr eT
  have aP : AnalyticAt ℂ (fun w : ℂ => w ^ k) z := by fun_prop
  have oS : analyticOrderAt F (-1 / z) = analyticOrderAt F z := by
    calc
      analyticOrderAt F (-1 / z) =
          analyticOrderAt (F ∘ fun w : ℂ => -1 / w) z :=
        (analyticOrderAt_comp_of_deriv_ne_zero aS (by simp [dS, hz0])).symm
      _ = analyticOrderAt (fun w => w ^ k * F w) z := analyticOrderAt_congr eS
      _ = analyticOrderAt (fun w : ℂ => w ^ k) z + analyticOrderAt F z :=
        analyticOrderAt_mul aP (hA z hz)
      _ = analyticOrderAt F z := by
        rw [aP.analyticOrderAt_eq_zero.mpr (pow_ne_zero k hz0), zero_add]
  refine ⟨congrArg ENat.toNat oT, congrArg ENat.toNat oS, ?_⟩
  intro hFz
  constructor
  · have h := (logDeriv_congr_nhds eT).self_of_nhds
    rw [logDeriv_comp (g := fun w : ℂ => w + 1) (hA (z + 1) hzT).differentiableAt aT.differentiableAt,
      dT, mul_one] at h
    exact h
  · have h := (logDeriv_congr_nhds eS).self_of_nhds
    rw [logDeriv_comp (g := fun w : ℂ => -1 / w) (hA (-1 / z) hzS).differentiableAt aS.differentiableAt,
      dS, logDeriv_mul (f := fun w : ℂ => w ^ k) (g := F) z (pow_ne_zero k hz0) hFz aP.differentiableAt
        (hA z hz).differentiableAt, logDeriv_pow] at h
    simpa only [logDeriv_apply, mul_one_div] using h


theorem Submission.p10_17ae7b7d_efp_inverse_coset_eq_iff :
    ∀ (N : ℕ) [NeZero N] (A B : Matrix.SpecialLinearGroup (Fin 2) ℤ),
      (QuotientGroup.mk (A⁻¹) :
        (Matrix.SpecialLinearGroup (Fin 2) ℤ) ⧸ CongruenceSubgroup.Gamma0 N) =
          QuotientGroup.mk (B⁻¹) ↔
        ∃ u : (ZMod N)ˣ,
          (B 1 0 : ZMod N) = (u : ZMod N) * (A 1 0 : ZMod N) ∧
          (B 1 1 : ZMod N) = (u : ZMod N) * (A 1 1 : ZMod N) := by
  intro N _ A B
  constructor
  · intro h
    let E := B * A⁻¹
    have hE : E ∈ CongruenceSubgroup.Gamma0 N := by
      simpa only [inv_inv] using (QuotientGroup.eq.mp h.symm)
    have hzero : (E 1 0 : ZMod N) = 0 := CongruenceSubgroup.Gamma0_mem.mp hE
    have hdet : (E 0 0 : ZMod N) * (E 1 1 : ZMod N) -
        (E 0 1 : ZMod N) * (E 1 0 : ZMod N) = 1 := by
      have h := E.det_coe
      rw [Matrix.det_fin_two] at h
      simpa only [Int.cast_sub, Int.cast_mul, Int.cast_one] using
        congrArg (fun z : ℤ => (z : ZMod N)) h
    have hunit : (E 1 1 : ZMod N) * (E 0 0 : ZMod N) = 1 := by
      rw [hzero, mul_zero, sub_zero] at hdet
      simpa only [mul_comm] using hdet
    let u : (ZMod N)ˣ := Units.mkOfMulEqOne (E 1 1 : ZMod N) (E 0 0 : ZMod N) hunit
    have hBA : E * A = B := by
      dsimp [E]
      rw [mul_assoc, inv_mul_cancel, mul_one]
    have hrow (j : Fin 2) : (B 1 j : ZMod N) = (E 1 1 : ZMod N) * (A 1 j : ZMod N) := by
      have h := congrArg (fun C : Matrix.SpecialLinearGroup (Fin 2) ℤ =>
        (C 1 j : ZMod N)) hBA
      change (((E.1 * A.1) 1 j : ℤ) : ZMod N) = (B 1 j : ZMod N) at h
      simp only [Matrix.mul_apply, Fin.sum_univ_two, Int.cast_add, Int.cast_mul] at h
      change (E 1 0 : ZMod N) * (A 0 j : ZMod N) +
        (E 1 1 : ZMod N) * (A 1 j : ZMod N) = (B 1 j : ZMod N) at h
      simpa only [hzero, zero_mul, zero_add] using h.symm
    exact ⟨u, hrow 0, hrow 1⟩
  · rintro ⟨u, hc, hd⟩
    apply Eq.symm
    apply QuotientGroup.eq.mpr
    rw [inv_inv]
    apply CongruenceSubgroup.Gamma0_mem.mpr
    change (((B.1 * (A⁻¹).1) 1 0 : ℤ) : ZMod N) = 0
    rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    change ((B 1 0 * A 1 1 + B 1 1 * -(A 1 0) : ℤ) : ZMod N) = 0
    push_cast
    rw [hc, hd]
    ring


theorem Submission.p10_17ae7b7d_cpo_analytic_order_nonzero :
    ∀ (w : ℕ) (ζ : ℂ) (A : ℂ → ℂ), ζ ≠ 0 → AnalyticAt ℂ A 0 →
      analyticOrderAt A 0 ≠ ⊤ →
      let P : ℂ → ℂ := fun t => ∏ j ∈ Finset.range w, A (ζ ^ j * t)
      AnalyticAt ℂ P 0 ∧ analyticOrderAt P 0 ≠ ⊤ ∧
        analyticOrderNatAt P 0 = w * analyticOrderNatAt A 0 := by
  intro w ζ A hζ hA hfinite
  let m := analyticOrderNatAt A 0
  obtain ⟨b, hb, hb0, hAb⟩ := (hA.analyticOrderNatAt_eq_iff hfinite).mp (rfl :
    analyticOrderNatAt A 0 = m)
  simp only [sub_zero, smul_eq_mul] at hAb
  have hL (j : ℕ) : AnalyticAt ℂ (fun t : ℂ => ζ ^ j * t) 0 :=
    analyticAt_const.mul analyticAt_id
  have hP : AnalyticAt ℂ (fun t => ∏ j ∈ Finset.range w, A (ζ ^ j * t)) 0 := by
    apply Finset.analyticAt_fun_prod
    intro j _
    exact (by simpa only [mul_zero] using hA : AnalyticAt ℂ A (ζ ^ j * 0)).comp (hL j)
  let D : ℂ → ℂ := fun t => ∏ j ∈ Finset.range w, ζ ^ (j * m) * b (ζ ^ j * t)
  have hD : AnalyticAt ℂ D 0 := by
    apply Finset.analyticAt_fun_prod
    intro j _
    exact analyticAt_const.mul
      ((by simpa only [mul_zero] using hb : AnalyticAt ℂ b (ζ ^ j * 0)).comp (hL j))
  have hD0 : D 0 ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j _
    simpa only [mul_zero] using mul_ne_zero (pow_ne_zero (j * m) hζ) hb0
  have hlocal : ∀ᶠ t in nhds (0 : ℂ), ∀ j ∈ Finset.range w,
      A (ζ ^ j * t) = (ζ ^ j * t) ^ m * b (ζ ^ j * t) := by
    apply (Filter.eventually_all_finset (Finset.range w)).mpr
    intro j _
    have ht : Filter.Tendsto (fun t : ℂ => ζ ^ j * t) (nhds 0) (nhds 0) := by
      simpa only [ContinuousAt, mul_zero] using (hL j).continuousAt
    exact ht.eventually hAb
  have horder : analyticOrderAt (fun t => ∏ j ∈ Finset.range w, A (ζ ^ j * t)) 0 =
      (w * m : ℕ) := by
    apply hP.analyticOrderAt_eq_natCast.mpr
    refine ⟨D, hD, hD0, ?_⟩
    filter_upwards [hlocal] with t ht
    simp only [sub_zero, smul_eq_mul]
    calc
      (∏ j ∈ Finset.range w, A (ζ ^ j * t)) =
          ∏ j ∈ Finset.range w, t ^ m * (ζ ^ (j * m) * b (ζ ^ j * t)) := by
        apply Finset.prod_congr rfl
        intro j hj
        rw [ht j hj, mul_pow, ← pow_mul]
        rw [mul_comm (ζ ^ (j * m)) (t ^ m), mul_assoc]
      _ = t ^ (w * m) * D t := by
        simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
          ← pow_mul, Nat.mul_comm, D]
  refine ⟨hP, ?_, ?_⟩
  · rw [horder]
    exact ENat.natCast_ne_top _
  · simp only [analyticOrderNatAt, horder, ENat.toNat_natCast]
    rfl


theorem Submission.p10_17ae7b7d_cpo_rotation_invariant :
    ∀ (w : ℕ) (ζ : ℂ) (A : ℂ → ℂ), 0 < w → ζ ^ w = 1 →
      let P : ℂ → ℂ := fun t => ∏ j ∈ Finset.range w, A (ζ ^ j * t)
      ∀ t : ℂ, P (ζ * t) = P t := by
  intro w ζ A hw hζ
  cases w with
  | zero => omega
  | succ n =>
    dsimp only
    intro t
    calc
      (∏ j ∈ Finset.range (n + 1), A (ζ ^ j * (ζ * t))) =
          ∏ j ∈ Finset.range (n + 1), A (ζ ^ (j + 1) * t) := by
        apply Finset.prod_congr rfl
        intro j _
        rw [pow_succ, mul_assoc]
      _ = (∏ j ∈ Finset.range n, A (ζ ^ (j + 1) * t)) *
          A (ζ ^ (n + 1) * t) := Finset.prod_range_succ _ _
      _ = (∏ j ∈ Finset.range n, A (ζ ^ (j + 1) * t)) *
          A (ζ ^ 0 * t) := by rw [hζ, pow_zero]
      _ = ∏ j ∈ Finset.range (n + 1), A (ζ ^ j * t) :=
        (Finset.prod_range_succ' (fun j => A (ζ ^ j * t)) n).symm

theorem Submission.p10_17ae7b7d_cld_qexp_finite_order :
    ∀ (F A : ℂ → ℂ), DifferentiableOn ℂ F {z : ℂ | 0 < z.im} →
      (∃ z : ℂ, 0 < z.im ∧ F z ≠ 0) → AnalyticAt ℂ A 0 →
      (∃ Y₀ : ℝ, ∀ z : ℂ, 0 < z.im → Y₀ ≤ z.im →
        F z = A (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * z))) →
      analyticOrderAt A 0 ≠ ⊤ := by
  intro F A hF ⟨z₁, hz₁, hFz₁⟩ _ ⟨Y₀, hfactor⟩ htop
  have hU : IsOpen {z : ℂ | 0 < z.im} :=
    isOpen_lt continuous_const Complex.continuous_im
  have hAn : AnalyticOnNhd ℂ F {z : ℂ | 0 < z.im} := hF.analyticOnNhd hU
  obtain ⟨δ, hδ, hAzero⟩ := Metric.eventually_nhds_iff.mp (analyticOrderAt_eq_top.mp htop)
  let T : ℝ := max (max 0 Y₀) (-Real.log δ / (2 * Real.pi))
  have hT0 : 0 ≤ T := le_trans (le_max_left 0 Y₀) (le_max_left _ _)
  have hTY : Y₀ ≤ T := le_trans (le_max_right 0 Y₀) (le_max_left _ _)
  have hTlog : -Real.log δ / (2 * Real.pi) ≤ T := le_max_right _ _
  have hexp : Real.exp (-2 * Real.pi * T) ≤ δ := by
    rw [← Real.exp_log hδ]
    apply Real.exp_le_exp.mpr
    have hmul := (div_le_iff₀ (by positivity : 0 < 2 * Real.pi)).mp hTlog
    nlinarith
  have hhigh : ∀ z : ℂ, T < z.im → F z = 0 := by
    intro z hz
    rw [hfactor z (lt_of_le_of_lt hT0 hz) (le_trans hTY hz.le)]
    apply hAzero
    rw [dist_zero_right]
    have hq := (Function.Periodic.norm_qParam_lt_iff (by norm_num : (0 : ℝ) < 1) T z).mpr hz
    have hq' : ‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I * z)‖ <
        Real.exp (-2 * Real.pi * T) := by
      simpa only [Function.Periodic.qParam, Complex.ofReal_one, div_one] using hq
    exact lt_of_lt_of_le hq' hexp
  let v : ℂ := ((T + 1 : ℝ) : ℂ) * Complex.I
  have hv : T < v.im := by simp [v]
  have hvU : v ∈ {z : ℂ | 0 < z.im} := lt_of_le_of_lt hT0 hv
  have hzero : F =ᶠ[nhds v] 0 := by
    have hV : IsOpen {z : ℂ | T < z.im} :=
      isOpen_lt continuous_const Complex.continuous_im
    filter_upwards [hV.mem_nhds hv] with z hz
    exact hhigh z hz
  exact hFz₁ (hAn.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_halfSpace_im_gt 0).isPreconnected hvU hzero hz₁)


theorem Submission.p10_17ae7b7d_rd_sparse_series_descent :
    ∀ (w : ℕ) (P : ℂ → ℂ) (p : FormalMultilinearSeries ℂ ℂ ℂ),
      0 < w → HasFPowerSeriesAt P p 0 →
      (∀ n : ℕ, ¬ w ∣ n → p.coeff n = 0) →
      ∃ C : ℂ → ℂ, AnalyticAt ℂ C 0 ∧
        ∃ r : ℝ, 0 < r ∧ ∀ t : ℂ, ‖t‖ < r → P t = C (t ^ w) := by
  intro w P p hw ⟨R, hR⟩ hsparse
  obtain ⟨r, hr, hrR⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hR.r_pos
  have hrpos : 0 < r := by exact_mod_cast hr
  have hinj : Function.Injective (fun n : ℕ => w * n) := mul_right_injective₀ hw.ne'
  let B : FormalMultilinearSeries ℂ ℂ ℂ :=
    FormalMultilinearSeries.ofScalars ℂ (fun n => p.coeff (w * n))
  have hsub := (p.summable_norm_mul_pow (hrR.trans_le hR.r_le)).comp_injective hinj
  have hBrad : ((r ^ w : NNReal) : ENNReal) ≤ B.radius := by
    apply B.le_radius_of_summable
    simpa only [B, FormalMultilinearSeries.norm_apply_eq_norm_coef,
      FormalMultilinearSeries.coeff_ofScalars, Function.comp_def,
      NNReal.coe_pow, pow_mul] using hsub
  have hBpos : 0 < B.radius :=
    lt_of_lt_of_le (by exact_mod_cast pow_pos hrpos w) hBrad
  refine ⟨B.sum, (B.hasFPowerSeriesOnBall hBpos).analyticAt, (r : ℝ), ?_, ?_⟩
  · exact_mod_cast hrpos
  · intro t ht
    have htR : t ∈ Metric.eball (0 : ℂ) R := by
      apply mem_eball_zero_iff.mpr
      exact lt_trans (by exact_mod_cast ht) hrR
    have hsupport : Function.support (fun n : ℕ => p n (fun _ => t)) ⊆
        Set.range (fun n : ℕ => w * n) := by
      intro n hn
      by_contra hnot
      have hnd : ¬ w ∣ n := by
        rintro ⟨k, hk⟩
        exact hnot ⟨k, hk.symm⟩
      apply hn
      change p n (fun _ => t) = 0
      rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff, hsparse n hnd, smul_zero]
    calc
      P t = p.sum t := by simpa only [zero_add] using hR.sum htR
      _ = ∑' n : ℕ, p (w * n) (fun _ => t) := (hinj.tsum_eq hsupport).symm
      _ = B.sum (t ^ w) := by
        apply tsum_congr
        intro n
        simp only [B, FormalMultilinearSeries.apply_eq_pow_smul_coeff,
          FormalMultilinearSeries.coeff_ofScalars, pow_mul]

theorem Submission.p10_17ae7b7d_indent_moving_interval_limit :
    ∀ (F : ℝ → ℝ → ℂ) (α β δ : ℝ → ℝ) (c : ℂ) (a b : ℝ),
      Filter.Tendsto α (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds a) →
      Filter.Tendsto β (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds b) →
      Filter.Tendsto δ (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (0 : ℝ)) →
      Filter.Eventually (fun ε : ℝ =>
        IntervalIntegrable (F ε) MeasureTheory.volume (α ε) (β ε) ∧
        ∀ t : ℝ, ‖F ε t - c‖ ≤ δ ε) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) →
      Filter.Tendsto (fun ε : ℝ =>
        intervalIntegral (F ε) (α ε) (β ε) MeasureTheory.volume)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (c * ((b - a : ℝ) : ℂ))) := by
  intro F α β δ c a b hα hβ hδ hF
  have herr : Filter.Tendsto (fun ε : ℝ =>
      intervalIntegral (fun t => F ε t - c) (α ε) (β ε) MeasureTheory.volume)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (0 : ℂ)) := by
    apply squeeze_zero_norm'
    · filter_upwards [hF] with ε hε
      exact intervalIntegral.norm_integral_le_of_norm_le_const (fun t _ => hε.2 t)
    · simpa only [zero_mul] using hδ.mul (hβ.sub hα).abs
  have hc : Filter.Tendsto (fun ε : ℝ => c * ((β ε - α ε : ℝ) : ℂ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (c * ((b - a : ℝ) : ℂ))) :=
    (hβ.sub hα).ofReal.const_mul c
  have hsum := herr.add hc
  rw [zero_add] at hsum
  apply hsum.congr'
  filter_upwards [hF] with ε hε
  rw [intervalIntegral.integral_sub hε.1 intervalIntegrable_const,
    intervalIntegral.integral_const]
  simp only [Complex.real_smul, mul_comm (↑(β ε - α ε) : ℂ) c, sub_add_cancel]

theorem Submission.p10_17ae7b7d_indent_logderiv_remainder :
    ∀ (f : ℂ → ℂ) (v : ℂ), AnalyticAt ℂ f v → analyticOrderAt f v ≠ ⊤ →
      ∃ (r M : ℝ) (G : ℂ → ℂ), 0 < r ∧ 0 ≤ M ∧
        AnalyticOnNhd ℂ G (Metric.closedBall v r) ∧
        (∀ z ∈ Metric.closedBall v r, ‖G z‖ ≤ M) ∧
        ∀ z ∈ Metric.ball v r, z ≠ v → f z ≠ 0 ∧
          deriv f z / f z = (analyticOrderNatAt f v : ℂ) / (z - v) + G z := by
  intro f v hf hfinite
  obtain ⟨B, hB, hBv, hfactor⟩ := hf.analyticOrderAt_ne_top.mp hfinite
  have hnear : ∀ᶠ z in nhds v, AnalyticAt ℂ B z ∧ B z ≠ 0 ∧
      f z = (z - v) ^ analyticOrderNatAt f v * B z := by
    filter_upwards [hB.eventually_analyticAt, hB.continuousAt.eventually_ne hBv,
      hfactor] with z hz hne heq
    exact ⟨hz, hne, by simpa only [smul_eq_mul] using heq⟩
  obtain ⟨ρ, hρ, hρprop⟩ := Metric.eventually_nhds_iff_ball.mp hnear
  have hclosed : Metric.closedBall v (ρ / 2) ⊆ Metric.ball v ρ :=
    Metric.closedBall_subset_ball (by linarith)
  let G : ℂ → ℂ := fun z => deriv B z / B z
  have hG : AnalyticOnNhd ℂ G (Metric.closedBall v (ρ / 2)) := by
    intro z hz
    obtain ⟨hBz, hBzne, _⟩ := hρprop z (hclosed hz)
    exact hBz.deriv.div hBz hBzne
  obtain ⟨K, hK⟩ := (isCompact_closedBall v (ρ / 2)).exists_bound_of_continuousOn
    hG.continuousOn
  refine ⟨ρ / 2, max 0 K, G, half_pos hρ, le_max_left _ _, hG,
    fun z hz => (hK z hz).trans (le_max_right _ _), ?_⟩
  intro z hz hzv
  have hzρ : z ∈ Metric.ball v ρ := hclosed (Metric.ball_subset_closedBall hz)
  obtain ⟨hBz, hBzne, hfz⟩ := hρprop z hzρ
  have hsub : z - v ≠ 0 := sub_ne_zero.mpr hzv
  have hpow : (z - v) ^ analyticOrderNatAt f v ≠ 0 := pow_ne_zero _ hsub
  refine ⟨by rw [hfz]; exact mul_ne_zero hpow hBzne, ?_⟩
  have heq : f =ᶠ[nhds z] fun w => (w - v) ^ analyticOrderNatAt f v * B w := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hzρ] with w hw
    exact (hρprop w hw).2.2
  change logDeriv f z = (analyticOrderNatAt f v : ℂ) / (z - v) + logDeriv B z
  have hdsub : DifferentiableAt ℂ (fun w : ℂ => w - v) z :=
    differentiableAt_id.sub_const v
  have hdpow : DifferentiableAt ℂ
      (fun w : ℂ => (w - v) ^ analyticOrderNatAt f v) z := hdsub.pow _
  rw [(logDeriv_congr_nhds heq).self_of_nhds,
    logDeriv_mul z hpow hBzne hdpow hBz.differentiableAt,
    logDeriv_fun_pow hdsub]
  simp only [logDeriv_apply, deriv_sub_const, deriv_id'', mul_one_div]


theorem Submission.p10_17ae7b7d_cld_local_logderiv_bound :
    ∀ (A : ℂ → ℂ), AnalyticAt ℂ A 0 → analyticOrderAt A 0 ≠ ⊤ →
      ∃ r M : ℝ, 0 < r ∧ 0 ≤ M ∧
        DifferentiableOn ℂ A (Metric.ball (0 : ℂ) r) ∧
        ∀ q : ℂ, q ≠ 0 → ‖q‖ < r → A q ≠ 0 ∧
          ‖q * deriv A q / A q - (analyticOrderNatAt A 0 : ℂ)‖ ≤ M * ‖q‖ := by
  intro A hA hfinite
  obtain ⟨B, hB, hB0, hfactor⟩ := hA.analyticOrderAt_ne_top.mp hfinite
  let m := analyticOrderNatAt A 0
  have hlocal : ∀ᶠ q in nhds (0 : ℂ),
      AnalyticAt ℂ B q ∧ B q ≠ 0 ∧ A q = q ^ m * B q := by
    filter_upwards [hB.eventually_analyticAt, hB.continuousAt.eventually_ne hB0,
      hfactor] with q hBq hBq0 hAq
    exact ⟨hBq, hBq0, by simpa only [sub_zero, smul_eq_mul] using hAq⟩
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp hlocal
  have hdB : DifferentiableOn ℂ B (Metric.ball (0 : ℂ) ρ) := by
    intro q hq
    exact (hball hq).1.differentiableAt.differentiableWithinAt
  have hG : ContinuousOn (fun q => deriv B q / B q) (Metric.ball (0 : ℂ) ρ) :=
    ((hdB.deriv Metric.isOpen_ball).div hdB (fun q hq => (hball hq).2.1)).continuousOn
  have hsub : Metric.closedBall (0 : ℂ) (ρ / 2) ⊆ Metric.ball (0 : ℂ) ρ :=
    Metric.closedBall_subset_ball (by linarith)
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) (ρ / 2)).exists_bound_of_continuousOn
    (hG.mono hsub)
  have heq : ∀ q ∈ Metric.ball (0 : ℂ) ρ,
      A =ᶠ[nhds q] fun z => z ^ m * B z := by
    intro q hq
    filter_upwards [Metric.isOpen_ball.mem_nhds hq] with z hz
    exact (hball hz).2.2
  refine ⟨ρ / 2, max M 0, half_pos hρ, le_max_right _ _, ?_, ?_⟩
  · intro q hq
    have hqρ := hsub (Metric.ball_subset_closedBall hq)
    have hprod : DifferentiableAt ℂ (fun z : ℂ => z ^ m * B z) q :=
      (differentiableAt_id.pow m).mul (hball hqρ).1.differentiableAt
    exact (hprod.congr_of_eventuallyEq (heq q hqρ)).differentiableWithinAt
  · intro q hq0 hqr
    have hq : q ∈ Metric.closedBall (0 : ℂ) (ρ / 2) := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hqr.le
    have hqρ := hsub hq
    have hBq := (hball hqρ).2.1
    have hAq : A q ≠ 0 := by
      rw [(hball hqρ).2.2]
      exact mul_ne_zero (pow_ne_zero _ hq0) hBq
    have hlog : logDeriv A q = (m : ℂ) / q + deriv B q / B q := by
      calc
        logDeriv A q = logDeriv (fun z => z ^ m * B z) q :=
          (logDeriv_congr_nhds (heq q hqρ)).self_of_nhds
        _ = logDeriv (fun z : ℂ => z ^ m) q + logDeriv B q :=
          logDeriv_mul (f := fun z : ℂ => z ^ m) (g := B) q
            (pow_ne_zero _ hq0) hBq (differentiableAt_id.pow m)
            (hball hqρ).1.differentiableAt
        _ = (m : ℂ) / q + deriv B q / B q :=
          congrArg (fun c : ℂ => c + logDeriv B q) (logDeriv_pow q m)
    have hid : q * deriv A q / A q - (m : ℂ) = q * (deriv B q / B q) := by
      rw [mul_div_assoc, ← logDeriv_apply, hlog, mul_add,
        mul_div_cancel₀ _ hq0]
      ring
    refine ⟨hAq, ?_⟩
    change ‖q * deriv A q / A q - (m : ℂ)‖ ≤ max M 0 * ‖q‖
    rw [hid, norm_mul, mul_comm (max M 0)]
    exact mul_le_mul_of_nonneg_left ((hM q hq).trans (le_max_left _ _)) (norm_nonneg q)

theorem Submission.p10_17ae7b7d_indent_mobius_arc_estimates :
    ∀ (v : ℂ) (ε : ℝ), 0 < v.im → 0 < ε → ε < 1 →
      let w : ℝ → ℂ := fun t => (ε : ℂ) * Complex.exp ((t : ℂ) * Complex.I)
      let γ : ℝ → ℂ := fun t => (v - star v * w t) / (1 - w t)
      Continuous γ ∧ Continuous (deriv γ) ∧ ∀ t : ℝ,
        γ t ≠ v ∧
        γ t - v = (v - star v) * w t / (1 - w t) ∧
        HasDerivAt γ ((v - star v) * Complex.I * w t / (1 - w t) ^ 2) t ∧
        deriv γ t / (γ t - v) = Complex.I / (1 - w t) ∧
        ‖γ t - v‖ ≤ ‖v - star v‖ * ε / (1 - ε) ∧
        ‖deriv γ t‖ ≤ ‖v - star v‖ * ε / (1 - ε) ^ 2 ∧
        ‖deriv γ t / (γ t - v) - Complex.I‖ ≤ ε / (1 - ε) := by
  intro v ε hv hε hε1
  dsimp only
  let w : ℝ → ℂ := fun t => (ε : ℂ) * Complex.exp ((t : ℂ) * Complex.I)
  let γ : ℝ → ℂ := fun t => (v - star v * w t) / (1 - w t)
  change Continuous γ ∧ Continuous (deriv γ) ∧ _
  have hc : v - star v ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp at hi
    linarith
  have hwcircle : w = circleMap 0 ε := by
    funext t
    simp only [w, circleMap, zero_add]
  have hwnorm (t : ℝ) : ‖w t‖ = ε := by
    rw [hwcircle, norm_circleMap_zero, abs_of_pos hε]
  have hwne (t : ℝ) : w t ≠ 0 :=
    norm_pos_iff.mp (by rw [hwnorm]; exact hε)
  have hpos : 0 < 1 - ε := sub_pos.mpr hε1
  have hbound (t : ℝ) : 1 - ε ≤ ‖1 - w t‖ := by
    simpa only [norm_one, hwnorm] using norm_sub_norm_le (1 : ℂ) (w t)
  have hden (t : ℝ) : 1 - w t ≠ 0 :=
    norm_pos_iff.mp (lt_of_lt_of_le hpos (hbound t))
  have hwderiv (t : ℝ) : HasDerivAt w (Complex.I * w t) t := by
    rw [hwcircle]
    simpa only [mul_comm] using hasDerivAt_circleMap 0 ε t
  have hwcont : Continuous w :=
    (show Differentiable ℝ w from fun t => (hwderiv t).differentiableAt).continuous
  have hsub (t : ℝ) : γ t - v = (v - star v) * w t / (1 - w t) := by
    dsimp only [γ]
    field_simp [hden t]
    ring
  have hγderiv (t : ℝ) :
      HasDerivAt γ ((v - star v) * Complex.I * w t / (1 - w t) ^ 2) t := by
    have hd := (((hwderiv t).const_mul (star v)).const_sub v).div
      ((hwderiv t).const_sub 1) (hden t)
    convert hd using 1 <;> first | rfl | ring
  have hderiv (t : ℝ) :
      deriv γ t = (v - star v) * Complex.I * w t / (1 - w t) ^ 2 :=
    (hγderiv t).deriv
  refine ⟨(show Differentiable ℝ γ from fun t => (hγderiv t).differentiableAt).continuous,
    ?_, ?_⟩
  · have heq : deriv γ = fun t =>
        (v - star v) * Complex.I * w t / (1 - w t) ^ 2 := funext hderiv
    rw [heq]
    exact (continuous_const.mul hwcont).div
      ((continuous_const.sub hwcont).pow 2) (fun t => pow_ne_zero 2 (hden t))
  · intro t
    have hratio : deriv γ t / (γ t - v) = Complex.I / (1 - w t) := by
      rw [hderiv, hsub]
      field_simp [hc, hwne t, hden t]
    refine ⟨?_, hsub t, hγderiv t, hratio, ?_, ?_, ?_⟩
    · apply sub_ne_zero.mp
      rw [hsub]
      exact div_ne_zero (mul_ne_zero hc (hwne t)) (hden t)
    · rw [hsub, norm_div, norm_mul, hwnorm]
      exact div_le_div_of_nonneg_left (mul_nonneg (norm_nonneg _) hε.le) hpos (hbound t)
    · rw [hderiv, norm_div, norm_mul, norm_mul, Complex.norm_I, mul_one, hwnorm,
        norm_pow]
      exact div_le_div_of_nonneg_left (mul_nonneg (norm_nonneg _) hε.le)
        (sq_pos_of_pos hpos) (pow_le_pow_left₀ hpos.le (hbound t) 2)
    · rw [hratio]
      have heq : Complex.I / (1 - w t) - Complex.I =
          Complex.I * w t / (1 - w t) := by
        field_simp [hden t]
        ring
      rw [heq, norm_div, norm_mul, Complex.norm_I, one_mul, hwnorm]
      exact div_le_div_of_nonneg_left hε.le hpos (hbound t)

theorem Submission.p10_17ae7b7d_cpd_orbit_product_order :
    ∀ (w : ℕ) (ζ : ℂ) (A : ℂ → ℂ), 0 < w → ζ ^ w = 1 →
      AnalyticAt ℂ A 0 → analyticOrderAt A 0 ≠ ⊤ →
      let P : ℂ → ℂ := fun t => ∏ j ∈ Finset.range w, A (ζ ^ j * t)
      AnalyticAt ℂ P 0 ∧ analyticOrderAt P 0 ≠ ⊤ ∧
        analyticOrderNatAt P 0 = w * analyticOrderNatAt A 0 ∧
        ∀ t : ℂ, P (ζ * t) = P t := by
  intro w ζ A hw hζ hA hfinite
  have hζ0 : ζ ≠ 0 := by
    intro hzero
    simp only [hzero, zero_pow (Nat.ne_of_gt hw)] at hζ
    exact zero_ne_one hζ
  obtain ⟨hP, hPfinite, hPorder⟩ :=
    Submission.p10_17ae7b7d_cpo_analytic_order_nonzero w ζ A hζ0 hA hfinite
  exact ⟨hP, hPfinite, hPorder,
    Submission.p10_17ae7b7d_cpo_rotation_invariant w ζ A hw hζ⟩

theorem Submission.p10_17ae7b7d_ppr_nonunit_card :
    ∀ (p a : ℕ), p.Prime → 0 < a →
      Nat.card {z : ZMod (p ^ a) // ¬ IsUnit z} = p ^ (a - 1) := by
  intro p a hp ha
  have hpow : p ^ a = p * p ^ (a - 1) := by
    calc
      p ^ a = p ^ ((a - 1) + 1) := by congr 1; omega
      _ = p * p ^ (a - 1) := by rw [pow_succ, Nat.mul_comm]
  let : NeZero (p ^ a) := ⟨pow_ne_zero a hp.ne_zero⟩
  have hnonunit (z : ZMod (p ^ a)) : ¬ IsUnit z ↔ p ∣ z.val := by
    simpa only [ZMod.natCast_zmod_val, not_not] using
      not_congr (ZMod.isUnit_natCast_iff_not_dvd_pow (a := z.val) hp ha)
  let f : Fin (p ^ (a - 1)) → {z : ZMod (p ^ a) // ¬ IsUnit z} := fun k =>
    ⟨((p * k.val : ℕ) : ZMod (p ^ a)), fun h =>
      ((ZMod.isUnit_natCast_iff_not_dvd_pow hp ha).mp h) (dvd_mul_right p k.val)⟩
  have hval (k : Fin (p ^ (a - 1))) : (f k).val.val = p * k.val := by
    change ((p * k.val : ℕ) : ZMod (p ^ a)).val = p * k.val
    apply ZMod.val_natCast_of_lt
    rw [hpow]
    exact Nat.mul_lt_mul_of_pos_left k.isLt hp.pos
  have hinj : Function.Injective f := by
    intro k l h
    apply Fin.ext
    apply Nat.eq_of_mul_eq_mul_left hp.pos
    exact (hval k).symm.trans
      ((congrArg (fun z : {z : ZMod (p ^ a) // ¬ IsUnit z} => z.val.val) h).trans (hval l))
  have hsurj : Function.Surjective f := by
    intro z
    obtain ⟨k, hk⟩ := (hnonunit z.val).mp z.property
    have hlt : k < p ^ (a - 1) := by
      apply Nat.lt_of_mul_lt_mul_left
      rw [← hk, ← hpow]
      exact ZMod.val_lt z.val
    refine ⟨⟨k, hlt⟩, ?_⟩
    apply Subtype.ext
    change ((p * k : ℕ) : ZMod (p ^ a)) = z.val
    rw [← hk, ZMod.natCast_zmod_val]
  calc
    Nat.card {z : ZMod (p ^ a) // ¬ IsUnit z} = Nat.card (Fin (p ^ (a - 1))) :=
      (Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)).symm
    _ = p ^ (a - 1) := Nat.card_fin _
/-- Count elliptic fixed cosets by their unique normalized bottom rows. -/
theorem Submission.p10_17ae7b7d_cc_elliptic_fixed_points :
    ∀ (N : ℕ) [NeZero N],
      let Q := (Matrix.SpecialLinearGroup (Fin 2) ℤ) ⧸ CongruenceSubgroup.Gamma0 N
      Nat.card {q : Q // ModularGroup.S • q = q} = ModularCurve.nuTwo N ∧
        Nat.card {q : Q // (ModularGroup.S * ModularGroup.T) • q = q} =
          ModularCurve.nuThree N := by
  intro N _
  classical
  let G := Matrix.SpecialLinearGroup (Fin 2) ℤ
  let Q := G ⧸ CongruenceSubgroup.Gamma0 N
  let R := ZMod N
  -- Choose integral lifts of the normalized unimodular rows (1,t).
  have hlift (t : R) : ∃ A : G, (A 1 0 : R) = 1 ∧ (A 1 1 : R) = t :=
    Submission.p10_17ae7b7d_cc_lift_unimodular_row N 1 t ⟨1, 0, by simp⟩
  choose L hL₀ hL₁ using hlift
  let f (t : R) : Q := QuotientGroup.mk (L t)⁻¹
  have hf_inj : Function.Injective f := by
    intro t t' h
    obtain ⟨u, hu, ht⟩ :=
      (Submission.p10_17ae7b7d_efp_inverse_coset_eq_iff N (L t) (L t')).mp h
    rw [hL₀, hL₀, mul_one] at hu
    rw [hL₁, hL₁, ← hu, one_mul] at ht
    exact ht.symm
  -- Inversion turns right multiplication on rows into inverse left action.
  have hcount (B : G) (k : R)
      (hB : ∀ A : G, ((A * B) 1 0 : R) = (A 1 1 : R) ∧
        ((A * B) 1 1 : R) = k * (A 1 1 : R) - (A 1 0 : R)) :
      Nat.card {q : Q // B • q = q} = Nat.card {t : R // t ^ 2 - k * t + 1 = 0} := by
    have hnorm (A : G) :
        B • (QuotientGroup.mk A⁻¹ : Q) = QuotientGroup.mk A⁻¹ ↔
          IsUnit (A 1 0 : R) ∧
            ∃! t : R, (A 1 1 : R) = (A 1 0 : R) * t ∧ t ^ 2 - k * t + 1 = 0 := by
      have hrow : ∃ x y : R, x * (A 1 0 : R) + y * (A 1 1 : R) = 1 := by
        obtain ⟨x, y, hxy⟩ := A.isCoprime_row 1
        refine ⟨(x : R), (y : R), ?_⟩
        have h := congrArg (Int.castRingHom R) hxy
        simpa only [map_add, map_mul, map_one, Int.coe_castRingHom] using h
      rw [smul_eq_iff_eq_inv_smul]
      change (QuotientGroup.mk A⁻¹ : Q) = QuotientGroup.mk (B⁻¹ * A⁻¹) ↔ _
      rw [← mul_inv_rev, Submission.p10_17ae7b7d_efp_inverse_coset_eq_iff N A (A * B)]
      simp only [(hB A).1, (hB A).2]
      exact Submission.p10_17ae7b7d_efp_unimodular_eigenrow_iff R k _ _ hrow
    have hf_fixed (t : R) (ht : t ^ 2 - k * t + 1 = 0) : B • f t = f t := by
      apply (hnorm (L t)).mpr
      rw [hL₀, hL₁]
      refine ⟨isUnit_one, t, ⟨by simp, ht⟩, ?_⟩
      intro y hy
      simpa only [one_mul] using hy.1.symm
    let g : {t : R // t ^ 2 - k * t + 1 = 0} → {q : Q // B • q = q} :=
      fun t => ⟨f t, hf_fixed t t.property⟩
    apply (Nat.card_eq_of_bijective g ?_).symm
    constructor
    · intro t t' h
      exact Subtype.ext (hf_inj (congrArg Subtype.val h))
    · intro q
      obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective q.val
      let A : G := a⁻¹
      have hA : (QuotientGroup.mk A⁻¹ : Q) = q.val := by
        change (QuotientGroup.mk (a⁻¹)⁻¹ : Q) = q.val
        rw [inv_inv]
        exact ha
      have hfixed : B • (QuotientGroup.mk A⁻¹ : Q) = QuotientGroup.mk A⁻¹ := by
        rw [hA]
        exact q.property
      obtain ⟨⟨u, hu⟩, t, ⟨hst, ht⟩, _⟩ := (hnorm A).mp hfixed
      refine ⟨⟨t, ht⟩, Subtype.ext ?_⟩
      change f t = q.val
      rw [← hA]
      apply (Submission.p10_17ae7b7d_efp_inverse_coset_eq_iff N (L t) A).mpr
      refine ⟨u, ?_, ?_⟩
      · rw [hL₀, mul_one]
        exact hu.symm
      · rw [hL₁, hu]
        exact hst
  constructor
  · have h := hcount ModularGroup.S 0 (by
      intro A
      change ((A.1 * ModularGroup.S.1) 1 0 : R) = (A 1 1 : R) ∧
        ((A.1 * ModularGroup.S.1) 1 1 : R) = 0 * (A 1 1 : R) - (A 1 0 : R)
      simp [Matrix.mul_apply, Fin.sum_univ_two, ModularGroup.S, R])
    simpa only [zero_mul, sub_zero, ModularCurve.nuTwo] using h
  · have h := hcount (ModularGroup.S * ModularGroup.T) 1 (by
      intro A
      change ((A.1 * (ModularGroup.S.1 * ModularGroup.T.1)) 1 0 : R) = (A 1 1 : R) ∧
        ((A.1 * (ModularGroup.S.1 * ModularGroup.T.1)) 1 1 : R) =
          1 * (A 1 1 : R) - (A 1 0 : R)
      simp [Matrix.mul_apply, Fin.sum_univ_two, ModularGroup.S, ModularGroup.T,
        R, sub_eq_add_neg, add_comm])
    apply h.trans
    unfold ModularCurve.nuThree
    -- Negation changes t² - t + 1 into the defining polynomial for nuThree.
    apply Nat.card_congr
    refine
      { toFun := fun t => ⟨-t.val, ?_⟩
        invFun := fun x => ⟨-x.val, ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · calc
        (-t.val) ^ 2 + -t.val + 1 = t.val ^ 2 - 1 * t.val + 1 := by ring
        _ = 0 := t.property
    · calc
        (-x.val) ^ 2 - 1 * -x.val + 1 = x.val ^ 2 + x.val + 1 := by ring
        _ = 0 := x.property
    · intro t
      apply Subtype.ext
      exact neg_neg t.val
    · intro x
      apply Subtype.ext
      exact neg_neg x.val
theorem Submission.p10_17ae7b7d_pp_stratum_card :
    ∀ (p a j : ℕ), Nat.Prime p → 1 ≤ j → j < a →
      Nat.card {z : ZMod (p ^ a) // p ^ j ∣ z.val ∧ ¬ p ^ (j + 1) ∣ z.val} =
        Nat.totient (p ^ min j (a - j)) * p ^ (a - 2 * j) := by
  classical
  intro p a j hp hj hja
  have : NeZero (p ^ a) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hcount (k : ℕ) (hk : k ≤ a) :
      (Finset.univ.filter (fun z : ZMod (p ^ a) => p ^ k ∣ z.val)).card = p ^ (a - k) := by
    have hpk : 0 < p ^ k := pow_pos hp.pos _
    have hpa : p ^ k * p ^ (a - k) = p ^ a := by
      rw [← pow_add, Nat.add_sub_of_le hk]
    have hbound (t : Fin (p ^ (a - k))) : p ^ k * t.val < p ^ a := by
      rw [← hpa]
      exact Nat.mul_lt_mul_of_pos_left t.isLt hpk
    let f : Fin (p ^ (a - k)) → {z : ZMod (p ^ a) // p ^ k ∣ z.val} :=
      fun t => ⟨(p ^ k * t.val : ℕ), by
        rw [ZMod.val_natCast_of_lt (hbound t)]
        exact dvd_mul_right _ _⟩
    have hfval (t : Fin (p ^ (a - k))) : (f t).val.val = p ^ k * t.val :=
      ZMod.val_natCast_of_lt (hbound t)
    have hbij : Function.Bijective f := by
      constructor
      · intro t u h
        apply Fin.ext
        apply Nat.eq_of_mul_eq_mul_left hpk
        simpa only [hfval] using congrArg (fun z => z.val.val) h
      · intro z
        obtain ⟨t, ht⟩ := z.property
        have htlt : t < p ^ (a - k) := by
          apply (Nat.mul_lt_mul_left hpk).mp
          rw [hpa, ← ht]
          exact ZMod.val_lt z.val
        refine ⟨⟨t, htlt⟩, Subtype.ext ?_⟩
        change ((p ^ k * t : ℕ) : ZMod (p ^ a)) = z.val
        rw [← ht, ZMod.natCast_zmod_val]
    rw [← Fintype.card_subtype]
    simpa using (Fintype.card_congr (Equiv.ofBijective f hbij)).symm
  have hsub :
      Finset.univ.filter (fun z : ZMod (p ^ a) => p ^ (j + 1) ∣ z.val) ⊆
        Finset.univ.filter (fun z : ZMod (p ^ a) => p ^ j ∣ z.val) := by
    intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    exact dvd_trans (pow_dvd_pow p (by omega : j ≤ j + 1)) hz
  have hstratum :
      Finset.univ.filter (fun z : ZMod (p ^ a) => p ^ j ∣ z.val ∧ ¬ p ^ (j + 1) ∣ z.val) =
        (Finset.univ.filter (fun z : ZMod (p ^ a) => p ^ j ∣ z.val)) \
          (Finset.univ.filter (fun z : ZMod (p ^ a) => p ^ (j + 1) ∣ z.val)) := by
    ext z
    simp
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, hstratum,
    Finset.card_sdiff_of_subset hsub, hcount j hja.le, hcount (j + 1) (by omega)]
  have hpos : 0 < min j (a - j) := by omega
  rw [Nat.totient_prime_pow hp hpos]
  have hexp : a - j = (a - (j + 1)) + 1 := by omega
  have he : a - (j + 1) = min j (a - j) - 1 + (a - 2 * j) := by omega
  calc
    p ^ (a - j) - p ^ (a - (j + 1)) = p ^ (a - (j + 1)) * (p - 1) := by
      simp only [hexp, pow_succ, Nat.mul_sub_left_distrib, Nat.mul_one]
    _ = (p ^ (min j (a - j) - 1) * p ^ (a - 2 * j)) * (p - 1) := by
      rw [← pow_add, ← he]
    _ = p ^ (min j (a - j) - 1) * (p - 1) * p ^ (a - 2 * j) := by ac_rfl

namespace Submission

theorem p10_17ae7b7d_valence_indentation_limit
    (f : ℂ → ℂ) (v : ℂ) (hv : 0 < v.im) (hf : AnalyticAt ℂ f v)
    (horder : analyticOrderAt f v ≠ ⊤)
    (α β : ℝ → ℝ) (a b : ℝ)
    (hα : Filter.Tendsto α (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds a))
    (hβ : Filter.Tendsto β (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds b)) :
    let γ : ℝ → ℝ → ℂ := fun ε t =>
      (v - star v * ((ε : ℂ) * Complex.exp ((t : ℂ) * Complex.I))) /
        (1 - (ε : ℂ) * Complex.exp ((t : ℂ) * Complex.I))
    Filter.Tendsto
      (fun ε : ℝ => intervalIntegral
        (fun t : ℝ => (deriv f (γ ε t) / f (γ ε t)) * deriv (γ ε) t)
        (α ε) (β ε) MeasureTheory.volume)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (Complex.I * (analyticOrderNatAt f v : ℂ) * ((b - a : ℝ) : ℂ))) := by
  dsimp only
  let γ : ℝ → ℝ → ℂ := fun ε t =>
    (v - star v * ((ε : ℂ) * Complex.exp ((t : ℂ) * Complex.I))) /
      (1 - (ε : ℂ) * Complex.exp ((t : ℂ) * Complex.I))
  let F : ℝ → ℝ → ℂ := fun ε t =>
    (deriv f (γ ε t) / f (γ ε t)) * deriv (γ ε) t
  let m : ℂ := (analyticOrderNatAt f v : ℂ)
  obtain ⟨r, M, G, hr, hM, hG, hGbound, hlog⟩ :=
    p10_17ae7b7d_indent_logderiv_remainder f v hf horder
  let δ : ℝ → ℝ := fun ε =>
    ‖m‖ * (ε / (1 - ε)) + M * (‖v - star v‖ * ε / (1 - ε) ^ 2)
  have hε : Filter.Tendsto (fun ε : ℝ => ε)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) :=
    Filter.tendsto_id.mono_left nhdsWithin_le_nhds
  have hden : Filter.Tendsto (fun ε : ℝ => 1 - ε)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hε
  have hshrink : Filter.Tendsto (fun ε : ℝ => ‖v - star v‖ * ε / (1 - ε))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    simpa [Pi.div_def] using (hε.const_mul ‖v - star v‖).div hden (by norm_num)
  have hδ : Filter.Tendsto δ
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have hfirst : Filter.Tendsto (fun ε : ℝ => ε / (1 - ε))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
      simpa [Pi.div_def] using hε.div hden (by norm_num)
    have hsecond : Filter.Tendsto (fun ε : ℝ => ‖v - star v‖ * ε / (1 - ε) ^ 2)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
      simpa [Pi.div_def] using (hε.const_mul ‖v - star v‖).div (hden.pow 2) (by norm_num)
    simpa [δ] using (hfirst.const_mul ‖m‖).add (hsecond.const_mul M)
  apply p10_17ae7b7d_indent_moving_interval_limit F α β δ (Complex.I * m) a b hα hβ hδ
  filter_upwards [self_mem_nhdsWithin, hε.eventually_lt_const (by norm_num : (0 : ℝ) < 1),
    hshrink.eventually_lt_const hr] with ε hεpos hεone hεsmall
  have hεpos' : 0 < ε := hεpos
  obtain ⟨hγ, hdγ, hest⟩ := p10_17ae7b7d_indent_mobius_arc_estimates v ε hv hεpos' hεone
  change Continuous (γ ε) at hγ
  change Continuous (deriv (γ ε)) at hdγ
  have hball (t : ℝ) : γ ε t ∈ Metric.ball v r := by
    rw [Metric.mem_ball, dist_eq_norm]
    exact lt_of_le_of_lt (hest t).2.2.2.2.1 hεsmall
  have hclosed (t : ℝ) : γ ε t ∈ Metric.closedBall v r :=
    Metric.ball_subset_closedBall (hball t)
  have hlogγ (t : ℝ) : deriv f (γ ε t) / f (γ ε t) = m / (γ ε t - v) + G (γ ε t) :=
    (hlog (γ ε t) (hball t) (hest t).1).2
  have hGc : Continuous (fun t : ℝ => G (γ ε t)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (hG (γ ε t) (hclosed t)).continuousAt.comp hγ.continuousAt
  have hFc : Continuous (F ε) := by
    have heq : F ε = fun t => (m / (γ ε t - v) + G (γ ε t)) * deriv (γ ε) t := by
      funext t
      exact congrArg (fun z : ℂ => z * deriv (γ ε) t) (hlogγ t)
    rw [heq]
    exact ((continuous_const.div (hγ.sub continuous_const)
      (fun t => sub_ne_zero.mpr (hest t).1)).add hGc).mul hdγ
  refine ⟨hFc.intervalIntegrable _ _, ?_⟩
  intro t
  have herror : F ε t - Complex.I * m =
      m * (deriv (γ ε) t / (γ ε t - v) - Complex.I) + G (γ ε t) * deriv (γ ε) t := by
    dsimp only [F]
    rw [hlogγ t]
    ring
  rw [herror]
  calc
    ‖m * (deriv (γ ε) t / (γ ε t - v) - Complex.I) + G (γ ε t) * deriv (γ ε) t‖
        ≤ ‖m‖ * ‖deriv (γ ε) t / (γ ε t - v) - Complex.I‖ +
          ‖G (γ ε t)‖ * ‖deriv (γ ε) t‖ := by
            simpa only [norm_mul] using norm_add_le
              (m * (deriv (γ ε) t / (γ ε t - v) - Complex.I))
              (G (γ ε t) * deriv (γ ε) t)
    _ ≤ δ ε := add_le_add
      (mul_le_mul_of_nonneg_left (hest t).2.2.2.2.2.2 (norm_nonneg m))
      (mul_le_mul (hGbound (γ ε t) (hclosed t)) (hest t).2.2.2.2.2.1
        (norm_nonneg _) hM)

end Submission
theorem Submission.p10_17ae7b7d_crt_ring_equiv_rows :
    ∀ (R S : Type) [CommRing R] [CommRing S], (R ≃+* S) →
      let P := fun (A : Type) [CommRing A] =>
        Quot (fun v w : {v : A × A // ∃ x y : A, x * v.1 + y * v.2 = 1} =>
          ∃ u : Aˣ, (u : A) * v.1.1 = w.1.1 ∧ (u : A) * v.1.2 = w.1.2)
      Nonempty (P R ≃ P S) := by
  intro R S _ _ e
  let f : {v : R × R // ∃ x y : R, x * v.1 + y * v.2 = 1} ≃
      {v : S × S // ∃ x y : S, x * v.1 + y * v.2 = 1} :=
    { toFun := fun v => ⟨(e v.1.1, e v.1.2), by
        obtain ⟨x, y, hxy⟩ := v.2
        exact ⟨e x, e y, by simpa only [map_add, map_mul, map_one] using congrArg e hxy⟩⟩
      invFun := fun v => ⟨(e.symm v.1.1, e.symm v.1.2), by
        obtain ⟨x, y, hxy⟩ := v.2
        exact ⟨e.symm x, e.symm y, by
          simpa only [map_add, map_mul, map_one] using congrArg e.symm hxy⟩⟩
      left_inv := fun v => Subtype.ext (Prod.ext
        (e.symm_apply_apply v.1.1) (e.symm_apply_apply v.1.2))
      right_inv := fun v => Subtype.ext (Prod.ext
        (e.apply_symm_apply v.1.1) (e.apply_symm_apply v.1.2)) }
  refine ⟨Quot.congr f ?_⟩
  intro v w
  constructor
  · rintro ⟨u, h₁, h₂⟩
    refine ⟨Units.map e.toMonoidHom u, ?_, ?_⟩
    · change e (u : R) * e v.1.1 = e w.1.1
      simpa only [map_mul] using congrArg e h₁
    · change e (u : R) * e v.1.2 = e w.1.2
      simpa only [map_mul] using congrArg e h₂
  · rintro ⟨u, h₁, h₂⟩
    change (u : S) * e v.1.1 = e w.1.1 at h₁
    change (u : S) * e v.1.2 = e w.1.2 at h₂
    refine ⟨Units.map e.symm.toMonoidHom u, ?_, ?_⟩
    · change e.symm (u : S) * v.1.1 = w.1.1
      simpa only [map_mul, e.symm_apply_apply] using congrArg e.symm h₁
    · change e.symm (u : S) * v.1.2 = w.1.2
      simpa only [map_mul, e.symm_apply_apply] using congrArg e.symm h₂
theorem Submission.p10_17ae7b7d_fi_square_annihilation :
    ∀ (p a j : ℕ), Nat.Prime p → j < a → ∀ z : ZMod (p ^ a),
      p ^ j ∣ z.val → ¬ p ^ (j + 1) ∣ z.val → ∀ n : ℕ,
      ((n : ZMod (p ^ a)) * z ^ 2 = 0 ↔ p ^ (a - 2 * j) ∣ n) := by
  intro p a j hp _hja z hz hznext n
  have : NeZero (p ^ a) := ⟨pow_ne_zero _ hp.ne_zero⟩
  obtain ⟨v, hv⟩ := hz
  have hpv : ¬ p ∣ v := by
    rintro ⟨w, hw⟩
    apply hznext
    refine ⟨w, ?_⟩
    rw [hv, hw, pow_succ, mul_assoc]
  have hcop : (p ^ a).Coprime (v ^ 2) :=
    (hp.coprime_pow_of_not_dvd hpv).symm.pow_right 2
  have hcast : ((n * z.val ^ 2 : ℕ) : ZMod (p ^ a)) =
      (n : ZMod (p ^ a)) * z ^ 2 := by
    simp only [Nat.cast_mul, Nat.cast_pow, ZMod.natCast_zmod_val]
  rw [← hcast, ZMod.natCast_eq_zero_iff, hv, mul_pow, ← pow_mul,
    Nat.mul_comm j 2, ← mul_assoc, hcop.dvd_mul_right]
  by_cases h : 2 * j ≤ a
  · have hpow : p ^ a = p ^ (2 * j) * p ^ (a - 2 * j) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hpow, mul_comm n (p ^ (2 * j)),
      Nat.mul_dvd_mul_iff_left (pow_pos hp.pos _)]
  · have ha : a ≤ 2 * j := by omega
    exact iff_of_true (dvd_mul_of_dvd_right (pow_dvd_pow p ha) n)
      (by simp [Nat.sub_eq_zero_of_le ha])
theorem Submission.p10_17ae7b7d_crt_pi_rows :
    ∀ (ι : Type) [Fintype ι] (R : ι → Type) [∀ i, CommRing (R i)],
      let P := fun (A : Type) [CommRing A] =>
        Quot (fun v w : {v : A × A // ∃ x y : A, x * v.1 + y * v.2 = 1} =>
          ∃ u : Aˣ, (u : A) * v.1.1 = w.1.1 ∧ (u : A) * v.1.2 = w.1.2)
      Nonempty (P (∀ i, R i) ≃ (∀ i, P (R i))) := by
  classical
  intro ι _ R _
  let U := fun (A : Type) [CommRing A] =>
    {v : A × A // ∃ x y : A, x * v.1 + y * v.2 = 1}
  let rel := fun (A : Type) [CommRing A] (v w : U A) =>
    ∃ u : Aˣ, (u : A) * v.1.1 = w.1.1 ∧ (u : A) * v.1.2 = w.1.2
  have hrel (A : Type) [CommRing A] : Equivalence (rel A) := by
    refine ⟨fun v => ⟨1, by simp, by simp⟩, ?_, ?_⟩
    · rintro v w ⟨u, h1, h2⟩
      exact ⟨u⁻¹, by rw [← h1, Units.inv_mul_cancel_left],
        by rw [← h2, Units.inv_mul_cancel_left]⟩
    · rintro v w z ⟨u, h1, h2⟩ ⟨u', h1', h2'⟩
      exact ⟨u' * u, by rw [Units.val_mul, mul_assoc, h1, h1'],
        by rw [Units.val_mul, mul_assoc, h2, h2']⟩
  let ev : U (∀ i, R i) → ∀ i, U (R i) := fun v i =>
    ⟨(v.1.1 i, v.1.2 i), by
      obtain ⟨x, y, hxy⟩ := v.2
      exact ⟨x i, y i, congrFun hxy i⟩⟩
  let F : Quot (rel (∀ i, R i)) → ∀ i, Quot (rel (R i)) :=
    Quot.lift (fun v i => Quot.mk _ (ev v i)) (by
      rintro v w ⟨u, h1, h2⟩
      funext i
      exact Quot.sound ⟨MulEquiv.piUnits u i, congrFun h1 i, congrFun h2 i⟩)
  change Nonempty (Quot (rel (∀ i, R i)) ≃ (∀ i, Quot (rel (R i))))
  refine ⟨Equiv.ofBijective F ⟨?_, ?_⟩⟩
  · intro a b
    refine Quot.inductionOn a (fun v => ?_)
    refine Quot.inductionOn b (fun w => ?_)
    intro h
    have hscale : ∀ i, ∃ u : (R i)ˣ,
        (u : R i) * (ev v i).1.1 = (ev w i).1.1 ∧
        (u : R i) * (ev v i).1.2 = (ev w i).1.2 := by
      intro i
      exact ((hrel (R i)).quot_mk_eq_iff (ev v i) (ev w i)).mp (congrFun h i)
    choose u h1 h2 using hscale
    apply Quot.sound
    exact ⟨MulEquiv.piUnits.symm u, funext h1, funext h2⟩
  · intro q
    choose v hv using fun i => Quot.exists_rep (q i)
    have hwitness : ∀ i, ∃ x y : R i,
        x * (v i).1.1 + y * (v i).1.2 = 1 := fun i => (v i).2
    choose x y hxy using hwitness
    let row : U (∀ i, R i) :=
      ⟨(fun i => (v i).1.1, fun i => (v i).1.2), x, y, funext hxy⟩
    refine ⟨Quot.mk _ row, ?_⟩
    funext i
    change Quot.mk (rel (R i)) (ev row i) = q i
    have he : ev row i = v i := Subtype.ext rfl
    rw [he]
    exact hv i


theorem Submission.p10_17ae7b7d_idx_dedekind_psi_product :
    ∀ (N : ℕ) [NeZero N], ModularCurve.dedekindPsi N =
      N.primeFactors.prod (fun p => p ^ N.factorization p + p ^ (N.factorization p - 1)) := by
  classical
  intro N _
  have hN : N ≠ 0 := NeZero.ne N
  rw [ModularCurve.dedekindPsi, Nat.sum_divisors_filter_squarefree hN, Nat.factors_eq]
  simp only [List.toFinset_coe, Nat.toFinset_factors, Finset.prod_val]
  change (∑ s ∈ N.primeFactors.powerset, N / (∏ p ∈ s, p)) = _
  calc
    _ = ∑ s ∈ N.primeFactors.powerset,
        (∏ p ∈ s, p ^ (N.factorization p - 1)) *
          ∏ p ∈ N.primeFactors \ s, p ^ N.factorization p := by
      apply Finset.sum_congr rfl
      intro s hs
      have hsub : s ⊆ N.primeFactors := Finset.mem_powerset.mp hs
      have hpos : 0 < ∏ p ∈ s, p :=
        Finset.prod_pos fun p hp => Nat.pos_of_mem_primeFactors (hsub hp)
      have hprod : (∏ p ∈ s, p) * (∏ p ∈ s, p ^ (N.factorization p - 1)) =
          ∏ p ∈ s, p ^ N.factorization p := by
        rw [← Finset.prod_mul_distrib]
        apply Finset.prod_congr rfl
        intro p hp
        have he : 1 ≤ N.factorization p :=
          (Nat.prime_of_mem_primeFactors (hsub hp)).factorization_pos_of_dvd hN
            (Nat.dvd_of_mem_primeFactors (hsub hp))
        rw [← pow_succ', Nat.sub_add_cancel he]
      apply Nat.div_eq_of_eq_mul_right hpos
      calc
        N = ∏ p ∈ N.primeFactors, p ^ N.factorization p :=
          Nat.prod_primeFactors_pow_factorization hN
        _ = (∏ p ∈ s, p ^ N.factorization p) *
            ∏ p ∈ N.primeFactors \ s, p ^ N.factorization p := by
          rw [mul_comm, Finset.prod_sdiff hsub]
        _ = _ := by rw [← hprod, mul_assoc]
    _ = ∏ p ∈ N.primeFactors, (p ^ (N.factorization p - 1) + p ^ N.factorization p) :=
      (Finset.prod_add _ _ _).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro p _
      exact Nat.add_comm _ _
theorem Submission.p10_17ae7b7d_phdisk_mobius_bijon :
    ∀ (a b c d : ℝ), a * d - b * c = 1 →
      Set.BijOn (fun z : ℂ => ((a : ℂ) * z + (b : ℂ)) / ((c : ℂ) * z + (d : ℂ)))
        {z : ℂ | 0 < z.im} {z : ℂ | 0 < z.im} := by
  have hden (a b c d : ℝ) (hdet : a * d - b * c = 1)
      (z : ℂ) (hz : 0 < z.im) : (c : ℂ) * z + (d : ℂ) ≠ 0 := by
    intro hzero
    have him : c * z.im = 0 := by
      simpa only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, add_zero, Complex.zero_im] using
        congrArg Complex.im hzero
    have hc : c = 0 := (mul_eq_zero.mp him).resolve_right (ne_of_gt hz)
    have hd : d = 0 := by simpa [hc] using hzero
    simp [hc, hd] at hdet
  have hpos (a b c d : ℝ) (hdet : a * d - b * c = 1)
      (z : ℂ) (hz : 0 < z.im) :
      0 < (((a : ℂ) * z + (b : ℂ)) / ((c : ℂ) * z + (d : ℂ))).im := by
    have him : (((a : ℂ) * z + (b : ℂ)) / ((c : ℂ) * z + (d : ℂ))).im =
        z.im / Complex.normSq ((c : ℂ) * z + (d : ℂ)) := by
      simp only [Complex.div_im, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, add_zero, Complex.add_re, Complex.mul_re,
        sub_zero, ← sub_div]
      congr 1
      calc
        a * z.im * (c * z.re + d) - (a * z.re + b) * (c * z.im) =
            (a * d - b * c) * z.im := by ring
        _ = z.im := by rw [hdet, one_mul]
    rw [him]
    exact div_pos hz (Complex.normSq_pos.mpr (hden a b c d hdet z hz))
  have hleft (a b c d : ℝ) (hdet : a * d - b * c = 1)
      (z : ℂ) (hz : 0 < z.im) :
      ((d : ℂ) * (((a : ℂ) * z + (b : ℂ)) / ((c : ℂ) * z + (d : ℂ))) - (b : ℂ)) /
        (-(c : ℂ) * (((a : ℂ) * z + (b : ℂ)) / ((c : ℂ) * z + (d : ℂ))) + (a : ℂ)) = z := by
    have hdetC : (a : ℂ) * (d : ℂ) - (b : ℂ) * (c : ℂ) = 1 := by
      exact_mod_cast hdet
    have hq := hden a b c d hdet z hz
    have hnum : (d : ℂ) * (((a : ℂ) * z + (b : ℂ)) / ((c : ℂ) * z + (d : ℂ))) -
        (b : ℂ) = z / ((c : ℂ) * z + (d : ℂ)) := by
      apply (eq_div_iff hq).2
      rw [sub_mul, mul_assoc, div_mul_cancel₀ _ hq]
      linear_combination z * hdetC
    have hinv : -(c : ℂ) * (((a : ℂ) * z + (b : ℂ)) / ((c : ℂ) * z + (d : ℂ))) +
        (a : ℂ) = 1 / ((c : ℂ) * z + (d : ℂ)) := by
      apply (eq_div_iff hq).2
      rw [add_mul, mul_assoc, div_mul_cancel₀ _ hq]
      linear_combination hdetC
    rw [hnum, hinv, div_div_div_cancel_right₀ hq, div_one]
  intro a b c d hdet
  have hinvdet : d * a - (-b) * (-c) = 1 := by nlinarith [hdet]
  refine ⟨fun z hz => hpos a b c d hdet z hz, ?_, ?_⟩
  · intro z hz w hw heq
    have h := congrArg (fun u : ℂ => ((d : ℂ) * u - (b : ℂ)) / (-(c : ℂ) * u + (a : ℂ))) heq
    simpa only [hleft a b c d hdet z hz, hleft a b c d hdet w hw] using h
  · intro w hw
    refine ⟨((d : ℂ) * w + ((-b : ℝ) : ℂ)) / (((-c : ℝ) : ℂ) * w + (a : ℂ)),
      hpos d (-b) (-c) a hinvdet w hw, ?_⟩
    simpa only [Complex.ofReal_neg, neg_neg, sub_neg_eq_add] using
      hleft d (-b) (-c) a hinvdet w hw
theorem Submission.p10_17ae7b7d_phdisk_euclidean :
    ∀ (v : ℂ) (ε : ℝ), 0 < v.im → 0 < ε → ε < 1 →
      {z : ℂ | 0 < z.im ∧ ‖(z - v) / (z - star v)‖ ≤ ε} =
        Metric.closedBall
          ((v.re : ℂ) + ((v.im * (1 + ε ^ 2) / (1 - ε ^ 2) : ℝ) : ℂ) * Complex.I)
          (2 * v.im * ε / (1 - ε ^ 2)) := by
  intro v ε hv hε hε1
  have hΔ : 0 < 1 - ε ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hε1) (show 0 < 1 + ε by linarith)]
  let Y : ℝ := v.im * (1 + ε ^ 2) / (1 - ε ^ 2)
  let R : ℝ := 2 * v.im * ε / (1 - ε ^ 2)
  let C : ℂ := (v.re : ℂ) + (Y : ℂ) * Complex.I
  have hR : 0 < R := div_pos (mul_pos (mul_pos (by norm_num) hv) hε) hΔ
  have hYR : 0 < Y - R := by
    have heq : Y - R = v.im * (1 - ε) ^ 2 / (1 - ε ^ 2) := by
      dsimp [Y, R]
      ring
    rw [heq]
    exact div_pos (mul_pos hv (sq_pos_of_pos (sub_pos.mpr hε1))) hΔ
  have hsq (w : ℂ) : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  ext z
  change (0 < z.im ∧ ‖(z - v) / (z - star v)‖ ≤ ε) ↔ dist z C ≤ R
  rw [dist_eq_norm]
  have hidentity : (1 - ε ^ 2) * (‖z - C‖ ^ 2 - R ^ 2) =
      ‖z - v‖ ^ 2 - ε ^ 2 * ‖z - star v‖ ^ 2 := by
    simp only [hsq, C, Complex.sub_re, Complex.sub_im, Complex.add_re,
      Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.star_def,
      Complex.conj_re, Complex.conj_im, mul_zero, mul_one,
      sub_zero, add_zero, zero_add, sub_neg_eq_add]
    dsimp [Y, R]
    field_simp [hΔ.ne']
    ring
  have hshape : ‖z - C‖ ≤ R ↔
      ‖z - v‖ ^ 2 ≤ ε ^ 2 * ‖z - star v‖ ^ 2 := by
    calc
      ‖z - C‖ ≤ R ↔ ‖z - C‖ ^ 2 - R ^ 2 ≤ 0 := by
        rw [sub_nonpos, sq_le_sq₀ (norm_nonneg _) hR.le]
      _ ↔ (1 - ε ^ 2) * (‖z - C‖ ^ 2 - R ^ 2) ≤ 0 := by
        simpa only [mul_zero] using
          (mul_le_mul_iff_right₀ hΔ (b := ‖z - C‖ ^ 2 - R ^ 2) (c := 0)).symm
      _ ↔ ‖z - v‖ ^ 2 ≤ ε ^ 2 * ‖z - star v‖ ^ 2 := by
        rw [hidentity, sub_nonpos]
  have hratio (hz : 0 < z.im) : ‖(z - v) / (z - star v)‖ ≤ ε ↔
      ‖z - v‖ ^ 2 ≤ ε ^ 2 * ‖z - star v‖ ^ 2 := by
    have hden : z - star v ≠ 0 := by
      intro heq
      have him := congrArg Complex.im heq
      simp only [Complex.sub_im, Complex.star_def, Complex.conj_im,
        Complex.zero_im] at him
      linarith
    rw [norm_div, div_le_iff₀ (norm_pos_iff.mpr hden),
      ← sq_le_sq₀ (norm_nonneg _) (mul_nonneg hε.le (norm_nonneg _)), mul_pow]
  constructor
  · rintro ⟨hz, hnorm⟩
    exact hshape.mpr ((hratio hz).mp hnorm)
  · intro hball
    have him : |z.im - Y| ≤ R := by
      simpa [C] using (Complex.abs_im_le_norm (z - C)).trans hball
    have hz : 0 < z.im := by
      have hlower := (abs_le.mp him).1
      linarith
    exact ⟨hz, (hratio hz).mpr (hshape.mp hball)⟩
theorem Submission.p10_17ae7b7d_fi_unit_mul_dvd_val :
    ∀ (M d : ℕ), 0 < M → d ∣ M → ∀ (x u : ZMod M), IsUnit u →
      (d ∣ (x * u).val ↔ d ∣ x.val) := by
  intro M d hM hd x u hu
  let : NeZero M := ⟨Nat.ne_of_gt hM⟩
  let ρ : ZMod M →+* ZMod d := ZMod.castHom hd (ZMod d)
  have hval (y : ZMod M) : ρ y = 0 ↔ d ∣ y.val := by
    change (ZMod.cast y : ZMod d) = 0 ↔ d ∣ y.val
    rw [ZMod.cast_eq_val, ZMod.natCast_eq_zero_iff]
  have hinv : ρ u * ρ (u⁻¹) = 1 := by
    rw [← map_mul, ZMod.mul_inv_of_unit u hu, map_one]
  rw [← hval (x * u), ← hval x, map_mul]
  constructor
  · intro h
    calc
      ρ x = (ρ x * ρ u) * ρ (u⁻¹) := by rw [mul_assoc, hinv, mul_one]
      _ = 0 := by rw [h, zero_mul]
  · intro h
    rw [h, zero_mul]
theorem Submission.p10_17ae7b7d_valence_cusp_log_derivative :
    ∀ (F A : ℂ → ℂ), DifferentiableOn ℂ F {z : ℂ | 0 < z.im} →
      (∃ z : ℂ, 0 < z.im ∧ F z ≠ 0) → AnalyticAt ℂ A 0 →
      (∃ Y₀ : ℝ, ∀ z : ℂ, 0 < z.im → Y₀ ≤ z.im →
        F z = A (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * z))) →
      analyticOrderAt A 0 ≠ ⊤ ∧ ∃ Y C : ℝ, 0 < Y ∧ 0 ≤ C ∧
        ∀ z : ℂ, Y ≤ z.im → F z ≠ 0 ∧
          ‖deriv F z / F z -
            2 * (Real.pi : ℂ) * Complex.I * (analyticOrderNatAt A 0 : ℂ)‖ ≤
            C * Real.exp (-2 * Real.pi * z.im) := by
  intro F A hF hnonzero hA hfactor
  have hfinite := Submission.p10_17ae7b7d_cld_qexp_finite_order F A hF hnonzero hA hfactor
  obtain ⟨r, M, hr, hM, hAdiff, hbound⟩ :=
    Submission.p10_17ae7b7d_cld_local_logderiv_bound A hA hfinite
  obtain ⟨Y₀, hfactor⟩ := hfactor
  let k : ℂ := 2 * (Real.pi : ℂ) * Complex.I
  let q : ℂ → ℂ := fun z => Complex.exp (k * z)
  let T : ℝ := max (max 0 Y₀) (-Real.log r / (2 * Real.pi))
  have hT0 : 0 ≤ T := le_trans (le_max_left 0 Y₀) (le_max_left _ _)
  have hTlog : -Real.log r / (2 * Real.pi) ≤ T := le_max_right _ _
  have hexp : Real.exp (-2 * Real.pi * T) ≤ r := by
    rw [← Real.exp_log hr]
    apply Real.exp_le_exp.mpr
    have hmul := (div_le_iff₀ (by positivity : 0 < 2 * Real.pi)).mp hTlog
    nlinarith
  refine ⟨hfinite, T + 1, ‖k‖ * M, by linarith, mul_nonneg (norm_nonneg _) hM, ?_⟩
  intro z hz
  have hzT : T < z.im := by linarith
  have hzmax : max 0 Y₀ < z.im := lt_of_le_of_lt (le_max_left _ _) hzT
  have hqnorm : ‖q z‖ = Real.exp (-2 * Real.pi * z.im) := by
    simpa only [Function.Periodic.qParam, Complex.ofReal_one, div_one] using
      Function.Periodic.norm_qParam 1 z
  have hqr : ‖q z‖ < r := by
    rw [hqnorm]
    apply lt_of_lt_of_le _ hexp
    apply Real.exp_lt_exp.mpr
    exact mul_lt_mul_of_neg_left hzT (mul_neg_of_neg_of_pos (by norm_num) Real.pi_pos)
  obtain ⟨hAq, hestimate⟩ := hbound (q z) (Complex.exp_ne_zero _) hqr
  have heq : F =ᶠ[nhds z] fun w => A (q w) := by
    have hopen : IsOpen {w : ℂ | max 0 Y₀ < w.im} :=
      isOpen_lt continuous_const Complex.continuous_im
    filter_upwards [hopen.mem_nhds hzmax] with w hw
    exact hfactor w (lt_of_le_of_lt (le_max_left _ _) hw)
      (le_of_lt (lt_of_le_of_lt (le_max_right _ _) hw))
  have hFz : F z = A (q z) := heq.self_of_nhds
  have hqderiv : HasDerivAt q (q z * k) z := by
    convert! ((hasDerivAt_id z).const_mul k).cexp using 1
    simp [q]
  have hball : q z ∈ Metric.ball (0 : ℂ) r := by
    simpa only [Metric.mem_ball, dist_zero_right] using hqr
  have hderiv : deriv F z = deriv A (q z) * (q z * k) :=
    (((hAdiff.differentiableAt (Metric.isOpen_ball.mem_nhds hball)).hasDerivAt.comp z
      hqderiv).congr_of_eventuallyEq heq).deriv
  refine ⟨hFz ▸ hAq, ?_⟩
  change ‖deriv F z / F z - k * (analyticOrderNatAt A 0 : ℂ)‖ ≤
    (‖k‖ * M) * Real.exp (-2 * Real.pi * z.im)
  rw [hderiv, hFz]
  have hid : deriv A (q z) * (q z * k) / A (q z) -
      k * (analyticOrderNatAt A 0 : ℂ) =
      k * (q z * deriv A (q z) / A (q z) - (analyticOrderNatAt A 0 : ℂ)) := by ring
  rw [hid, norm_mul, mul_assoc, ← hqnorm]
  exact mul_le_mul_of_nonneg_left hestimate (norm_nonneg k)
theorem Submission.p10_17ae7b7d_idx_crt_row_card :
    ∀ (N : ℕ) [NeZero N],
      let P : ℕ → Type := fun n => Quot
        (fun v w : {v : ZMod n × ZMod n // ∃ x y : ZMod n, x * v.1 + y * v.2 = 1} =>
          ∃ u : (ZMod n)ˣ, (u : ZMod n) * v.1.1 = w.1.1 ∧
            (u : ZMod n) * v.1.2 = w.1.2)
      Nat.card (P N) = N.primeFactors.prod (fun p => Nat.card (P (p ^ N.factorization p))) := by
  intro N _
  classical
  let P := fun (A : Type) [CommRing A] => Quot
    (fun v w : {v : A × A // ∃ x y : A, x * v.1 + y * v.2 = 1} =>
      ∃ u : Aˣ, (u : A) * v.1.1 = w.1.1 ∧ (u : A) * v.1.2 = w.1.2)
  change Nat.card (P (ZMod N)) =
    N.primeFactors.prod (fun p => Nat.card (P (ZMod (p ^ N.factorization p))))
  obtain ⟨eCRT⟩ := Submission.p10_17ae7b7d_crt_ring_equiv_rows
    (ZMod N) (∀ p : N.primeFactors, ZMod (p.1 ^ N.factorization p.1))
    (ZMod.equivPi N (NeZero.ne N))
  obtain ⟨ePi⟩ := Submission.p10_17ae7b7d_crt_pi_rows N.primeFactors
    (fun p => ZMod (p.1 ^ N.factorization p.1))
  calc
    Nat.card (P (ZMod N)) =
        Nat.card (∀ p : N.primeFactors, P (ZMod (p.1 ^ N.factorization p.1))) :=
      Nat.card_congr (eCRT.trans ePi)
    _ = ∏ p : N.primeFactors, Nat.card (P (ZMod (p.1 ^ N.factorization p.1))) :=
      Nat.card_pi
    _ = _ := Finset.prod_coe_sort N.primeFactors
      (fun p => Nat.card (P (ZMod (p ^ N.factorization p))))
