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
