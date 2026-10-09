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
theorem Submission.p10_17ae7b7d_phdisk_mobius_ratio_norm :
    ∀ (a b c d : ℝ) (z v : ℂ), a * d - b * c = 1 → 0 < z.im → 0 < v.im →
      let M : ℂ → ℂ := fun x =>
        ((a : ℂ) * x + (b : ℂ)) / ((c : ℂ) * x + (d : ℂ))
      ‖(M z - M v) / (M z - star (M v))‖ = ‖(z - v) / (z - star v)‖ := by
  intro a b c d z v hdet hz hv
  let Q : ℂ → ℂ := fun x => (c : ℂ) * x + (d : ℂ)
  let M : ℂ → ℂ := fun x => ((a : ℂ) * x + (b : ℂ)) / Q x
  change ‖(M z - M v) / (M z - star (M v))‖ = ‖(z - v) / (z - star v)‖
  have hQ (x : ℂ) (hx : 0 < x.im) : Q x ≠ 0 := by
    intro hzero
    have him : c * x.im = 0 := by
      simpa only [Q, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, add_zero, Complex.zero_im] using
        congrArg Complex.im hzero
    have hc : c = 0 := (mul_eq_zero.mp him).resolve_right (ne_of_gt hx)
    have hd : d = 0 := by
      simpa only [Q, hc, Complex.ofReal_zero, zero_mul, zero_add,
        Complex.ofReal_eq_zero] using hzero
    norm_num [hc, hd] at hdet
  have hQz : Q z ≠ 0 := hQ z hz
  have hQv : Q v ≠ 0 := hQ v hv
  have hQconj : Q (star v) = star (Q v) := by
    simp [Q]
  have hMconj : M (star v) = star (M v) := by
    simp [M, Q]
  have hQstar : star (Q v) ≠ 0 := star_ne_zero.mpr hQv
  have hQsv : Q (star v) ≠ 0 := by
    rw [hQconj]
    exact hQstar
  have hdetC : (a : ℂ) * (d : ℂ) - (b : ℂ) * (c : ℂ) = 1 := by
    exact_mod_cast hdet
  have hdiff (x y : ℂ) (hx : Q x ≠ 0) (hy : Q y ≠ 0) :
      M x - M y = (x - y) / (Q x * Q y) := by
    dsimp only [M]
    rw [div_sub_div _ _ hx hy]
    congr 1
    calc
      ((a : ℂ) * x + (b : ℂ)) * Q y -
          Q x * ((a : ℂ) * y + (b : ℂ)) =
          ((a : ℂ) * (d : ℂ) - (b : ℂ) * (c : ℂ)) * (x - y) := by
        dsimp only [Q]
        ring
      _ = x - y := by rw [hdetC, one_mul]
  have hzsv : z - star v ≠ 0 := by
    intro hzero
    have him := congrArg Complex.im hzero
    simp only [Complex.sub_im, Complex.star_def, Complex.conj_im,
      Complex.zero_im] at him
    linarith
  have hratio : (M z - M v) / (M z - star (M v)) =
      ((z - v) / (z - star v)) * (star (Q v) / Q v) := by
    rw [hdiff z v hQz hQv, ← hMconj, hdiff z (star v) hQz hQsv, hQconj]
    field_simp [hQz, hQv, hQstar, hzsv]
  have hunit : ‖star (Q v) / Q v‖ = 1 := by
    rw [norm_div, Complex.star_def, Complex.norm_conj,
      div_self (norm_ne_zero_iff.mpr hQv)]
  rw [hratio, norm_mul, hunit, mul_one]


theorem Submission.p10_17ae7b7d_phdisk_mobius_image :
    let D : ℂ → ℝ → Set ℂ := fun v ε =>
      {z : ℂ | 0 < z.im ∧ ‖(z - v) / (z - star v)‖ ≤ ε}
    ∀ (v : ℂ) (ε : ℝ), 0 < v.im → 0 < ε → ε < 1 →
      ∀ a b c d : ℝ, a * d - b * c = 1 →
        let M : ℂ → ℂ := fun z =>
          ((a : ℂ) * z + (b : ℂ)) / ((c : ℂ) * z + (d : ℂ))
        M '' (D v ε) = D (M v) ε := by
  dsimp only
  intro v ε hv _hεpos _hεlt a b c d hdet
  have hbij := Submission.p10_17ae7b7d_phdisk_mobius_bijon a b c d hdet
  apply Set.Subset.antisymm
  · rintro w ⟨z, ⟨hz, hbound⟩, rfl⟩
    refine ⟨hbij.mapsTo hz, ?_⟩
    rw [Submission.p10_17ae7b7d_phdisk_mobius_ratio_norm a b c d z v hdet hz hv]
    exact hbound
  · rintro w ⟨hw, hbound⟩
    obtain ⟨z, hz, rfl⟩ := hbij.surjOn hw
    refine ⟨z, ⟨hz, ?_⟩, rfl⟩
    rw [Submission.p10_17ae7b7d_phdisk_mobius_ratio_norm a b c d z v hdet hz hv]
      at hbound
    exact hbound


theorem Submission.p10_17ae7b7d_valence_pseudohyperbolic_disks :
    let D : ℂ → ℝ → Set ℂ :=
      fun v ε => {z : ℂ | 0 < z.im ∧ ‖(z - v) / (z - star v)‖ ≤ ε}
    ∀ (v : ℂ) (ε : ℝ), 0 < v.im → 0 < ε → ε < 1 →
      D v ε = Metric.closedBall
        ((v.re : ℂ) + ((v.im * (1 + ε ^ 2) / (1 - ε ^ 2) : ℝ) : ℂ) * Complex.I)
        (2 * v.im * ε / (1 - ε ^ 2)) ∧
      ∀ a b c d : ℝ, a * d - b * c = 1 →
        let M : ℂ → ℂ :=
          fun z => ((a : ℂ) * z + (b : ℂ)) / ((c : ℂ) * z + (d : ℂ))
        M '' (D v ε) = D (M v) ε := by
  dsimp only
  intro v ε hv hε hε_one
  exact ⟨Submission.p10_17ae7b7d_phdisk_euclidean v ε hv hε hε_one,
    Submission.p10_17ae7b7d_phdisk_mobius_image v ε hv hε hε_one⟩
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


namespace Submission

/-- The level-one valence inequality, with the orders at the two elliptic points
and the cusp. The contour computation follows the frozen parent-supplied proof. -/
theorem p10_17ae7b7d_level_one_valence_inequality :
    ∀ (k : ℕ) (F A : ℂ → ℂ), Even k →
      DifferentiableOn ℂ F {z : ℂ | 0 < z.im} →
      (∃ z : ℂ, 0 < z.im ∧ F z ≠ 0) →
      (∀ z : ℂ, 0 < z.im → F (z + 1) = F z) →
      (∀ z : ℂ, 0 < z.im → F (-1 / z) = z ^ k * F z) →
      AnalyticAt ℂ A 0 →
      (∃ Y : ℝ, ∀ z : ℂ, 0 < z.im → Y ≤ z.im →
        F z = A (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * z))) →
      (analyticOrderNatAt A 0 : ℝ) + (analyticOrderNatAt F Complex.I : ℝ) / 2 +
        (analyticOrderNatAt F ((-1 + (Real.sqrt 3 : ℂ) * Complex.I) / 2) : ℝ) / 3 ≤
          (k : ℝ) / 12 := by
  classical
  intro k F A hk hF hnonzero hT hS hA hq
  let H : Set ℂ := {z : ℂ | 0 < z.im}
  let ρ : ℂ := (-1 + (Real.sqrt 3 : ℂ) * Complex.I) / 2
  let L : ℂ → ℂ := fun z => deriv F z / F z
  have hH : IsOpen H := isOpen_lt continuous_const Complex.continuous_im
  have hHconn : IsPreconnected H := (convex_halfSpace_im_gt 0).isPreconnected
  have hFan : AnalyticOnNhd ℂ F H := hF.analyticOnNhd hH
  -- Steps 1–2: the identity principle makes every order in the half-plane finite.
  have hFfinite : ∀ z ∈ H, analyticOrderAt F z ≠ ⊤ := by
    obtain ⟨w, hw, hwF⟩ := hnonzero
    intro z hz
    apply hFan.analyticOrderAt_ne_top_of_isPreconnected hHconn hw hz
    rw [(hFan w hw).analyticOrderAt_eq_zero.mpr hwF]
    exact ENat.zero_ne_top
  have hfactor : ∀ z ∈ H, ∃ g : ℂ → ℂ,
      AnalyticAt ℂ g z ∧ g z ≠ 0 ∧
        ∀ᶠ w in nhds z, F w = (w - z) ^ analyticOrderNatAt F z * g w := by
    intro z hz
    simpa only [Filter.EventuallyEq, smul_eq_mul] using
      (hFan z hz).analyticOrderAt_ne_top.mp (hFfinite z hz)
  have hisolated : ∀ v ∈ H, ∃ r : ℝ, 0 < r ∧ Metric.ball v r ⊆ H ∧
      ∀ z ∈ Metric.ball v r, z ≠ v → F z ≠ 0 := by
    intro v hv
    have hp := (hFan v hv).eventually_eq_zero_or_eventually_ne_zero.resolve_left
      (fun hzero => hFfinite v hv (analyticOrderAt_eq_top.mpr hzero))
    have hn : ∀ᶠ z in nhds v, z ≠ v → F z ≠ 0 :=
      eventually_nhdsWithin_iff.mp hp
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem (hH.mem_nhds hv) hn)
    exact ⟨r, hr, fun z hz => (hball hz).1, fun z hz => (hball hz).2⟩
  have hzeros : ∀ᶠ z in Filter.codiscreteWithin H, F z ≠ 0 := by
    rcases hFan.eqOn_zero_or_eventually_ne_zero_of_preconnected hHconn with hzero | hzero
    · obtain ⟨w, hw, hwF⟩ := hnonzero
      exact False.elim (hwF (hzero hw))
    · exact hzero
  have hfiniteZeros : ∀ K : Set ℂ, IsCompact K → K ⊆ H →
      {z ∈ K | F z = 0}.Finite := by
    intro K hK hKH
    have hz := hK.finite_sdiff_of_mem_codiscreteWithin
      (Filter.codiscreteWithin_mono hKH hzeros)
    exact hz.subset (fun _ hz => ⟨hz.1, not_not.mpr hz.2⟩)
  obtain ⟨hAfin, Y₀, C, hY₀, hC, hcusp⟩ :=
    p10_17ae7b7d_valence_cusp_log_derivative F A hF hnonzero hA hq
  let Y : ℝ := max Y₀ 2
  have hYY₀ : Y₀ ≤ Y := le_max_left _ _
  have hY : 1 < Y := lt_of_lt_of_le (by norm_num) (le_max_right Y₀ 2)
  have hupper : ∀ z : ℂ, Y ≤ z.im → F z ≠ 0 :=
    fun z hz => (hcusp z (hYY₀.trans hz)).1
  -- Step 3: express the truncated region with a positive closed lower height bound.
  let K : Set ℂ := {z : ℂ |
    |z.re| ≤ 1 / 2 ∧ 1 ≤ ‖z‖ ∧ 0 < z.im ∧ z.im ≤ Y}
  have hKlower : ∀ z ∈ K, Real.sqrt 3 / 2 ≤ z.im := by
    intro z hz
    have hre := (abs_le.mp hz.1)
    have hre2 : z.re ^ 2 ≤ 1 / 4 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hre.2) (sub_nonneg.mpr hre.1)]
    have hnorm2 : 1 ≤ ‖z‖ ^ 2 := by
      nlinarith [sq_nonneg (‖z‖ - 1), hz.2.1]
    have him2 : 3 / 4 ≤ z.im ^ 2 := by
      nlinarith [Complex.sq_norm_sub_sq_re z]
    have hsqrt : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have hpos := hz.2.2.1
    nlinarith [Real.sqrt_nonneg 3]
  have hKclosed : IsClosed K := by
    have heq : K = {z : ℂ | |z.re| ≤ 1 / 2 ∧ 1 ≤ ‖z‖ ∧
        Real.sqrt 3 / 2 ≤ z.im ∧ z.im ≤ Y} := by
      ext z
      constructor
      · intro hz
        exact ⟨hz.1, hz.2.1, hKlower z hz, hz.2.2.2⟩
      · intro hz
        exact ⟨hz.1, hz.2.1, lt_of_lt_of_le (by positivity) hz.2.2.1, hz.2.2.2⟩
    rw [heq]
    exact (isClosed_le Complex.continuous_re.abs continuous_const).inter
      ((isClosed_le continuous_const continuous_norm).inter
        ((isClosed_le continuous_const Complex.continuous_im).inter
          (isClosed_le Complex.continuous_im continuous_const)))
  have hKbounded : Bornology.IsBounded K := by
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨1 / 2 + Y, ?_⟩
    intro z hz
    calc
      ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
      _ ≤ 1 / 2 + Y := by
        rw [abs_of_pos hz.2.2.1]
        exact add_le_add hz.1 hz.2.2.2
  have hKcompact : IsCompact K := Metric.isCompact_iff_isClosed_bounded.mpr ⟨hKclosed, hKbounded⟩
  have hKH : K ⊆ H := fun _ hz => hz.2.2.1
  have hKzeros : {z ∈ K | F z = 0}.Finite := hfiniteZeros K hKcompact hKH
  have hKtop : ∀ z ∈ K, z.im = Y → F z ≠ 0 := by
    intro z _ hz
    exact hupper z (le_of_eq hz.symm)
  have hLan : ∀ z ∈ H, F z ≠ 0 → AnalyticAt ℂ L z := by
    intro z hz hne
    exact (hFan z hz).deriv.div (hFan z hz) hne
  have hlocalPrimitive : ∀ z ∈ H, F z ≠ 0 →
      ∃ r : ℝ, 0 < r ∧ Complex.IsExactOn L (Metric.ball z r) := by
    intro z hz hne
    obtain ⟨r, hr, han⟩ := (hLan z hz hne).exists_ball_analyticOnNhd
    exact ⟨r, hr, han.differentiableOn.isExactOn_ball⟩
  -- Step 7: the exact counterclockwise contribution of a small circle about a zero.
  have hlocalResidue : ∀ v ∈ H, ∃ r : ℝ, 0 < r ∧ Metric.closedBall v r ⊆ H ∧
      ∀ s : ℝ, 0 < s → s ≤ r →
        (∀ z ∈ Metric.sphere v s, F z ≠ 0) ∧ CircleIntegrable L v s ∧
          circleIntegral L v s =
            2 * (Real.pi : ℂ) * Complex.I * (analyticOrderNatAt F v : ℂ) := by
    intro v hv
    obtain ⟨b, hb, hbv, hFb⟩ := hfactor v hv
    have hnear : ∀ᶠ z in nhds v, z ∈ H ∧ AnalyticAt ℂ b z ∧ b z ≠ 0 ∧
        F z = (z - v) ^ analyticOrderNatAt F v * b z := by
      filter_upwards [hH.mem_nhds hv, hb.eventually_analyticAt,
        hb.continuousAt.eventually_ne hbv, hFb] with z hz hbz hbnz hFbz
      exact ⟨hz, hbz, hbnz, hFbz⟩
    obtain ⟨r, hr, hrprop⟩ := Metric.eventually_nhds_iff_ball.mp hnear
    let G : ℂ → ℂ := fun z => deriv b z / b z
    have hG : AnalyticOnNhd ℂ G (Metric.ball v r) := by
      intro z hz
      obtain ⟨_, hbz, hbnz, _⟩ := hrprop z hz
      exact hbz.deriv.div hbz hbnz
    have hlocal : ∀ z ∈ Metric.ball v r, z ≠ v →
        F z ≠ 0 ∧ L z = (analyticOrderNatAt F v : ℂ) / (z - v) + G z := by
      intro z hz hne
      obtain ⟨_, hbz, hbnz, hFbz⟩ := hrprop z hz
      have hp : (z - v) ^ analyticOrderNatAt F v ≠ 0 :=
        pow_ne_zero _ (sub_ne_zero.mpr hne)
      refine ⟨by rw [hFbz]; exact mul_ne_zero hp hbnz, ?_⟩
      have heq : F =ᶠ[nhds z] fun w => (w - v) ^ analyticOrderNatAt F v * b w := by
        filter_upwards [Metric.isOpen_ball.mem_nhds hz] with w hw
        exact (hrprop w hw).2.2.2
      change logDeriv F z = (analyticOrderNatAt F v : ℂ) / (z - v) + logDeriv b z
      have hd : DifferentiableAt ℂ (fun w : ℂ => w - v) z :=
        differentiableAt_id.sub_const v
      have hdp : DifferentiableAt ℂ
          (fun w : ℂ => (w - v) ^ analyticOrderNatAt F v) z := hd.pow _
      rw [(logDeriv_congr_nhds heq).self_of_nhds,
        logDeriv_mul z hp hbnz hdp hbz.differentiableAt,
        logDeriv_fun_pow hd]
      simp only [logDeriv_apply, deriv_sub_const, deriv_id'', mul_one_div]
    have hhalf : Metric.closedBall v (r / 2) ⊆ Metric.ball v r :=
      Metric.closedBall_subset_ball (by linarith)
    refine ⟨r / 2, half_pos hr, fun z hz => (hrprop z (hhalf hz)).1, ?_⟩
    intro s hs hsr
    have hsub : Metric.closedBall v s ⊆ Metric.ball v r :=
      (Metric.closedBall_subset_closedBall hsr).trans hhalf
    have hsphere : ∀ z ∈ Metric.sphere v s, z ∈ Metric.ball v r ∧ z ≠ v := by
      intro z hz
      exact ⟨hsub (Metric.sphere_subset_closedBall hz), Metric.ne_of_mem_sphere hz hs.ne'⟩
    have hLcont : ContinuousOn L (Metric.sphere v s) := by
      intro z hz
      obtain ⟨hzr, hne⟩ := hsphere z hz
      exact (hLan z (hrprop z hzr).1 (hlocal z hzr hne).1).continuousAt.continuousWithinAt
    have hsing : CircleIntegrable
        (fun z : ℂ => (analyticOrderNatAt F v : ℂ) / (z - v)) v s := by
      apply ContinuousOn.circleIntegrable hs.le
      exact continuousOn_const.div (continuousOn_id.sub continuousOn_const)
        (fun z hz => sub_ne_zero.mpr (hsphere z hz).2)
    have hGcont := (hG.mono hsub).continuousOn
    have hGzero : circleIntegral G v s = 0 := by
      apply Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hs.le
        Set.countable_empty hGcont
      intro z hz
      exact (hG z (hsub (Metric.ball_subset_closedBall hz.1))).differentiableAt
    refine ⟨fun z hz => (hlocal z (hsphere z hz).1 (hsphere z hz).2).1,
      hLcont.circleIntegrable hs.le, ?_⟩
    calc
      circleIntegral L v s = circleIntegral
          (fun z => (analyticOrderNatAt F v : ℂ) / (z - v) + G z) v s :=
        circleIntegral.integral_congr hs.le
          (fun z hz => (hlocal z (hsphere z hz).1 (hsphere z hz).2).2)
      _ = circleIntegral (fun z => (analyticOrderNatAt F v : ℂ) / (z - v)) v s := by
        rw [circleIntegral.integral_add hsing
          ((hGcont.mono Metric.sphere_subset_closedBall).circleIntegrable hs.le), hGzero, add_zero]
      _ = (analyticOrderNatAt F v : ℂ) * circleIntegral (fun z => (z - v)⁻¹) v s := by
        simpa only [div_eq_mul_inv, smul_eq_mul] using
          circleIntegral.integral_smul (analyticOrderNatAt F v : ℂ)
            (fun z : ℂ => (z - v)⁻¹) v s
      _ = 2 * (Real.pi : ℂ) * Complex.I * (analyticOrderNatAt F v : ℂ) := by
        rw [circleIntegral.integral_sub_inv_of_mem_ball (Metric.mem_ball_self hs)]
        ring
  -- Steps 5–6: compactness gives a common size for primitive neighborhoods.
  have hprimitiveMesh : ∀ Q : Set ℂ, IsCompact Q → Q ⊆ H →
      (∀ z ∈ Q, F z ≠ 0) → ∃ δ : ℝ, 0 < δ ∧
        ∀ z ∈ Q, Complex.IsExactOn L (Metric.ball z δ) := by
    intro Q hQ hQH hQF
    let cover : Set (Set ℂ) := {U | IsOpen U ∧ Complex.IsExactOn L U}
    have hcover : Q ⊆ ⋃₀ cover := by
      intro z hz
      obtain ⟨r, hr, hprimitive⟩ := hlocalPrimitive z (hQH hz) (hQF z hz)
      exact Set.mem_sUnion.mpr
        ⟨Metric.ball z r, ⟨Metric.isOpen_ball, hprimitive⟩, Metric.mem_ball_self hr⟩
    obtain ⟨δ, hδ, hsub⟩ := lebesgue_number_lemma_of_metric_sUnion hQ
      (fun U hU => hU.1) hcover
    refine ⟨δ, hδ, ?_⟩
    intro z hz
    obtain ⟨U, hU, hzU⟩ := hsub z hz
    obtain ⟨g, hg⟩ := hU.2
    exact ⟨g, fun w hw => hg w (hzU hw)⟩
  -- Step 6: each regular piece in a primitive domain contributes its endpoint difference.
  have hprimitiveIntegral : ∀ (U : Set ℂ) (g : ℂ → ℂ),
      (∀ z ∈ U, HasDerivAt g (L z) z) →
      ∀ (η η' : ℝ → ℂ) (a b : ℝ),
        (∀ t ∈ Set.uIcc a b, η t ∈ U) →
        (∀ t ∈ Set.uIcc a b, HasDerivAt η (η' t) t) →
        IntervalIntegrable (fun t => L (η t) * η' t) MeasureTheory.volume a b →
        intervalIntegral (fun t => L (η t) * η' t) a b MeasureTheory.volume =
          g (η b) - g (η a) := by
    intro U g hg η η' a b hηU hη hηint
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ hηint
    intro t ht
    simpa only [Function.comp_def, smul_eq_mul, mul_comm] using
      (hg (η t) (hηU t ht)).scomp t (hη t ht)
  have hprimitiveCycles : ∀ (U : Set ℂ) (g : ℂ → ℂ),
      (∀ z ∈ U, HasDerivAt g (L z) z) →
      ∀ (n : ℕ) (next : Equiv.Perm (Fin n))
        (η η' : Fin n → ℝ → ℂ) (a b : Fin n → ℝ),
        (∀ i t, t ∈ Set.uIcc (a i) (b i) → η i t ∈ U) →
        (∀ i t, t ∈ Set.uIcc (a i) (b i) → HasDerivAt (η i) (η' i t) t) →
        (∀ i, IntervalIntegrable (fun t => L (η i t) * η' i t)
          MeasureTheory.volume (a i) (b i)) →
        (∀ i, η i (b i) = η (next i) (a (next i))) →
        ∑ i, intervalIntegral (fun t => L (η i t) * η' i t)
          (a i) (b i) MeasureTheory.volume = 0 := by
    intro U g hg n next η η' a b hηU hη hηint hnext
    calc
      _ = ∑ i : Fin n, (g (η i (b i)) - g (η i (a i))) := by
        apply Finset.sum_congr rfl
        intro i _
        exact hprimitiveIntegral U g hg (η i) (η' i) (a i) (b i)
          (hηU i) (hη i) (hηint i)
      _ = (∑ i : Fin n, g (η i (b i))) - ∑ i : Fin n, g (η i (a i)) :=
        Finset.sum_sub_distrib _ _
      _ = 0 := by
        simp_rw [hnext]
        rw [Equiv.sum_comp next (fun i => g (η i (a i))), sub_self]
  -- Steps 5–7: simultaneously excise the interior zeros and retain a primitive mesh.
  have hinteriorExcision : ∀ U : Set ℂ, IsOpen U → U.Nonempty →
      IsCompact (closure U) → closure U ⊆ H → (∀ z ∈ frontier U, F z ≠ 0) →
      let S : Set ℂ := {z ∈ U | F z = 0}
      ∃ (r : ℝ) (p : ℂ), 0 < r ∧ p ∈ U ∧ F p ≠ 0 ∧
        S.Pairwise (fun v w => Disjoint (Metric.closedBall v r) (Metric.closedBall w r)) ∧
        (∀ v ∈ S, Metric.closedBall v r ⊆ U ∧ CircleIntegrable L v r ∧
          circleIntegral L v r =
            2 * (Real.pi : ℂ) * Complex.I * (analyticOrderNatAt F v : ℂ)) ∧
        let V := U \ ⋃ v ∈ S, Metric.closedBall v r
        p ∈ V ∧ IsOpen V ∧ IsCompact (closure V) ∧
          (∀ z ∈ closure V, F z ≠ 0) ∧
          ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ closure V, Complex.IsExactOn L (Metric.ball z δ) := by
    intro U hU hUne hUc hUH hUF
    let S : Set ℂ := {z ∈ U | F z = 0}
    have hS : S.Finite := (hfiniteZeros (closure U) hUc hUH).subset
      (fun z hz => ⟨subset_closure hz.1, hz.2⟩)
    obtain ⟨p, hpU, hpF⟩ : ∃ p ∈ U, F p ≠ 0 := by
      by_contra! hzero
      obtain ⟨p, hp⟩ := hUne
      apply hFfinite p (hUH (subset_closure hp))
      apply analyticOrderAt_eq_top.mpr
      filter_upwards [hU.mem_nhds hp] with z hz
      exact hzero z hz
    have hsmall : ∀ v ∈ S, ∀ᶠ r in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        Metric.closedBall v r ⊆ U ∧ p ∉ Metric.closedBall v r ∧ CircleIntegrable L v r ∧
          circleIntegral L v r =
            2 * (Real.pi : ℂ) * Complex.I * (analyticOrderNatAt F v : ℂ) := by
      intro v hv
      obtain ⟨a, ha, haU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hv.1)
      obtain ⟨b, hb, _, hbint⟩ := hlocalResidue v (hUH (subset_closure hv.1))
      have hpv : p ≠ v := by rintro rfl; exact hpF hv.2
      have hlt (c : ℝ) (hc : 0 < c) :
          ∀ᶠ r in nhdsWithin (0 : ℝ) (Set.Ioi 0), r < c :=
        (eventually_lt_nhds hc).filter_mono nhdsWithin_le_nhds
      filter_upwards [self_mem_nhdsWithin, hlt a ha, hlt b hb,
        hlt (dist p v) (dist_pos.mpr hpv)] with r hr hra hrb hrpv
      refine ⟨(Metric.closedBall_subset_ball hra).trans haU, ?_, (hbint r hr hrb.le).2⟩
      intro hp
      exact (not_le_of_gt hrpv) (Metric.mem_closedBall.mp hp)
    have hpairs : ∀ v ∈ S, ∀ w ∈ S,
        ∀ᶠ r in nhdsWithin (0 : ℝ) (Set.Ioi 0),
          v ≠ w → Disjoint (Metric.closedBall v r) (Metric.closedBall w r) := by
      intro v _ w _
      by_cases hvw : v = w
      · exact Filter.Eventually.of_forall (fun _ hne => (hne hvw).elim)
      have hlt : ∀ᶠ r in nhdsWithin (0 : ℝ) (Set.Ioi 0), r < dist v w / 2 :=
        (eventually_lt_nhds (half_pos (dist_pos.mpr hvw))).filter_mono nhdsWithin_le_nhds
      filter_upwards [hlt] with r hr
      intro _
      exact Metric.closedBall_disjoint_closedBall (by linarith)
    have hall := (Filter.eventually_all_finite hS).mpr hsmall
    have hallpairs := (Filter.eventually_all_finite hS).mpr
      (fun v hv => (Filter.eventually_all_finite hS).mpr (hpairs v hv))
    have hpos : ∀ᶠ r in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < r := self_mem_nhdsWithin
    obtain ⟨r, hr, hrsmall, hrpairs⟩ :=
      (hpos.and (hall.and hallpairs)).exists
    let V : Set ℂ := U \ ⋃ v ∈ S, Metric.closedBall v r
    have hVopen : IsOpen V := hU.sdiff
      (hS.isClosed_biUnion (fun _ _ => Metric.isClosed_closedBall))
    have hVU : closure V ⊆ closure U := closure_mono (fun _ hz => hz.1)
    have hVc : IsCompact (closure V) := hUc.of_isClosed_subset isClosed_closure hVU
    have hVF : ∀ z ∈ closure V, F z ≠ 0 := by
      intro z hz hzero
      have hzU : z ∈ U := by
        by_contra hznot
        exact hUF z (by rw [hU.frontier_eq]; exact ⟨hVU hz, hznot⟩) hzero
      have hsub : V ⊆ (Metric.ball z r)ᶜ := by
        intro w hw hwz
        exact hw.2 (Set.mem_iUnion₂.mpr
          ⟨z, ⟨hzU, hzero⟩, Metric.ball_subset_closedBall hwz⟩)
      exact (closure_minimal hsub Metric.isOpen_ball.isClosed_compl) hz
        (Metric.mem_ball_self hr)
    refine ⟨r, p, hr, hpU, hpF, fun v hv w hw hne => hrpairs v hv w hw hne,
      fun v hv => ⟨(hrsmall v hv).1, (hrsmall v hv).2.2⟩, ?_⟩
    refine ⟨⟨hpU, ?_⟩, hVopen, hVc, hVF,
      hprimitiveMesh (closure V) hVc (hVU.trans hUH) hVF⟩
    intro hp
    obtain ⟨v, hv, hpv⟩ := Set.mem_iUnion₂.mp hp
    exact (hrsmall v hv).2.1 hpv
  have htopBound : ∀ (y : ℝ), Y ≤ y → ∀ x : ℝ,
      ‖L ((x : ℂ) + (y : ℂ) * Complex.I) -
        2 * (Real.pi : ℂ) * Complex.I * (analyticOrderNatAt A 0 : ℂ)‖ ≤
          C * Real.exp (-2 * Real.pi * y) := by
    intro y hy x
    simpa only [L, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero,
      zero_add] using
      (hcusp ((x : ℂ) + (y : ℂ) * Complex.I) (by simpa using hYY₀.trans hy)).2
  -- Step 13: the top is oriented from right to left and has displacement -1.
  let cInf : ℂ := 2 * (Real.pi : ℂ) * Complex.I * (analyticOrderNatAt A 0 : ℂ)
  let top : ℝ → ℂ := fun y => intervalIntegral
    (fun x : ℝ => L ((x : ℂ) + (y : ℂ) * Complex.I))
    (1 / 2 : ℝ) (-1 / 2 : ℝ) MeasureTheory.volume
  have htopContinuous : ∀ y : ℝ, Y ≤ y →
      Continuous (fun x : ℝ => L ((x : ℂ) + (y : ℂ) * Complex.I)) := by
    intro y hy
    apply continuous_iff_continuousAt.mpr
    intro x
    have hz : (x : ℂ) + (y : ℂ) * Complex.I ∈ H := by
      change 0 < ((x : ℂ) + (y : ℂ) * Complex.I).im
      simpa using (lt_of_lt_of_le (lt_trans zero_lt_one hY) hy)
    exact (hLan _ hz (hupper _ (by simpa using hy))).continuousAt.comp
      (f := fun x : ℝ => (x : ℂ) + (y : ℂ) * Complex.I)
      (show ContinuousAt (fun x : ℝ => (x : ℂ) + (y : ℂ) * Complex.I) x by fun_prop)
  have htopError : ∀ y : ℝ, Y ≤ y →
      ‖top y + cInf‖ ≤ C * Real.exp (-2 * Real.pi * y) := by
    intro y hy
    have hint := (htopContinuous y hy).intervalIntegrable
      (μ := MeasureTheory.volume) (1 / 2 : ℝ) (-1 / 2 : ℝ)
    have hid : (intervalIntegral (fun x : ℝ =>
        L ((x : ℂ) + (y : ℂ) * Complex.I) - cInf)
        (1 / 2 : ℝ) (-1 / 2 : ℝ) MeasureTheory.volume) = top y + cInf := by
      rw [intervalIntegral.integral_sub hint intervalIntegrable_const,
        intervalIntegral.integral_const]
      norm_num [top]
    rw [← hid]
    simpa only [cInf, show |(-1 / 2 : ℝ) - 1 / 2| = 1 by norm_num, mul_one] using
      intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (1 / 2 : ℝ)) (b := (-1 / 2 : ℝ)) (fun x _ => htopBound y hy x)
  have hdecay : Filter.Tendsto (fun y : ℝ => C * Real.exp (-2 * Real.pi * y))
      Filter.atTop (nhds 0) := by
    simpa only [mul_zero, Function.comp_apply, id_eq] using
      (Real.tendsto_exp_atBot.comp
        (Filter.tendsto_id.const_mul_atTop_of_neg
          (show -2 * Real.pi < 0 from
            mul_neg_of_neg_of_pos (by norm_num) Real.pi_pos))).const_mul C
  have htopLimit : Filter.Tendsto top Filter.atTop (nhds (-cInf)) := by
    have herr : Filter.Tendsto (fun y : ℝ => top y + cInf) Filter.atTop (nhds 0) :=
      squeeze_zero_norm' (Filter.eventually_atTop.mpr ⟨Y, htopError⟩) hdecay
    simpa only [add_sub_cancel_right, zero_sub] using herr.sub_const cInf
  -- Step 12: paired orders and logarithmic derivatives use the frozen child interface.
  have hmod := p10_17ae7b7d_valence_modular_log_derivative k F hF hT hS
  have hperiod : ∀ z ∈ H, F z ≠ 0 → L (z + 1) = L z := by
    intro z hz hne
    exact ((hmod z hz).2.2 hne).1
  have htopStable : ∀ y : ℝ, Y ≤ y → top y = top Y := by
    intro y hy
    have hdiff : DifferentiableOn ℂ L
        (Set.uIcc (-1 / 2 : ℝ) (1 / 2 : ℝ) ×ℂ Set.uIcc Y y) := by
      intro z hz
      have hzY : Y ≤ z.im := by
        have hm := (Complex.mem_reProdIm.mp hz).2
        rw [Set.uIcc_of_le hy] at hm
        exact hm.1
      exact (hLan z (lt_of_lt_of_le (by linarith [hY] : (0 : ℝ) < Y) hzY)
        (hupper z hzY)).differentiableAt.differentiableWithinAt
    have hrect := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
      L (⟨-1 / 2, Y⟩ : ℂ) (⟨1 / 2, y⟩ : ℂ) hdiff
    have hpair : intervalIntegral
        (fun t : ℝ => L ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)) Y y MeasureTheory.volume =
      intervalIntegral
        (fun t : ℝ => L ((-1 / 2 : ℂ) + (t : ℂ) * Complex.I)) Y y MeasureTheory.volume := by
      apply intervalIntegral.integral_congr
      intro t ht
      have htY : Y ≤ t := by
        rw [Set.uIcc_of_le hy] at ht
        exact ht.1
      have hpos : 0 < ((-1 / 2 : ℂ) + (t : ℂ) * Complex.I).im := by
        simp only [Complex.add_im, Complex.div_ofNat_im, Complex.neg_im,
          Complex.one_im, neg_zero, zero_div, Complex.mul_im, Complex.ofReal_re,
          Complex.I_im, Complex.ofReal_im, Complex.I_re, mul_one, mul_zero, add_zero,
          zero_add]
        linarith [hY]
      have heq := hperiod ((-1 / 2 : ℂ) + (t : ℂ) * Complex.I) hpos
        (hupper _ (by simpa using htY))
      convert heq using 2
      ring
    dsimp only at hrect
    push_cast at hrect
    rw [hpair, add_sub_cancel_right] at hrect
    have heq := sub_eq_zero.mp hrect
    dsimp only [top]
    simpa only [intervalIntegral.integral_symm (-1 / 2 : ℝ) (1 / 2 : ℝ)] using
      congrArg Neg.neg heq.symm
  have htopExact : top Y = -cInf := by
    have heventually : (fun _ : ℝ => top Y) =ᶠ[Filter.atTop] top :=
      Filter.eventually_atTop.mpr ⟨Y, fun y hy => (htopStable y hy).symm⟩
    exact tendsto_nhds_unique (tendsto_const_nhds.congr' heventually) htopLimit
  have hvertical : ∀ a b : ℝ,
      (∀ t ∈ Set.uIcc a b, 0 < t ∧ F ((-1 / 2 : ℂ) + (t : ℂ) * Complex.I) ≠ 0) →
      (intervalIntegral (fun t : ℝ => L ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) * Complex.I)
        a b MeasureTheory.volume) +
      (intervalIntegral (fun t : ℝ => L ((-1 / 2 : ℂ) + (t : ℂ) * Complex.I) * Complex.I)
        b a MeasureTheory.volume) = 0 := by
    intro a b hab
    have hp : (intervalIntegral
        (fun t : ℝ => L ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) * Complex.I)
        a b MeasureTheory.volume) =
        (intervalIntegral
          (fun t : ℝ => L ((-1 / 2 : ℂ) + (t : ℂ) * Complex.I) * Complex.I)
          a b MeasureTheory.volume) := by
      apply intervalIntegral.integral_congr
      intro t ht
      have h := hperiod ((-1 / 2 : ℂ) + (t : ℂ) * Complex.I)
        (by simpa [H] using (hab t ht).1) (hab t ht).2
      have heq : (-1 / 2 : ℂ) + (t : ℂ) * Complex.I + 1 =
          (1 / 2 : ℂ) + (t : ℂ) * Complex.I := by ring
      rw [heq] at h
      exact congrArg (fun w : ℂ => w * Complex.I) h
    rw [hp, intervalIntegral.integral_symm, neg_add_cancel]
  -- Step 14: pair first, so no separate singular arc integral is asserted.
  have harcPair : ∀ z ∈ H, F z ≠ 0 →
      (L z - L (-1 / z) / z ^ 2) * (Complex.I * z) = -(k : ℂ) * Complex.I := by
    intro z hz hne
    have hz0 : z ≠ 0 := by
      intro heq
      have hzpos : 0 < z.im := hz
      simp [heq] at hzpos
    change (L z - (deriv F (-1 / z) / F (-1 / z)) / z ^ 2) *
      (Complex.I * z) = -(k : ℂ) * Complex.I
    rw [((hmod z hz).2.2 hne).2]
    dsimp only [L]
    field_simp
    ring
  have hI : Complex.I ∈ H := by simp [H]
  have hρ : ρ ∈ H := by
    change 0 < ρ.im
    simp only [ρ, Complex.div_ofNat_im, Complex.add_im, Complex.neg_im,
      Complex.one_im, neg_zero, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.ofReal_im, Complex.I_re, mul_one, mul_zero, add_zero,
      zero_add]
    positivity
  have hρT : analyticOrderNatAt F (ρ + 1) = analyticOrderNatAt F ρ :=
    (hmod ρ hρ).1
  let D : ℂ → ℝ → Set ℂ :=
    fun v ε => {z : ℂ | 0 < z.im ∧ ‖(z - v) / (z - star v)‖ ≤ ε}
  have hdisks := p10_17ae7b7d_valence_pseudohyperbolic_disks
  -- Step 8: every prescribed neighborhood eventually contains the entire cut disk.
  have hdiskShrink : ∀ v ∈ H, ∀ r : ℝ, 0 < r →
      ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), D v ε ⊆ Metric.ball v r := by
    intro v hv r hr
    let center : ℝ → ℂ := fun ε => (v.re : ℂ) +
      ((v.im * (1 + ε ^ 2) / (1 - ε ^ 2) : ℝ) : ℂ) * Complex.I
    let radius : ℝ → ℝ := fun ε => 2 * v.im * ε / (1 - ε ^ 2)
    have hc : Filter.Tendsto center (nhds 0) (nhds v) := by
      have hcont : ContinuousAt center 0 := by
        dsimp [center]
        fun_prop (disch := norm_num)
      simpa [center, Complex.re_add_im] using hcont.tendsto
    have hradius : Filter.Tendsto radius (nhds 0) (nhds 0) := by
      have hcont : ContinuousAt radius 0 := by
        dsimp [radius]
        fun_prop (disch := norm_num)
      simpa [radius] using hcont.tendsto
    have hsize : Filter.Tendsto (fun ε => dist (center ε) v + radius ε)
        (nhds 0) (nhds 0) := by
      simpa only [dist_self, zero_add] using
        (hc.dist (tendsto_const_nhds :
          Filter.Tendsto (fun _ : ℝ => v) (nhds 0) (nhds v))).add hradius
    have hsmall : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        dist (center ε) v + radius ε < r :=
      ((tendsto_order.mp hsize).2 r hr).filter_mono nhdsWithin_le_nhds
    have hlessOne : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), ε < 1 :=
      (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, hlessOne, hsmall] with ε hε hε1 hsizeε
    intro z hz
    rw [show D v ε = _ from (hdisks v ε hv hε hε1).1] at hz
    change dist z (center ε) ≤ radius ε at hz
    change dist z v < r
    calc
      dist z v ≤ dist z (center ε) + dist (center ε) v := dist_triangle _ _ _
      _ ≤ radius ε + dist (center ε) v := add_le_add hz le_rfl
      _ < r := by linarith
  have hcutNoOtherZeros : ∀ v ∈ H,
      ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        ∀ z ∈ D v ε, z ≠ v → F z ≠ 0 := by
    intro v hv
    obtain ⟨r, hr, _, hzero⟩ := hisolated v hv
    filter_upwards [hdiskShrink v hv r hr] with ε hε
    exact fun z hz hne => hzero z (hε hz) hne
  have hcutsNoOtherZeros : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ∀ v ∈ {z ∈ K | F z = 0}, ∀ z ∈ D v ε, z ≠ v → F z ≠ 0 :=
    (Filter.eventually_all_finite hKzeros).mpr
      (fun v hv => hcutNoOtherZeros v (hKH hv.1))
  -- Steps 5 and 8: one sufficiently small parameter separates every pair of cuts.
  let Z : Set ℂ := {z ∈ K | F z = 0}
  have hcutsDisjoint : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      Z.Pairwise (fun v w => Disjoint (D v ε) (D w ε)) := by
    have hpair : ∀ v ∈ Z, ∀ w ∈ Z,
        ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
          v ≠ w → Disjoint (D v ε) (D w ε) := by
      intro v hv w hw
      by_cases hvw : v = w
      · exact Filter.Eventually.of_forall (fun _ hne => (hne hvw).elim)
      have hd : 0 < dist v w / 2 := half_pos (dist_pos.mpr hvw)
      filter_upwards [hdiskShrink v (hKH hv.1) _ hd,
        hdiskShrink w (hKH hw.1) _ hd] with ε hvε hwε
      intro _
      apply Set.disjoint_left.mpr
      intro z hzv hzw
      have hvz : dist v z < dist v w / 2 := by
        simpa only [Metric.mem_ball, dist_comm] using hvε hzv
      have hzw' : dist z w < dist v w / 2 := hwε hzw
      linarith [dist_triangle v z w]
    have hall := (Filter.eventually_all_finite hKzeros).mpr
      (fun v hv => (Filter.eventually_all_finite hKzeros).mpr (hpair v hv))
    filter_upwards [hall] with ε hε
    exact fun v hv w hw hne => hε v hv w hw hne
  have hcenterInterior : ∀ v ∈ H, ∀ ε : ℝ, 0 < ε → v ∈ interior (D v ε) := by
    intro v hv ε hε
    have hden : v - star v ≠ 0 := by
      intro heq
      have him := congrArg Complex.im heq
      have hvpos : 0 < v.im := hv
      simp only [Complex.sub_im, Complex.star_def, Complex.conj_im, Complex.zero_im] at him
      linarith
    have hc : ContinuousAt (fun z : ℂ => ‖(z - v) / (z - star v)‖) v :=
      ((continuousAt_id.sub continuousAt_const).div
        (continuousAt_id.sub continuousAt_const) hden).norm
    have hsmall : ∀ᶠ z in nhds v, ‖(z - v) / (z - star v)‖ < ε :=
      hc.tendsto.eventually (eventually_lt_nhds (by simpa using hε))
    apply mem_interior_iff_mem_nhds.mpr
    filter_upwards [hH.mem_nhds hv, hsmall] with z hz hnorm
    exact ⟨hz, hnorm.le⟩
  -- Removing the interiors of all zero disks leaves a compact, zero-free set.
  let Q : ℝ → Set ℂ := fun ε => K \ ⋃ v ∈ Z, interior (D v ε)
  have hQcompact : ∀ ε : ℝ, IsCompact (Q ε) :=
    fun ε => hKcompact.diff (isOpen_biUnion (fun _ _ => isOpen_interior))
  have hQzeroFree : ∀ ε : ℝ, 0 < ε → ∀ z ∈ Q ε, F z ≠ 0 := by
    intro ε hε z hz hzero
    exact hz.2 (Set.mem_iUnion₂.mpr
      ⟨z, ⟨hz.1, hzero⟩, hcenterInterior z (hKH hz.1) ε hε⟩)
  have hcutPrimitiveMesh : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ z ∈ Q ε, Complex.IsExactOn L (Metric.ball z δ) := by
    intro ε hε
    exact hprimitiveMesh (Q ε) (hQcompact ε) (fun _ hz => hKH hz.1)
      (hQzeroFree ε hε)
  -- Boundary cuts preserve every interior zero, which is needed for the count.
  let O : Set ℂ := {z : ℂ |
    |z.re| < 1 / 2 ∧ 1 < ‖z‖ ∧ 0 < z.im ∧ z.im < Y}
  let B : Set ℂ := Z \ O
  have hboundaryCutsPreserve : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ∀ z ∈ O, F z = 0 → z ∉ ⋃ v ∈ B, D v ε := by
    filter_upwards [hcutsNoOtherZeros] with ε hε
    intro z hz hzero hcut
    obtain ⟨v, hv, hzv⟩ := Set.mem_iUnion₂.mp hcut
    have hne : z ≠ v := by
      intro heq
      exact hv.2 (heq ▸ hz)
    exact hε v hv.1 z hzv hne hzero
  have hcutsBelowTop : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ∀ v ∈ Z, D v ε ⊆ {z : ℂ | z.im < Y} := by
    apply (Filter.eventually_all_finite hKzeros).mpr
    intro v hv
    have hvY : v.im < Y := lt_of_le_of_ne hv.1.2.2.2
      (fun heq => hKtop v hv.1 heq hv.2)
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
      ((isOpen_lt Complex.continuous_im continuous_const).mem_nhds hvY)
    filter_upwards [hdiskShrink v (hKH hv.1) r hr] with ε hε
    exact hε.trans hball
  -- Steps 10 and 17: construct the retained region and identify its zeros.
  have hOopen : IsOpen O :=
    (isOpen_lt Complex.continuous_re.abs continuous_const).inter
      ((isOpen_lt continuous_const continuous_norm).inter
        ((isOpen_lt continuous_const Complex.continuous_im).inter
          (isOpen_lt Complex.continuous_im continuous_const)))
  have hOK : O ⊆ K := fun _ hz => ⟨hz.1.le, hz.2.1.le, hz.2.2.1, hz.2.2.2.le⟩
  have hBfinite : B.Finite := hKzeros.subset (fun _ hz => hz.1)
  let Ω : ℝ → Set ℂ := fun ε => O \ ⋃ v ∈ B, D v ε
  have hcutOpen : ∀ ε : ℝ, 0 < ε → ε < 1 → IsOpen (Ω ε) := by
    intro ε hε hε1
    apply hOopen.sdiff
    apply hBfinite.isClosed_biUnion
    intro v hv
    rw [show D v ε = _ from (hdisks v ε (hKH hv.1.1) hε hε1).1]
    exact Metric.isClosed_closedBall
  have hcutClosureK : ∀ ε : ℝ, closure (Ω ε) ⊆ K :=
    fun ε => closure_minimal (fun _ hz => hOK hz.1) hKclosed
  have hcutCompact : ∀ ε : ℝ, IsCompact (closure (Ω ε)) :=
    fun ε => hKcompact.of_isClosed_subset isClosed_closure (hcutClosureK ε)
  have hcutClosureAvoidCenters : ∀ ε : ℝ, 0 < ε →
      ∀ v ∈ B, v ∉ closure (Ω ε) := by
    intro ε hε v hv hclosure
    have hsub : Ω ε ⊆ (interior (D v ε))ᶜ := by
      intro z hz hzv
      exact hz.2 (Set.mem_iUnion₂.mpr ⟨v, hv, interior_subset hzv⟩)
    exact (closure_minimal hsub isOpen_interior.isClosed_compl) hclosure
      (hcenterInterior v (hKH hv.1.1) ε hε)
  have hcutZeros : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      {z ∈ Ω ε | F z = 0} = {z ∈ O | F z = 0} := by
    filter_upwards [hboundaryCutsPreserve] with ε hε
    ext z
    exact ⟨fun hz => ⟨hz.1.1, hz.2⟩,
      fun hz => ⟨⟨hz.1, hε z hz.1 hz.2⟩, hz.2⟩⟩
  have hcutBoundaryZeroFree : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ∀ z ∈ frontier (Ω ε), F z ≠ 0 := by
    have hlessOne : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), ε < 1 :=
      (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, hlessOne, hboundaryCutsPreserve]
      with ε hε hε1 hkeep
    intro z hz hzero
    rw [(hcutOpen ε hε hε1).frontier_eq] at hz
    have hzO : z ∈ O := by
      by_contra hn
      exact hcutClosureAvoidCenters ε hε z ⟨⟨hcutClosureK ε hz.1, hzero⟩, hn⟩ hz.1
    exact hz.2 ⟨hzO, hkeep z hzO hzero⟩
  have hcutNonempty : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), (Ω ε).Nonempty := by
    let p : ℂ := (((Y + 1) / 2 : ℝ) : ℂ) * Complex.I
    have hypos : 0 < (Y + 1) / 2 := by linarith
    have hpim : p.im = (Y + 1) / 2 := by simp [p]
    have hpre : p.re = 0 := by simp [p]
    have hpnorm : ‖p‖ = (Y + 1) / 2 := by
      change ‖(((Y + 1) / 2 : ℝ) : ℂ) * Complex.I‖ = _
      rw [norm_mul, Complex.norm_of_nonneg hypos.le, Complex.norm_I, mul_one]
    have hpO : p ∈ O := by
      change |p.re| < 1 / 2 ∧ 1 < ‖p‖ ∧ 0 < p.im ∧ p.im < Y
      rw [hpre, hpnorm, hpim, abs_zero]
      exact ⟨by norm_num, by linarith, hypos, by linarith⟩
    have havoid : ∀ v ∈ B,
        ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), p ∉ D v ε := by
      intro v hv
      have hpv : p ≠ v := fun heq => hv.2 (heq ▸ hpO)
      filter_upwards [hdiskShrink v (hKH hv.1.1) _ (dist_pos.mpr hpv)] with ε hε
      intro hp
      exact (lt_irrefl (dist p v)) (hε hp)
    filter_upwards [(Filter.eventually_all_finite hBfinite).mpr havoid] with ε hε
    refine ⟨p, hpO, ?_⟩
    intro hp
    obtain ⟨v, hv, hpv⟩ := Set.mem_iUnion₂.mp hp
    exact hε v hv hpv
  have hsmallCuts : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < ε ∧ ε < 1 :=
    (show ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < ε from self_mem_nhdsWithin).and
      ((eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds)
  have hcutExcision :=
    (hsmallCuts.and (hcutNonempty.and hcutBoundaryZeroFree)).mono (fun ε hε =>
      hinteriorExcision (Ω ε) (hcutOpen ε hε.1.1 hε.1.2) hε.2.1
        (hcutCompact ε) ((hcutClosureK ε).trans hKH) hε.2.2)
  -- Step 10: identify the supports of the genuine retained boundary.
  -- Intersecting with the actual closure discards the removed portions of each support.
  let cutCenter : ℂ → ℝ → ℂ := fun v ε => (v.re : ℂ) +
    ((v.im * (1 + ε ^ 2) / (1 - ε ^ 2) : ℝ) : ℂ) * Complex.I
  let cutRadius : ℂ → ℝ → ℝ := fun v ε => 2 * v.im * ε / (1 - ε ^ 2)
  let outerSupport : Fin 4 → Set ℂ :=
    ![{z | ‖z‖ = 1}, {z | z.re = 1 / 2}, {z | z.im = Y}, {z | z.re = -1 / 2}]
  let boundarySupport : ℝ → Fin 4 ⊕ B → Set ℂ := fun ε =>
    Sum.elim outerSupport (fun v => Metric.sphere (cutCenter v ε) (cutRadius v ε))
  have hcutFrontier : ∀ ε : ℝ, 0 < ε → ε < 1 →
      frontier (Ω ε) = ⋃ i, closure (Ω ε) ∩ boundarySupport ε i := by
    intro ε hε hε1
    rw [(hcutOpen ε hε hε1).frontier_eq]
    ext z
    constructor
    · rintro ⟨hzcl, hznot⟩
      have hzK := hcutClosureK ε hzcl
      by_cases hzO : z ∈ O
      · have hzcut : z ∈ ⋃ v ∈ B, D v ε := by
          by_contra hn
          exact hznot ⟨hzO, hn⟩
        obtain ⟨v, hv, hzv⟩ := Set.mem_iUnion₂.mp hzcut
        have hball : D v ε = Metric.closedBall (cutCenter v ε) (cutRadius v ε) :=
          (hdisks v ε (hKH hv.1.1) hε hε1).1
        have hsub : Ω ε ⊆ (Metric.ball (cutCenter v ε) (cutRadius v ε))ᶜ := by
          intro w hw hwb
          apply hw.2
          exact Set.mem_iUnion₂.mpr ⟨v, hv, hball.symm ▸ Metric.ball_subset_closedBall hwb⟩
        have hnball := (closure_minimal hsub Metric.isOpen_ball.isClosed_compl) hzcl
        have hdist : dist z (cutCenter v ε) = cutRadius v ε := by
          apply le_antisymm
          · exact Metric.mem_closedBall.mp (hball ▸ hzv)
          · exact le_of_not_gt hnball
        exact Set.mem_iUnion.mpr ⟨Sum.inr ⟨v, hv⟩, hzcl, hdist⟩
      · have hcases : ‖z‖ = 1 ∨ z.re = 1 / 2 ∨ z.im = Y ∨ z.re = -1 / 2 := by
          by_contra! hn
          apply hzO
          refine ⟨?_, lt_of_le_of_ne hzK.2.1 (Ne.symm hn.1), hzK.2.2.1,
            lt_of_le_of_ne hzK.2.2.2 hn.2.2.1⟩
          apply abs_lt.mpr
          exact ⟨lt_of_le_of_ne (abs_le.mp hzK.1).1
              (by simpa only [neg_div] using Ne.symm hn.2.2.2),
            lt_of_le_of_ne (abs_le.mp hzK.1).2 hn.2.1⟩
        rcases hcases with hz | hz | hz | hz
        · exact Set.mem_iUnion.mpr ⟨Sum.inl 0, hzcl, hz⟩
        · exact Set.mem_iUnion.mpr ⟨Sum.inl 1, hzcl, hz⟩
        · exact Set.mem_iUnion.mpr ⟨Sum.inl 2, hzcl, hz⟩
        · exact Set.mem_iUnion.mpr ⟨Sum.inl 3, hzcl, hz⟩
    · intro hz
      obtain ⟨i, hzcl, hzi⟩ := Set.mem_iUnion.mp hz
      refine ⟨hzcl, ?_⟩
      intro hzΩ
      rcases i with i | v
      · fin_cases i
        · exact (ne_of_gt hzΩ.1.2.1) hzi
        · have heq : z.re = 1 / 2 := hzi
          exact (ne_of_lt (abs_lt.mp hzΩ.1.1).2) heq
        · exact (ne_of_lt hzΩ.1.2.2.2) hzi
        · have heq : z.re = -1 / 2 := hzi
          have hlt := (abs_lt.mp hzΩ.1.1).1
          linarith
      · apply hzΩ.2
        refine Set.mem_iUnion₂.mpr ⟨v, v.property, ?_⟩
        rw [show D v ε = _ from (hdisks v ε (hKH v.property.1.1) hε hε1).1]
        exact Metric.sphere_subset_closedBall hzi
  -- Steps 5–7 for this cut domain: the new boundary components are exactly the
  -- excision circles. Their clockwise parametrizations carry the negative residues.
  let square : ℝ → ℤ × ℤ → Set ℂ := fun d i => {z |
    (i.1 : ℝ) * d ≤ z.re ∧ z.re ≤ ((i.1 : ℝ) + 1) * d ∧
    (i.2 : ℝ) * d ≤ z.im ∧ z.im ≤ ((i.2 : ℝ) + 1) * d}
  have hfixedExcisionBoundary : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ∃ r δ : ℝ, 0 < r ∧ 0 < δ ∧
        let S : Set ℂ := {z ∈ Ω ε | F z = 0}
        let V := Ω ε \ ⋃ v ∈ S, Metric.closedBall v r
        IsOpen V ∧ IsCompact (closure V) ∧ (∀ z ∈ closure V, F z ≠ 0) ∧
          frontier V = (⋃ i, closure (Ω ε) ∩ boundarySupport ε i) ∪
            ⋃ v ∈ S, Metric.sphere v r ∧
          (∀ v ∈ S, Set.range (circleMap v r) ⊆ frontier V ∧
            IntervalIntegrable (fun t => L (circleMap v r t) * deriv (circleMap v r) t)
              MeasureTheory.volume (2 * Real.pi) 0 ∧
            intervalIntegral (fun t => L (circleMap v r t) * deriv (circleMap v r) t)
              (2 * Real.pi) 0 MeasureTheory.volume =
                -(2 * (Real.pi : ℂ) * Complex.I * (analyticOrderNatAt F v : ℂ))) ∧
          (∀ z ∈ closure V, Complex.IsExactOn L (Metric.ball z δ)) ∧
          ∃ d : ℝ, 0 < d ∧
            let cells : Set (ℤ × ℤ) := {i | (closure V ∩ square d i).Nonempty}
            cells.Finite ∧ closure V ⊆ ⋃ i ∈ cells, square d i ∧
              ∀ i ∈ cells, Complex.IsExactOn L (square d i) := by
    filter_upwards [hsmallCuts, hcutExcision] with ε hε hexc
    let S : Set ℂ := {z ∈ Ω ε | F z = 0}
    obtain ⟨r, p, hr, _, _, hpairs, hcircles, hpV, hVopen, hVc, hVF, δ, hδ, hmesh⟩ := hexc
    let V := Ω ε \ ⋃ v ∈ S, Metric.closedBall v r
    have hS : S.Finite := hKzeros.subset (fun z hz => ⟨hOK hz.1.1, hz.2⟩)
    have hballsClosed : IsClosed (⋃ v ∈ S, Metric.closedBall v r) :=
      hS.isClosed_biUnion (fun _ _ => Metric.isClosed_closedBall)
    have hfrontier : frontier V = frontier (Ω ε) ∪ ⋃ v ∈ S, Metric.sphere v r := by
      ext z
      rw [hVopen.frontier_eq, (hcutOpen ε hε.1 hε.2).frontier_eq]
      constructor
      · rintro ⟨hzcl, hznot⟩
        have hzΩcl : z ∈ closure (Ω ε) :=
          (closure_mono (show V ⊆ Ω ε from fun _ hw => hw.1)) hzcl
        by_cases hzΩ : z ∈ Ω ε
        · right
          have hzball : z ∈ ⋃ v ∈ S, Metric.closedBall v r := by
            by_contra hn
            exact hznot ⟨hzΩ, hn⟩
          obtain ⟨v, hv, hzv⟩ := Set.mem_iUnion₂.mp hzball
          have hsub : V ⊆ (Metric.ball v r)ᶜ := by
            intro w hw hwb
            exact hw.2 (Set.mem_iUnion₂.mpr ⟨v, hv, Metric.ball_subset_closedBall hwb⟩)
          have hnball := (closure_minimal hsub Metric.isOpen_ball.isClosed_compl) hzcl
          exact Set.mem_iUnion₂.mpr ⟨v, hv,
            le_antisymm (Metric.mem_closedBall.mp hzv) (le_of_not_gt hnball)⟩
        · exact Or.inl ⟨hzΩcl, hzΩ⟩
      · intro hz
        rcases hz with ⟨hzcl, hznot⟩ | hz
        · have hzout : z ∉ ⋃ v ∈ S, Metric.closedBall v r := by
            intro hzball
            obtain ⟨v, hv, hzv⟩ := Set.mem_iUnion₂.mp hzball
            exact hznot ((hcircles v hv).1 hzv)
          refine ⟨?_, fun hzV => hznot hzV.1⟩
          apply mem_closure_iff.mpr
          intro U hU hzU
          obtain ⟨w, ⟨hwU, hwout⟩, hwΩ⟩ := mem_closure_iff.mp hzcl
            (U ∩ (⋃ v ∈ S, Metric.closedBall v r)ᶜ)
            (hU.inter hballsClosed.isOpen_compl) ⟨hzU, hzout⟩
          exact ⟨w, hwU, hwΩ, hwout⟩
        · obtain ⟨v, hv, hzv⟩ := Set.mem_iUnion₂.mp hz
          have hzball := Metric.sphere_subset_closedBall hzv
          have hzΩ := (hcircles v hv).1 hzball
          let W := Ω ε \ ⋃ w ∈ S \ {v}, Metric.closedBall w r
          have hWopen : IsOpen W := (hcutOpen ε hε.1 hε.2).sdiff
            ((hS.sdiff : (S \ {v}).Finite).isClosed_biUnion
              (fun _ _ => Metric.isClosed_closedBall))
          have hzW : z ∈ W := by
            refine ⟨hzΩ, ?_⟩
            intro hzother
            obtain ⟨w, hw, hzw⟩ := Set.mem_iUnion₂.mp hzother
            exact Set.disjoint_left.mp (hpairs hv hw.1 (Ne.symm hw.2)) hzball hzw
          have hzoutcl : z ∈ closure (Metric.closedBall v r)ᶜ := by
            have hzf : z ∈ frontier (Metric.closedBall v r) := by
              rwa [frontier_closedBall v hr.ne']
            rw [frontier_eq_closure_inter_closure] at hzf
            exact hzf.2
          refine ⟨?_, fun hzV => hzV.2 (Set.mem_iUnion₂.mpr ⟨v, hv, hzball⟩)⟩
          apply mem_closure_iff.mpr
          intro U hU hzU
          obtain ⟨w, ⟨hwU, hwW⟩, hwout⟩ := mem_closure_iff.mp hzoutcl
            (U ∩ W) (hU.inter hWopen) ⟨hzU, hzW⟩
          refine ⟨w, hwU, hwW.1, ?_⟩
          intro hwball
          obtain ⟨a, ha, hwa⟩ := Set.mem_iUnion₂.mp hwball
          by_cases hav : a = v
          · exact hwout (hav ▸ hwa)
          · exact hwW.2 (Set.mem_iUnion₂.mpr ⟨a, ⟨ha, hav⟩, hwa⟩)
    refine ⟨r, δ, hr, hδ, hVopen, hVc, hVF, ?_, ?_, hmesh, ?_⟩
    · rw [hfrontier, hcutFrontier ε hε.1 hε.2]
    · intro v hv
      refine ⟨?_, ?_, ?_⟩
      · rw [range_circleMap, abs_of_pos hr, hfrontier]
        exact fun z hz => Or.inr (Set.mem_iUnion₂.mpr ⟨v, hv, hz⟩)
      · simpa only [smul_eq_mul, mul_comm] using (hcircles v hv).2.1.out.symm
      · rw [intervalIntegral.integral_symm]
        have hcw : intervalIntegral
            (fun t => L (circleMap v r t) * deriv (circleMap v r) t)
            0 (2 * Real.pi) MeasureTheory.volume = circleIntegral L v r := by
          simp only [circleIntegral, smul_eq_mul, mul_comm]
        rw [hcw, (hcircles v hv).2.2]
    · let d : ℝ := δ / 4
      have hd : 0 < d := by dsimp [d]; positivity
      let cells : Set (ℤ × ℤ) := {i | (closure V ∩ square d i).Nonempty}
      have hVK : closure V ⊆ K :=
        (closure_mono (show V ⊆ Ω ε from fun _ hz => hz.1)).trans (hcutClosureK ε)
      have hcover : ∀ z : ℂ, ∃ i : ℤ × ℤ, z ∈ square d i := by
        intro z
        refine ⟨(⌊z.re / d⌋, ⌊z.im / d⌋), ?_⟩
        have hlo (x : ℝ) : (⌊x / d⌋ : ℝ) * d ≤ x := by
          simpa only [div_mul_cancel₀ _ hd.ne'] using
            mul_le_mul_of_nonneg_right (Int.floor_le (x / d)) hd.le
        have hhi (x : ℝ) : x ≤ ((⌊x / d⌋ : ℝ) + 1) * d := by
          simpa only [div_mul_cancel₀ _ hd.ne'] using
            mul_le_mul_of_nonneg_right (Int.lt_floor_add_one (x / d)).le hd.le
        exact ⟨hlo _, hhi _, hlo _, hhi _⟩
      have hfiniteCells : cells.Finite := by
        obtain ⟨N, hN⟩ := exists_nat_gt ((Y + 1) / d + 1)
        have hNd : Y + 1 + d < (N : ℝ) * d := by
          have hm := mul_lt_mul_of_pos_right hN hd
          rw [add_mul, div_mul_cancel₀ _ hd.ne', one_mul] at hm
          exact hm
        apply (Set.finite_Icc ((-(N : ℤ), -(N : ℤ))) ((N : ℤ), (N : ℤ))).subset
        intro i hi
        obtain ⟨z, hzV, hzi⟩ := hi
        have hzK := hVK hzV
        have hzre := abs_le.mp hzK.1
        have him := hzK.2.2
        have hi1lo : -(N : ℝ) ≤ (i.1 : ℝ) := by
          nlinarith [hzi.2.1]
        have hi1hi : (i.1 : ℝ) ≤ (N : ℝ) := by
          nlinarith [hzi.1]
        have hi2lo : -(N : ℝ) ≤ (i.2 : ℝ) := by
          nlinarith [hzi.2.2.2]
        have hi2hi : (i.2 : ℝ) ≤ (N : ℝ) := by
          nlinarith [hzi.2.2.1]
        exact ⟨⟨by exact_mod_cast hi1lo, by exact_mod_cast hi2lo⟩,
          ⟨by exact_mod_cast hi1hi, by exact_mod_cast hi2hi⟩⟩
      refine ⟨d, hd, hfiniteCells, ?_, ?_⟩
      · intro z hz
        obtain ⟨i, hzi⟩ := hcover z
        exact Set.mem_iUnion₂.mpr ⟨i, ⟨z, hz, hzi⟩, hzi⟩
      · intro i hi
        obtain ⟨z, hzV, hzi⟩ := hi
        obtain ⟨g, hg⟩ := hmesh z hzV
        refine ⟨g, fun w hwi => hg w ?_⟩
        have hre : |(w - z).re| ≤ d := by
          rw [Complex.sub_re, abs_le]
          constructor <;> linarith [hzi.1, hzi.2.1, hwi.1, hwi.2.1]
        have him : |(w - z).im| ≤ d := by
          rw [Complex.sub_im, abs_le]
          constructor <;> linarith [hzi.2.2.1, hzi.2.2.2, hwi.2.2.1, hwi.2.2.2]
        rw [Metric.mem_ball, dist_eq_norm]
        have hnorm := (Complex.norm_le_abs_re_add_abs_im (w - z)).trans (add_le_add hre him)
        dsimp [d] at hnorm
        linarith
  have htranslateDisks : ∀ v ∈ H, ∀ ε : ℝ, 0 < ε → ε < 1 →
      (fun z : ℂ => z + 1) '' D v ε = D (v + 1) ε := by
    intro v hv ε hε hε1
    simpa only [Complex.ofReal_one, Complex.ofReal_zero, one_mul, zero_mul,
      zero_add, div_one] using (hdisks v ε hv hε hε1).2 1 1 0 1 (by norm_num)
  have hinvertDisks : ∀ v ∈ H, ∀ ε : ℝ, 0 < ε → ε < 1 →
      (fun z : ℂ => -1 / z) '' D v ε = D (-1 / v) ε := by
    intro v hv ε hε hε1
    simpa only [Complex.ofReal_one, Complex.ofReal_zero, Complex.ofReal_neg,
      one_mul, zero_mul, zero_add, add_zero] using
      (hdisks v ε hv hε hε1).2 0 (-1) 1 0 (by norm_num)
  -- Steps 15–16: retain the endpoint functions; their limits come from the cut geometry.
  let γ : ℂ → ℝ → ℝ → ℂ := fun v ε t =>
    (v - star v * ((ε : ℂ) * Complex.exp ((t : ℂ) * Complex.I))) /
      (1 - (ε : ℂ) * Complex.exp ((t : ℂ) * Complex.I))
  -- Steps 9–11: exact coordinates for the cut map and its incident geodesics.
  have hcutCoordinates : ∀ v ∈ H, ∀ w : ℂ, Complex.normSq w < 1 →
      let z := (v - star v * w) / (1 - w)
      0 < z.im ∧
        (z.re - v.re) * Complex.normSq (1 - w) = -2 * v.im * w.im ∧
        (Complex.normSq z - Complex.normSq v) * Complex.normSq (1 - w) =
          4 * v.im * (v * star w).im ∧
        (z - v) / (z - star v) = w := by
    intro v hv w hw
    let z := (v - star v * w) / (1 - w)
    have hden : 1 - w ≠ 0 := by
      intro heq
      have hw1 : w = 1 := (sub_eq_zero.mp heq).symm
      simp only [hw1, Complex.normSq_one, lt_self_iff_false] at hw
    have hD : 0 < Complex.normSq (1 - w) := Complex.normSq_pos.mpr hden
    have hvbar : v - star v ≠ 0 := by
      intro heq
      have him := congrArg Complex.im heq
      have hvpos : 0 < v.im := hv
      simp only [Complex.sub_im, Complex.star_def, Complex.conj_im, Complex.zero_im] at him
      linarith
    have him : z.im * Complex.normSq (1 - w) = v.im * (1 - Complex.normSq w) := by
      dsimp only [z]
      rw [Complex.div_im, ← sub_div, div_mul_cancel₀ _ hD.ne']
      simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
        Complex.one_re, Complex.one_im, Complex.star_def, Complex.conj_re,
        Complex.conj_im, Complex.normSq_apply]
      ring
    refine ⟨(mul_pos_iff_of_pos_right hD).mp
      (him.symm ▸ mul_pos hv (sub_pos.mpr hw)), ?_, ?_, ?_⟩
    · rw [Complex.div_re, ← add_div, sub_mul, div_mul_cancel₀ _ hD.ne']
      simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
        Complex.one_re, Complex.one_im, Complex.star_def, Complex.conj_re,
        Complex.conj_im, Complex.normSq_apply]
      ring
    · rw [Complex.normSq_div, sub_mul, div_mul_cancel₀ _ hD.ne']
      simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
        Complex.mul_re, Complex.mul_im, Complex.one_re, Complex.one_im,
        Complex.star_def, Complex.conj_re, Complex.conj_im]
      ring
    · change (z - v) / (z - star v) = w
      have hsub : z - v = (v - star v) * w / (1 - w) := by
        dsimp only [z]
        field_simp [hden]
        ring
      have hsubbar : z - star v = (v - star v) / (1 - w) := by
        dsimp only [z]
        field_simp [hden]
        ring
      rw [hsub, hsubbar]
      field_simp [hden, hvbar]
  have hgammaOnCut : ∀ v ∈ H, ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ t : ℝ,
      γ v ε t ∈ D v ε ∧
        ‖(γ v ε t - v) / (γ v ε t - star v)‖ = ε ∧ γ v ε t ≠ v := by
    intro v hv ε hε hε1 t
    let w : ℂ := (ε : ℂ) * Complex.exp ((t : ℂ) * Complex.I)
    have hnorm : ‖w‖ = ε := by
      simpa only [w, circleMap, zero_add, abs_of_pos hε] using norm_circleMap_zero ε t
    have hwsq : Complex.normSq w < 1 := by
      rw [Complex.normSq_eq_norm_sq, hnorm]
      nlinarith
    have hc := hcutCoordinates v hv w hwsq
    have hratio : ‖(γ v ε t - v) / (γ v ε t - star v)‖ = ε := by
      change ‖((v - star v * w) / (1 - w) - v) /
        ((v - star v * w) / (1 - w) - star v)‖ = ε
      rw [hc.2.2.2]
      exact hnorm
    refine ⟨⟨hc.1, hratio.le⟩, hratio, ?_⟩
    intro heq
    rw [heq, sub_self, zero_div, norm_zero] at hratio
    linarith
  -- Exact side tests in the cut coordinate identify the retained angular sectors.
  have hgammaSides : ∀ v ∈ H, ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ t : ℝ,
      ((γ v ε t).re < v.re ↔ 0 < Real.sin t) ∧
      (v.re < (γ v ε t).re ↔ Real.sin t < 0) ∧
      ((γ v ε t).re = v.re ↔ Real.sin t = 0) ∧
      (Complex.normSq v < Complex.normSq (γ v ε t) ↔
        0 < v.im * Real.cos t - v.re * Real.sin t) ∧
      (Complex.normSq (γ v ε t) = Complex.normSq v ↔
        v.im * Real.cos t - v.re * Real.sin t = 0) := by
    intro v hv ε hε hε1 t
    let w : ℂ := (ε : ℂ) * Complex.exp ((t : ℂ) * Complex.I)
    have hnorm : ‖w‖ = ε := by
      simp [w, Complex.norm_exp, abs_of_pos hε]
    have hwsq : Complex.normSq w < 1 := by
      rw [Complex.normSq_eq_norm_sq, hnorm]
      nlinarith
    have hden : 1 - w ≠ 0 := by
      intro h
      have hw : w = 1 := (sub_eq_zero.mp h).symm
      rw [hw, norm_one] at hnorm
      linarith
    have hD : 0 < Complex.normSq (1 - w) := Complex.normSq_pos.mpr hden
    have hre : w.re = ε * Real.cos t := by
      simp [w, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    have him : w.im = ε * Real.sin t := by
      simp [w, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    have hcross : (v * star w).im = ε * (v.im * Real.cos t - v.re * Real.sin t) := by
      simp only [Complex.mul_im, Complex.star_def, Complex.conj_re, Complex.conj_im,
        hre, him]
      ring
    have hc := hcutCoordinates v hv w hwsq
    have hx : ((γ v ε t).re - v.re) * Complex.normSq (1 - w) =
        -(2 * v.im * ε) * Real.sin t := by
      change (((v - star v * w) / (1 - w)).re - v.re) * Complex.normSq (1 - w) = _
      rw [hc.2.1, him]
      ring
    have hn : (Complex.normSq (γ v ε t) - Complex.normSq v) * Complex.normSq (1 - w) =
        (4 * v.im * ε) * (v.im * Real.cos t - v.re * Real.sin t) := by
      change (Complex.normSq ((v - star v * w) / (1 - w)) - Complex.normSq v) *
        Complex.normSq (1 - w) = _
      rw [hc.2.2.1, hcross]
      ring
    have hvpos : 0 < v.im := hv
    have hp : 0 < 2 * v.im * ε := by positivity
    have hp4 : 0 < 4 * v.im * ε := by positivity
    have hnegRight (x : ℝ) : x * Complex.normSq (1 - w) < 0 ↔ x < 0 := by
      simp only [mul_neg_iff, hD, not_lt_of_ge hD.le, and_true, and_false, false_or]
    have hnegLeft (x : ℝ) : (2 * v.im * ε) * x < 0 ↔ x < 0 := by
      simp only [mul_neg_iff, hp, not_lt_of_ge hp.le, false_and, true_and, or_false]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [← sub_neg, ← hnegRight, hx, neg_mul,
        neg_neg_iff_pos, mul_pos_iff_of_pos_left hp]
    · rw [← sub_pos, ← mul_pos_iff_of_pos_right hD, hx, neg_mul,
        neg_pos, hnegLeft]
    · rw [← sub_eq_zero, ← mul_eq_zero_iff_right hD.ne', hx,
        mul_eq_zero_iff_left (neg_ne_zero.mpr hp.ne')]
    · rw [← sub_pos, ← mul_pos_iff_of_pos_right hD, hn, mul_pos_iff_of_pos_left hp4]
    · rw [← sub_eq_zero, ← mul_eq_zero_iff_right hD.ne', hn,
        mul_eq_zero_iff_left hp4.ne']
  have hgammaUnitCircle : ∀ v ∈ H, ‖v‖ = 1 → ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ t : ℝ,
      (1 < ‖γ v ε t‖ ↔ 0 < v.im * Real.cos t - v.re * Real.sin t) ∧
      (‖γ v ε t‖ = 1 ↔ v.im * Real.cos t - v.re * Real.sin t = 0) := by
    intro v hv hvnorm ε hε hε1 t
    have hvSq : Complex.normSq v = 1 := by
      rw [Complex.normSq_eq_norm_sq, hvnorm]
      norm_num
    have hc := (hgammaSides v hv ε hε hε1 t).2.2.2
    rw [hvSq, Complex.normSq_eq_norm_sq] at hc
    have hn := norm_nonneg (γ v ε t)
    refine ⟨?_, ?_⟩
    · have hsq : 1 < ‖γ v ε t‖ ↔ 1 < ‖γ v ε t‖ ^ 2 := by
        constructor <;> intro h <;> nlinarith
      exact hsq.trans hc.1
    · have hsq : ‖γ v ε t‖ = 1 ↔ ‖γ v ε t‖ ^ 2 = 1 := by
        constructor <;> intro h <;> nlinarith
      exact hsq.trans hc.2
  have hρre : ρ.re = -1 / 2 := by simp [ρ]
  have hρim : ρ.im = Real.sqrt 3 / 2 := by simp [ρ]
  have hρnorm : ‖ρ‖ = 1 := by
    have hs : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have hn : ‖ρ‖ ^ 2 = 1 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hρre, hρim]
      nlinarith
    nlinarith [norm_nonneg ρ]
  have hρH : ρ ∈ H := by
    change 0 < ρ.im
    rw [hρim]
    positivity
  have hρOneH : ρ + 1 ∈ H := by simpa [H] using hρH
  have hρOneNorm : ‖ρ + 1‖ = 1 := by
    have hs : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have hn : ‖ρ + 1‖ ^ 2 = 1 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im,
        add_zero, hρre, hρim]
      nlinarith
    nlinarith [norm_nonneg (ρ + 1)]
  have hgammaEllipticEndpoints : ∀ ε : ℝ, 0 < ε → ε < 1 →
      ‖γ Complex.I ε (Real.pi / 2)‖ = 1 ∧
      ‖γ Complex.I ε (-Real.pi / 2)‖ = 1 ∧
      (γ ρ ε 0).re = -1 / 2 ∧ ‖γ ρ ε (-Real.pi / 3)‖ = 1 ∧
      ‖γ (ρ + 1) ε (Real.pi / 3)‖ = 1 ∧ (γ (ρ + 1) ε 0).re = 1 / 2 := by
    intro ε hε hε1
    have hIH : Complex.I ∈ H := by simp [H]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · apply (hgammaUnitCircle Complex.I hIH Complex.norm_I ε hε hε1 _).2.mpr
      simp
    · apply (hgammaUnitCircle Complex.I hIH Complex.norm_I ε hε hε1 _).2.mpr
      simp [neg_div]
    · rw [← hρre]
      exact (hgammaSides ρ hρH ε hε hε1 0).2.2.1.mpr Real.sin_zero
    · apply (hgammaUnitCircle ρ hρH hρnorm ε hε hε1 _).2.mpr
      rw [hρim, hρre, neg_div, Real.cos_neg, Real.sin_neg,
        Real.cos_pi_div_three, Real.sin_pi_div_three]
      ring
    · apply (hgammaUnitCircle (ρ + 1) hρOneH hρOneNorm ε hε hε1 _).2.mpr
      simp only [Complex.add_im, Complex.add_re, Complex.one_im, Complex.one_re,
        add_zero, hρim, hρre, Real.cos_pi_div_three, Real.sin_pi_div_three]
      ring
    · have hc := (hgammaSides (ρ + 1) hρOneH ε hε hε1 0).2.2.1.mpr Real.sin_zero
      simpa only [Complex.add_re, Complex.one_re, hρre, show (-1 / 2 : ℝ) + 1 = 1 / 2 by norm_num] using hc
  have hgammaEllipticSectors : ∀ ε : ℝ, 0 < ε → ε < 1 →
      (∀ t ∈ Set.Ioo (-Real.pi / 2) (Real.pi / 2), 1 < ‖γ Complex.I ε t‖) ∧
      (∀ t ∈ Set.Ioo (-Real.pi / 3) 0,
        -1 / 2 < (γ ρ ε t).re ∧ 1 < ‖γ ρ ε t‖) ∧
      (∀ t ∈ Set.Ioo 0 (Real.pi / 3),
        (γ (ρ + 1) ε t).re < 1 / 2 ∧ 1 < ‖γ (ρ + 1) ε t‖) := by
    intro ε hε hε1
    refine ⟨?_, ?_, ?_⟩
    · intro t ht
      apply (hgammaUnitCircle Complex.I (by simp [H]) Complex.norm_I ε hε hε1 t).1.mpr
      simpa using Real.cos_pos_of_mem_Ioo (by simpa only [neg_div] using ht)
    · intro t ht
      constructor
      · rw [← hρre]
        apply (hgammaSides ρ hρH ε hε hε1 t).2.1.mpr
        exact Real.sin_neg_of_neg_of_neg_pi_lt ht.2 (by linarith [ht.1, Real.pi_pos])
      · apply (hgammaUnitCircle ρ hρH hρnorm ε hε hε1 t).1.mpr
        have hsin : 0 < Real.sin (t + Real.pi / 3) :=
          Real.sin_pos_of_pos_of_lt_pi (by linarith [ht.1]) (by linarith [ht.2, Real.pi_pos])
        rw [Real.sin_add, Real.cos_pi_div_three, Real.sin_pi_div_three] at hsin
        rw [hρim, hρre]
        nlinarith
    · intro t ht
      constructor
      · have hside := (hgammaSides (ρ + 1) hρOneH ε hε hε1 t).1.mpr
          (Real.sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2, Real.pi_pos]))
        simpa only [Complex.add_re, Complex.one_re, hρre, show (-1 / 2 : ℝ) + 1 = 1 / 2 by norm_num] using hside
      · apply (hgammaUnitCircle (ρ + 1) hρOneH hρOneNorm ε hε hε1 t).1.mpr
        have hsin : 0 < Real.sin (Real.pi / 3 - t) :=
          Real.sin_pos_of_pos_of_lt_pi (by linarith [ht.2]) (by linarith [ht.1, Real.pi_pos])
        rw [Real.sin_sub, Real.cos_pi_div_three, Real.sin_pi_div_three] at hsin
        simp only [Complex.add_im, Complex.add_re, Complex.one_im, Complex.one_re,
          add_zero, hρim, hρre]
        nlinarith
  have hgammaZeroFree : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ∀ v ∈ Z, ∀ t : ℝ, F (γ v ε t) ≠ 0 := by
    filter_upwards [hsmallCuts, hcutsNoOtherZeros] with ε hε hzero
    intro v hv t
    obtain ⟨hmem, _, hne⟩ := hgammaOnCut v (hKH hv.1) ε hε.1 hε.2 t
    exact hzero v hv (γ v ε t) hmem hne
  -- Steps 9–10: the incident geodesics are radial in the cut coordinate.
  -- The clockwise replacement runs from cutStart to cutEnd.
  let cutStart : ℂ → ℝ := fun v =>
    if v.re = -1 / 2 then 0 else if ‖v‖ = 1 then v.arg else Real.pi
  let cutEnd : ℂ → ℝ := fun v =>
    if v.re = 1 / 2 then 0 else if ‖v‖ = 1 then v.arg - Real.pi else -Real.pi
  have hcutAngles : ∀ v ∈ H,
      -Real.pi ≤ cutEnd v ∧ cutEnd v < cutStart v ∧ cutStart v ≤ Real.pi ∧
        (v.re = -1 / 2 → cutStart v = 0) ∧
        (v.re = 1 / 2 → cutEnd v = 0) ∧
        (‖v‖ = 1 → cutStart v ≤ v.arg ∧ v.arg - Real.pi ≤ cutEnd v) := by
    intro v hv
    have hvim : 0 < v.im := hv
    have harg0 : 0 < v.arg := by
      apply lt_of_le_of_ne (Complex.arg_nonneg_iff.mpr hvim.le)
      intro heq
      have him := Complex.norm_mul_sin_arg v
      rw [← heq, Real.sin_zero, mul_zero] at him
      linarith
    have hargπ : v.arg < Real.pi := Complex.arg_lt_pi_iff.mpr (Or.inr hvim.ne')
    have hlow : -Real.pi ≤ cutEnd v := by
      dsimp only [cutEnd]
      split_ifs <;> linarith [Real.pi_pos]
    have hhigh : cutStart v ≤ Real.pi := by
      dsimp only [cutStart]
      split_ifs <;> linarith [Real.pi_pos]
    have horder : cutEnd v < cutStart v := by
      dsimp only [cutStart, cutEnd]
      split_ifs <;> linarith [Real.pi_pos]
    refine ⟨hlow, horder, hhigh, ?_, ?_, ?_⟩
    · intro hvL
      simp only [cutStart, hvL, if_pos]
    · intro hvR
      simp only [cutEnd, hvR, if_pos]
    · intro hvN
      constructor
      · simp only [cutStart, hvN, if_pos]
        split_ifs <;> linarith
      · simp only [cutEnd, hvN, if_pos]
        split_ifs <;> linarith
  have hρarg : ρ.arg = 2 * Real.pi / 3 := by
    rw [Complex.arg_of_im_pos hρH, hρre, hρnorm, div_one]
    have hcos : Real.cos (2 * Real.pi / 3) = -1 / 2 := by
      rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring,
        Real.cos_pi_sub, Real.cos_pi_div_three]
      norm_num
    rw [← hcos]
    exact Real.arccos_cos (by positivity) (by linarith [Real.pi_pos])
  have hρOneArg : (ρ + 1).arg = Real.pi / 3 := by
    rw [Complex.arg_of_im_pos hρOneH, Complex.add_re, Complex.one_re,
      hρre, hρOneNorm, div_one]
    norm_num only
    rw [← Real.cos_pi_div_three]
    exact Real.arccos_cos (by positivity) (by linarith [Real.pi_pos])
  have hcutEllipticAngles :
      cutStart Complex.I = Real.pi / 2 ∧ cutEnd Complex.I = -Real.pi / 2 ∧
      cutStart ρ = 0 ∧ cutEnd ρ = -Real.pi / 3 ∧
      cutStart (ρ + 1) = Real.pi / 3 ∧ cutEnd (ρ + 1) = 0 := by
    norm_num [cutStart, cutEnd, Complex.arg_I, hρre, hρnorm, hρarg,
      hρOneNorm, hρOneArg]
    constructor <;> ring
  have hphaseNorm (ε : ℝ) (hε : 0 < ε) (t : ℝ) :
      ‖(ε : ℂ) * Complex.exp ((t : ℂ) * Complex.I)‖ = ε := by
    simpa only [circleMap, zero_add, abs_of_pos hε] using norm_circleMap_zero ε t
  have hphaseDen (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (t : ℝ) :
      1 - (ε : ℂ) * Complex.exp ((t : ℂ) * Complex.I) ≠ 0 := by
    intro heq
    have hn := hphaseNorm ε hε t
    rw [← sub_eq_zero.mp heq, norm_one] at hn
    linarith
  have hgammaSmooth : ∀ v : ℂ, ∀ ε : ℝ, 0 < ε → ε < 1 → ContDiff ℝ 1 (γ v ε) := by
    intro v ε hε hε1
    have hw : ContDiff ℝ 1 (fun t : ℝ => (ε : ℂ) * Complex.exp ((t : ℂ) * Complex.I)) := by
      convert! (contDiff_circleMap 0 ε (n := 1)) using 1
      funext t
      simp only [circleMap, zero_add]
    convert! (contDiff_const.sub (contDiff_const.mul hw)).mul
      ((contDiff_const.sub hw).inv (hphaseDen ε hε hε1)) using 1
  -- The cut coordinate parametrizes the entire Euclidean cut circle.
  have hgammaSphere : ∀ v ∈ H, ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ t : ℝ,
      γ v ε t ∈ Metric.sphere (cutCenter v ε) (cutRadius v ε) := by
    intro v hv ε hε hε1 t
    have hball : D v ε = Metric.closedBall (cutCenter v ε) (cutRadius v ε) :=
      (hdisks v ε hv hε hε1).1
    have hmem := (hgammaOnCut v hv ε hε hε1 t).1
    rw [hball] at hmem
    change dist (γ v ε t) (cutCenter v ε) = cutRadius v ε
    apply le_antisymm (Metric.mem_closedBall.mp hmem)
    by_contra! hlt
    have hvar : ContinuousAt (fun η : ℝ => γ v η t) ε := by
      dsimp only [γ]
      fun_prop (disch := exact hphaseDen ε hε hε1 t)
    have hnear : ∀ᶠ η in nhdsWithin ε (Set.Ioi ε),
        γ v η t ∈ Metric.ball (cutCenter v ε) (cutRadius v ε) ∧ η < 1 :=
      ((hvar.tendsto.eventually (Metric.isOpen_ball.mem_nhds hlt)).and
        (eventually_lt_nhds hε1)).filter_mono nhdsWithin_le_nhds
    have hlarge : ∀ᶠ η in nhdsWithin ε (Set.Ioi ε), ε < η := self_mem_nhdsWithin
    obtain ⟨η, hη, hηball, hη1⟩ := (hlarge.and hnear).exists
    have hηmem : γ v η t ∈ D v ε := hball ▸ Metric.ball_subset_closedBall hηball
    have hratio := (hgammaOnCut v hv η (hε.trans hη) hη1 t).2.1
    have hle := hηmem.2
    rw [hratio] at hle
    exact (not_le_of_gt hη) hle
  have hcutCircleRepresentation : ∀ v ∈ H, ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∀ z ∈ Metric.sphere (cutCenter v ε) (cutRadius v ε),
        ∃ t : ℝ, -Real.pi < t ∧ t ≤ Real.pi ∧ γ v ε t = z := by
    intro v hv ε hε hε1 z hz
    have hball : D v ε = Metric.closedBall (cutCenter v ε) (cutRadius v ε) :=
      (hdisks v ε hv hε hε1).1
    have hzD : z ∈ D v ε := hball ▸ Metric.sphere_subset_closedBall hz
    have hden : z - star v ≠ 0 := by
      intro heq
      have hi := congrArg Complex.im heq
      have hvpos : 0 < v.im := hv
      have hzpos : 0 < z.im := hzD.1
      simp only [Complex.sub_im, Complex.star_def, Complex.conj_im, Complex.zero_im] at hi
      linarith
    let w : ℂ := (z - v) / (z - star v)
    have hw : ‖w‖ = ε := by
      apply le_antisymm hzD.2
      by_contra! hlt
      have hcont : ContinuousAt (fun x : ℂ => ‖(x - v) / (x - star v)‖) z := by
        fun_prop
      have hnear : ∀ᶠ x in nhds z, x ∈ D v ε := by
        filter_upwards [hH.mem_nhds hzD.1,
          hcont.tendsto.eventually (eventually_lt_nhds hlt)] with x hx hxnorm
        exact ⟨hx, hxnorm.le⟩
      have hzint : z ∈ interior (D v ε) := mem_interior_iff_mem_nhds.mpr hnear
      rw [hball, interior_closedBall'] at hzint
      exact (not_lt_of_ge (Metric.mem_sphere.mp hz).ge) hzint
    have hphase : (ε : ℂ) * Complex.exp ((w.arg : ℂ) * Complex.I) = w := by
      simpa only [hw] using Complex.norm_mul_exp_arg_mul_I w
    refine ⟨w.arg, Complex.neg_pi_lt_arg w, Complex.arg_le_pi w, ?_⟩
    dsimp only [γ]
    rw [hphase]
    have hwden : 1 - w ≠ 0 := by
      intro heq
      have hw1 : w = 1 := (sub_eq_zero.mp heq).symm
      rw [hw1, norm_one] at hw
      linarith
    apply (div_eq_iff hwden).mpr
    dsimp only [w]
    field_simp
    ring
  -- Small cuts meet none of the original boundary pieces not incident at their center.
  have hcutInactive : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ∀ v ∈ B, ∀ z ∈ D v ε,
        (v.re ≠ -1 / 2 → -1 / 2 < z.re) ∧
        (v.re ≠ 1 / 2 → z.re < 1 / 2) ∧ (‖v‖ ≠ 1 → 1 < ‖z‖) := by
    apply (Filter.eventually_all_finite hBfinite).mpr
    intro v hv
    have hleft : ∀ᶠ z in nhds v, v.re ≠ -1 / 2 → -1 / 2 < z.re := by
      by_cases hvL : v.re = -1 / 2
      · exact Filter.Eventually.of_forall (fun _ hn => (hn hvL).elim)
      have hlt : (-1 / 2 : ℝ) < v.re := by
        have hle := (abs_le.mp hv.1.1.1).1
        have hne : -(1 / 2 : ℝ) ≠ v.re := by simpa only [neg_div] using Ne.symm hvL
        simpa only [neg_div] using lt_of_le_of_ne hle hne
      exact Filter.Eventually.mono
        ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hlt)
        (fun _ hz _ => hz)
    have hright : ∀ᶠ z in nhds v, v.re ≠ 1 / 2 → z.re < 1 / 2 := by
      by_cases hvR : v.re = 1 / 2
      · exact Filter.Eventually.of_forall (fun _ hn => (hn hvR).elim)
      exact Filter.Eventually.mono
        ((isOpen_lt Complex.continuous_re continuous_const).mem_nhds
          (lt_of_le_of_ne (abs_le.mp hv.1.1.1).2 hvR)) (fun _ hz _ => hz)
    have hnorm : ∀ᶠ z in nhds v, ‖v‖ ≠ 1 → 1 < ‖z‖ := by
      by_cases hvN : ‖v‖ = 1
      · exact Filter.Eventually.of_forall (fun _ hn => (hn hvN).elim)
      exact Filter.Eventually.mono
        ((isOpen_lt continuous_const continuous_norm).mem_nhds
          (lt_of_le_of_ne hv.1.1.2.1 (Ne.symm hvN))) (fun _ hz _ => hz)
    obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp (hleft.and (hright.and hnorm))
    filter_upwards [hdiskShrink v (hKH hv.1.1) r hr] with ε hε
    exact fun z hz => hball z (hε hz)
  have hunitInversion : ∀ v : ℂ, ‖v‖ = 1 → -1 / v = -star v := by
    intro v hv
    simp only [div_eq_mul_inv, Complex.inv_eq_conj hv, neg_mul, one_mul,
      Complex.star_def]
  have hboundaryCenterS : ∀ v ∈ B, ‖v‖ = 1 → -1 / v ∈ B := by
    intro v hv hvnorm
    have him : (-1 / v).im = v.im := by
      rw [hunitInversion v hvnorm]
      simp only [Complex.neg_im, Complex.star_def, Complex.conj_im, neg_neg]
    have hre : (-1 / v).re = -v.re := by
      rw [hunitInversion v hvnorm]
      simp only [Complex.neg_re, Complex.star_def, Complex.conj_re]
    have hn : ‖-1 / v‖ = 1 := by rw [norm_div]; simp [hvnorm]
    refine ⟨⟨⟨?_, hn.ge, him ▸ hv.1.1.2.2.1, ?_⟩, ?_⟩, ?_⟩
    · simpa only [hre, abs_neg] using hv.1.1.1
    · simpa only [him] using hv.1.1.2.2.2
    · rw [hS v hv.1.1.2.2.1, hv.1.2, mul_zero]
    · intro hO
      exact (lt_irrefl (1 : ℝ)) (hn ▸ hO.2.1)
  have hboundaryCenterT : ∀ v ∈ B, v.re = -1 / 2 → v + 1 ∈ B := by
    intro v hv hvre
    have hre : (v + 1).re = 1 / 2 := by simp only [Complex.add_re, Complex.one_re, hvre]; norm_num
    have him : (v + 1).im = v.im := by simp
    have hn : ‖v + 1‖ = ‖v‖ := by
      apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
      rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
      simp only [Complex.normSq_apply, hre, him, hvre]
      ring
    refine ⟨⟨⟨?_, hn ▸ hv.1.1.2.1, him ▸ hv.1.1.2.2.1, ?_⟩, ?_⟩, ?_⟩
    · rw [hre, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    · simpa only [him] using hv.1.1.2.2.2
    · rw [hT v hv.1.1.2.2.1, hv.1.2]
    · intro hO
      have hlt := (abs_lt.mp hO.1).2
      rw [hre] at hlt
      exact lt_irrefl _ hlt
  have hboundaryCenterTinv : ∀ v ∈ B, v.re = 1 / 2 → v - 1 ∈ B := by
    intro v hv hvre
    have hre : (v - 1).re = -1 / 2 := by simp only [Complex.sub_re, Complex.one_re, hvre]; norm_num
    have him : (v - 1).im = v.im := by simp
    have hn : ‖v - 1‖ = ‖v‖ := by
      apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
      rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
      simp only [Complex.normSq_apply, hre, him, hvre]
      ring
    refine ⟨⟨⟨?_, hn ▸ hv.1.1.2.1, him ▸ hv.1.1.2.2.1, ?_⟩, ?_⟩, ?_⟩
    · norm_num [hre]
    · simpa only [him] using hv.1.1.2.2.2
    · have heq := hT (v - 1) (him ▸ hv.1.1.2.2.1)
      rw [sub_add_cancel, hv.1.2] at heq
      exact heq.symm
    · intro hO
      have hlt := (abs_lt.mp hO.1).1
      rw [hre] at hlt
      norm_num at hlt
  -- The same cut parameter removes matching portions of the paired outer sides.
  have hpairedRemoved : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (∀ z : ℂ, ‖z‖ = 1 →
        (z ∈ ⋃ v ∈ B, D v ε ↔ -1 / z ∈ ⋃ v ∈ B, D v ε)) ∧
      (∀ z : ℂ, z.re = -1 / 2 →
        (z ∈ ⋃ v ∈ B, D v ε ↔ z + 1 ∈ ⋃ v ∈ B, D v ε)) := by
    filter_upwards [hsmallCuts, hcutInactive] with ε hε hinactive
    have hs : ∀ z : ℂ, ‖z‖ = 1 →
        z ∈ ⋃ v ∈ B, D v ε → -1 / z ∈ ⋃ v ∈ B, D v ε := by
      intro z hzn hz
      obtain ⟨v, hv, hzv⟩ := Set.mem_iUnion₂.mp hz
      have hvn : ‖v‖ = 1 := by
        by_contra hn
        have hlt := (hinactive v hv z hzv).2.2 hn
        rw [hzn] at hlt
        exact lt_irrefl _ hlt
      refine Set.mem_iUnion₂.mpr ⟨-1 / v, hboundaryCenterS v hv hvn, ?_⟩
      rw [← hinvertDisks v (hKH hv.1.1) ε hε.1 hε.2]
      exact Set.mem_image_of_mem _ hzv
    constructor
    · intro z hzn
      refine ⟨hs z hzn, fun hz => ?_⟩
      have hn : ‖-1 / z‖ = 1 := by rw [norm_div]; simp [hzn]
      simpa only [div_eq_mul_inv, mul_inv_rev, inv_neg, inv_one, inv_inv,
        mul_neg, mul_one, neg_mul, one_mul, neg_neg] using hs (-1 / z) hn hz
    · intro z hzre
      constructor
      · intro hz
        obtain ⟨v, hv, hzv⟩ := Set.mem_iUnion₂.mp hz
        have hvre : v.re = -1 / 2 := by
          by_contra hn
          have hlt := (hinactive v hv z hzv).1 hn
          rw [hzre] at hlt
          exact lt_irrefl _ hlt
        refine Set.mem_iUnion₂.mpr ⟨v + 1, hboundaryCenterT v hv hvre, ?_⟩
        rw [← htranslateDisks v (hKH hv.1.1) ε hε.1 hε.2]
        exact Set.mem_image_of_mem _ hzv
      · intro hz
        obtain ⟨v, hv, hzv⟩ := Set.mem_iUnion₂.mp hz
        have hzr : (z + 1).re = 1 / 2 := by
          simp only [Complex.add_re, Complex.one_re, hzre]
          norm_num
        have hvre : v.re = 1 / 2 := by
          by_contra hn
          have hlt := (hinactive v hv (z + 1) hzv).2.1 hn
          rw [hzr] at hlt
          exact lt_irrefl _ hlt
        have hv' := hboundaryCenterTinv v hv hvre
        refine Set.mem_iUnion₂.mpr ⟨v - 1, hv', ?_⟩
        have himage := htranslateDisks (v - 1) (hKH hv'.1.1) ε hε.1 hε.2
        rw [sub_add_cancel] at himage
        rw [← himage] at hzv
        obtain ⟨w, hw, heq⟩ := hzv
        have hwz : w = z := add_right_cancel heq
        exact hwz ▸ hw
  -- Step 14: the paired integrand is bounded even as the cuts shrink to zeros.
  let removed : ℝ → Set ℂ := fun ε => ⋃ v ∈ B, D v ε
  have hremovedClosed : ∀ ε : ℝ, 0 < ε → ε < 1 → IsClosed (removed ε) := by
    intro ε hε hε1
    apply hBfinite.isClosed_biUnion
    intro v hv
    rw [show D v ε = _ from (hdisks v ε (hKH hv.1.1) hε hε1).1]
    exact Metric.isClosed_closedBall
  have hremovedAvoid : ∀ z : ℂ, z ∉ B →
      ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), z ∉ removed ε := by
    intro z hz
    have havoid : ∀ v ∈ B,
        ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), z ∉ D v ε := by
      intro v hv
      have hne : z ≠ v := fun heq => hz (heq ▸ hv)
      filter_upwards [hdiskShrink v (hKH hv.1.1) (dist z v) (dist_pos.mpr hne)]
        with ε hε
      exact fun hmem => (lt_irrefl (dist z v)) (hε hmem)
    filter_upwards [(Filter.eventually_all_finite hBfinite).mpr havoid] with ε hε
    intro hmem
    obtain ⟨v, hv, hzv⟩ := Set.mem_iUnion₂.mp hmem
    exact hε v hv hzv
  have hretainedCircleLimit : ∀ (a b : ℝ) (c : ℂ),
      Filter.Tendsto (fun ε : ℝ => intervalIntegral
        (fun t : ℝ => if circleMap 0 1 t ∈ removed ε then 0 else c)
        a b MeasureTheory.volume)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (((b - a : ℝ) : ℂ) * c)) := by
    intro a b c
    have hcount : (circleMap 0 1 ⁻¹' B).Countable :=
      hBfinite.countable.preimage_circleMap 0 (by norm_num)
    have hae : ∀ᵐ t : ℝ ∂MeasureTheory.volume, circleMap 0 1 t ∉ B :=
      hcount.ae_notMem MeasureTheory.volume
    have hlim := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (a := a) (b := b) (μ := MeasureTheory.volume)
      (l := nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (F := fun ε t => if circleMap 0 1 t ∈ removed ε then (0 : ℂ) else c)
      (f := fun _ => c) (fun _ => ‖c‖) ?_ ?_ intervalIntegrable_const ?_
    · simpa only [intervalIntegral.integral_const, smul_eq_mul, Complex.real_smul]
        using hlim
    · filter_upwards [hsmallCuts] with ε hε
      have hm : MeasurableSet {t : ℝ | circleMap 0 1 t ∈ removed ε} :=
        (hremovedClosed ε hε.1 hε.2).measurableSet.preimage (by fun_prop)
      exact ((MeasureTheory.stronglyMeasurable_const.piecewise hm
          MeasureTheory.stronglyMeasurable_const)
        : MeasureTheory.StronglyMeasurable (fun t : ℝ =>
          if circleMap 0 1 t ∈ removed ε then (0 : ℂ) else c)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun ε => Filter.Eventually.of_forall
        (fun t _ => by split_ifs <;> simp))
    · filter_upwards [hae] with t ht
      intro _
      apply tendsto_const_nhds.congr'
      filter_upwards [hremovedAvoid (circleMap 0 1 t) ht] with ε hε
      simp only [if_neg hε]
  have hleftArcMem : ∀ t ∈ Set.Icc (Real.pi / 2) (2 * Real.pi / 3),
      circleMap 0 1 t ∈ K ∧ circleMap 0 1 t ∉ O := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht.1
    have htπ : t < Real.pi := by linarith only [ht.2, Real.pi_pos]
    have hcos : Real.cos (2 * Real.pi / 3) = -1 / 2 := by
      rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring,
        Real.cos_pi_sub, Real.cos_pi_div_three]
      norm_num
    have hlo := Real.cos_le_cos_of_nonneg_of_le_pi ht0.le
      (show 2 * Real.pi / 3 ≤ Real.pi by linarith [Real.pi_pos]) ht.2
    have hhi := Real.cos_le_cos_of_nonneg_of_le_pi (by positivity : 0 ≤ Real.pi / 2)
      htπ.le ht.1
    rw [hcos] at hlo
    rw [Real.cos_pi_div_two] at hhi
    have hnorm : ‖circleMap 0 1 t‖ = 1 := by
      simp only [norm_circleMap_zero, abs_one]
    have him : (circleMap 0 1 t).im = Real.sin t := by simp [circleMap_zero_im]
    have hre : (circleMap 0 1 t).re = Real.cos t := by simp [circleMap_zero_re]
    refine ⟨⟨?_, hnorm.ge, ?_, ?_⟩, ?_⟩
    · rw [hre, abs_le]
      constructor <;> linarith
    · rw [him]
      exact Real.sin_pos_of_pos_of_lt_pi ht0 htπ
    · rw [him]
      exact (Real.sin_le_one t).trans hY.le
    · intro hmem
      simpa only [hnorm, lt_self_iff_false] using hmem.2.1
  let pairedLower : ℝ → ℂ := fun ε => intervalIntegral
    (fun t : ℝ => if circleMap 0 1 t ∈ removed ε then 0 else
      (L (circleMap 0 1 t) - L (-1 / circleMap 0 1 t) / (circleMap 0 1 t) ^ 2) *
        (Complex.I * circleMap 0 1 t))
    (2 * Real.pi / 3) (Real.pi / 2) MeasureTheory.volume
  have hpairedLowerEq : ∀ ε : ℝ, 0 < ε → pairedLower ε = intervalIntegral
      (fun t : ℝ => if circleMap 0 1 t ∈ removed ε then 0 else -(k : ℂ) * Complex.I)
      (2 * Real.pi / 3) (Real.pi / 2) MeasureTheory.volume := by
    intro ε hε
    dsimp only [pairedLower]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_ge (by linarith [Real.pi_pos] : Real.pi / 2 ≤ 2 * Real.pi / 3)] at ht
    dsimp only
    split_ifs with hmem
    · rfl
    · have hz := hleftArcMem t ht
      have hne : F (circleMap 0 1 t) ≠ 0 := by
        intro hzero
        exact hmem (Set.mem_iUnion₂.mpr
          ⟨circleMap 0 1 t, ⟨⟨hz.1, hzero⟩, hz.2⟩,
            interior_subset (hcenterInterior _ (hKH hz.1) ε hε)⟩)
      exact harcPair _ (hKH hz.1) hne
  have hpairedLowerLimit : Filter.Tendsto pairedLower
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (2 * (Real.pi : ℂ) * Complex.I * ((k : ℂ) / 12))) := by
    have hlim := hretainedCircleLimit (2 * Real.pi / 3) (Real.pi / 2)
      (-(k : ℂ) * Complex.I)
    have heq : (((Real.pi / 2 - 2 * Real.pi / 3 : ℝ) : ℂ) * (-(k : ℂ) * Complex.I)) =
        2 * (Real.pi : ℂ) * Complex.I * ((k : ℂ) / 12) := by
      push_cast
      ring
    rw [heq] at hlim
    apply hlim.congr'
    filter_upwards [hsmallCuts] with ε hε
    exact (hpairedLowerEq ε hε.1).symm
  let verticalContribution : ℝ → ℂ := fun ε =>
    intervalIntegral (fun t : ℝ =>
      if ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) ∈ removed ε then 0 else
        L ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) * Complex.I)
      (Real.sqrt 3 / 2) Y MeasureTheory.volume +
    intervalIntegral (fun t : ℝ =>
      if ((-1 / 2 : ℂ) + (t : ℂ) * Complex.I) ∈ removed ε then 0 else
        L ((-1 / 2 : ℂ) + (t : ℂ) * Complex.I) * Complex.I)
      Y (Real.sqrt 3 / 2) MeasureTheory.volume
  have hretainedVertical : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      verticalContribution ε = 0 := by
    have hbottom : Real.sqrt 3 / 2 < Y := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg 3, hY]
    filter_upwards [hsmallCuts, hpairedRemoved] with ε hε hpaired
    have hp : intervalIntegral (fun t : ℝ =>
        if ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) ∈ removed ε then 0 else
          L ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) * Complex.I)
        (Real.sqrt 3 / 2) Y MeasureTheory.volume =
      intervalIntegral (fun t : ℝ =>
        if ((-1 / 2 : ℂ) + (t : ℂ) * Complex.I) ∈ removed ε then 0 else
          L ((-1 / 2 : ℂ) + (t : ℂ) * Complex.I) * Complex.I)
        (Real.sqrt 3 / 2) Y MeasureTheory.volume := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le hbottom.le] at ht
      let z : ℂ := (-1 / 2 : ℂ) + (t : ℂ) * Complex.I
      have hre : z.re = -1 / 2 := by simp [z]
      have him : z.im = t := by simp [z]
      have hpos : 0 < z.im := by rw [him]; exact lt_of_lt_of_le (by positivity) ht.1
      have hn : 1 ≤ ‖z‖ := by
        have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
        have heq := Complex.sq_norm_sub_sq_re z
        rw [hre, him] at heq
        nlinarith [norm_nonneg z, Real.sqrt_nonneg 3, ht.1]
      have hzK : z ∈ K :=
        ⟨by rw [hre]; norm_num, hn, hpos, by simpa only [him] using ht.2⟩
      have hzO : z ∉ O := by
        intro hmem
        have h := (abs_lt.mp hmem.1).1
        rw [hre] at h
        linarith
      have hzT : z + 1 = (1 / 2 : ℂ) + (t : ℂ) * Complex.I := by dsimp [z]; ring
      have hcut : z + 1 ∈ removed ε ↔ z ∈ removed ε := (hpaired.2 z hre).symm
      dsimp only
      rw [← hzT]
      change (if z + 1 ∈ removed ε then 0 else L (z + 1) * Complex.I) =
        (if z ∈ removed ε then 0 else L z * Complex.I)
      rw [hcut]
      by_cases hmem : z ∈ removed ε
      · simp only [hmem, if_true]
      · have hne : F z ≠ 0 := by
          intro hzero
          exact hmem (Set.mem_iUnion₂.mpr
            ⟨z, ⟨⟨hzK, hzero⟩, hzO⟩, interior_subset (hcenterInterior z hpos ε hε.1)⟩)
        simp only [if_neg hmem, hperiod z hpos hne]
    dsimp only [verticalContribution]
    rw [hp, intervalIntegral.integral_symm Y (Real.sqrt 3 / 2), neg_add_cancel]
  have hcutArcInterior : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ∀ v ∈ B, ∀ t ∈ Set.Ioo (cutEnd v) (cutStart v), γ v ε t ∈ O := by
    filter_upwards [hsmallCuts, hcutInactive, hcutsBelowTop] with ε hε hinactive htop
    intro v hv t ht
    let w : ℂ := (ε : ℂ) * Complex.exp ((t : ℂ) * Complex.I)
    have hvH := hKH hv.1.1
    have hvim : 0 < v.im := hvH
    have hD : 0 < Complex.normSq (1 - w) := Complex.normSq_pos.mpr
      (hphaseDen ε hε.1 hε.2 t)
    have hwsq : Complex.normSq w < 1 := by
      rw [Complex.normSq_eq_norm_sq, hphaseNorm ε hε.1 t]
      nlinarith [hε.1, hε.2]
    have hc := hcutCoordinates v hvH w hwsq
    change 0 < (γ v ε t).im ∧
      ((γ v ε t).re - v.re) * Complex.normSq (1 - w) = -2 * v.im * w.im ∧
      (Complex.normSq (γ v ε t) - Complex.normSq v) * Complex.normSq (1 - w) =
        4 * v.im * (v * star w).im ∧ _ at hc
    have hmem := (hgammaOnCut v hvH ε hε.1 hε.2 t).1
    have hkeep := hinactive v hv (γ v ε t) hmem
    have ha := hcutAngles v hvH
    have hwre : w.re = ε * Real.cos t := by simp [w, Complex.exp_re]
    have hwim : w.im = ε * Real.sin t := by simp [w, Complex.exp_im]
    have hleft : (-1 / 2 : ℝ) < (γ v ε t).re := by
      by_cases hvL : v.re = -1 / 2
      · have ht0 : t < 0 := by rw [ha.2.2.2.1 hvL] at ht; exact ht.2
        have hneg : w.im < 0 := by
          rw [hwim]
          exact mul_neg_of_pos_of_neg hε.1
            (Real.sin_neg_of_neg_of_neg_pi_lt ht0 (lt_of_le_of_lt ha.1 ht.1))
        have hprod : 0 < -2 * v.im * w.im := mul_pos_of_neg_of_neg (by linarith) hneg
        rw [← hc.2.1] at hprod
        have hdiff := (mul_pos_iff_of_pos_right hD).mp hprod
        rw [hvL] at hdiff
        linarith
      · exact hkeep.1 hvL
    have hright : (γ v ε t).re < 1 / 2 := by
      by_cases hvR : v.re = 1 / 2
      · have ht0 : 0 < t := by rw [ha.2.2.2.2.1 hvR] at ht; exact ht.1
        have hpos : 0 < w.im := by
          rw [hwim]
          exact mul_pos hε.1
            (Real.sin_pos_of_pos_of_lt_pi ht0 (lt_of_lt_of_le ht.2 ha.2.2.1))
        have hprod : -2 * v.im * w.im < 0 := mul_neg_of_neg_of_pos (by linarith) hpos
        rw [← hc.2.1] at hprod
        have hdiff : (γ v ε t).re - v.re < 0 := by
          rcases mul_neg_iff.mp hprod with h | h
          · exact (not_lt_of_ge hD.le h.2).elim
          · exact h.1
        rw [hvR] at hdiff
        linarith
      · exact hkeep.2.1 hvR
    have hnorm : 1 < ‖γ v ε t‖ := by
      by_cases hvN : ‖v‖ = 1
      · have hsector := ha.2.2.2.2.2 hvN
        have hsin : 0 < Real.sin (v.arg - t) :=
          Real.sin_pos_of_pos_of_lt_pi (by linarith [ht.2]) (by linarith [ht.1])
        have hv0 : v ≠ 0 := norm_ne_zero_iff.mp (by rw [hvN]; norm_num)
        have hvre : v.re = Real.cos v.arg := by simpa only [hvN, div_one] using (Complex.cos_arg hv0).symm
        have hvim' : v.im = Real.sin v.arg := by simpa only [hvN, div_one] using (Complex.sin_arg v).symm
        have hcross : (v * star w).im = ε * Real.sin (v.arg - t) := by
          rw [Complex.mul_im, Complex.star_def, Complex.conj_im, Complex.conj_re,
            hwre, hwim, hvre, hvim', Real.sin_sub]
          ring
        have hprod : 0 < 4 * v.im * (v * star w).im := by
          rw [hcross]
          exact mul_pos (by positivity) (mul_pos hε.1 hsin)
        rw [← hc.2.2.1] at hprod
        have hdiff := (mul_pos_iff_of_pos_right hD).mp hprod
        rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, hvN] at hdiff
        nlinarith [norm_nonneg (γ v ε t)]
      · exact hkeep.2.2 hvN
    exact ⟨abs_lt.mpr ⟨by linarith, hright⟩, hnorm, hc.1, htop v hv.1 hmem⟩
  have hcutArcs : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ∀ v ∈ B,
        Set.MapsTo (γ v ε) (Set.Icc (cutEnd v) (cutStart v)) (frontier (Ω ε)) ∧
        (∀ t : ℝ, HasDerivAt (γ v ε) (deriv (γ v ε) t) t) ∧
        IntervalIntegrable (fun t => L (γ v ε t) * deriv (γ v ε) t)
          MeasureTheory.volume (cutStart v) (cutEnd v) := by
    filter_upwards [hsmallCuts, hcutArcInterior, hcutsDisjoint, hgammaZeroFree]
      with ε hε harc hdisjoint hzero
    intro v hv
    have hvH := hKH hv.1.1
    have hγsmooth := hgammaSmooth v ε hε.1 hε.2
    let U := O \ ⋃ w ∈ B \ {v}, D w ε
    have hUopen : IsOpen U := by
      apply hOopen.sdiff
      apply (hBfinite.sdiff : (B \ {v}).Finite).isClosed_biUnion
      intro w hw
      rw [show D w ε = _ from (hdisks w ε (hKH hw.1.1.1) hε.1 hε.2).1]
      exact Metric.isClosed_closedBall
    have hfrontierArc : ∀ t ∈ Set.Ioo (cutEnd v) (cutStart v), γ v ε t ∈ frontier (Ω ε) := by
      intro t ht
      have hzD := (hgammaOnCut v hvH ε hε.1 hε.2 t).1
      have hzU : γ v ε t ∈ U := by
        refine ⟨harc v hv t ht, ?_⟩
        intro hzother
        obtain ⟨w, hw, hzw⟩ := Set.mem_iUnion₂.mp hzother
        exact Set.disjoint_left.mp (hdisjoint hv.1 hw.1.1 (Ne.symm hw.2)) hzD hzw
      rw [(hcutOpen ε hε.1 hε.2).frontier_eq]
      refine ⟨?_, fun hz => hz.2 (Set.mem_iUnion₂.mpr ⟨v, hv, hzD⟩)⟩
      apply mem_closure_iff.mpr
      intro W hW hzW
      have hvar : ContinuousAt (fun η : ℝ => γ v η t) ε := by
        dsimp only [γ]
        fun_prop (disch := exact hphaseDen ε hε.1 hε.2 t)
      have hnear : ∀ᶠ η in nhds ε, γ v η t ∈ W ∩ U :=
        hvar.tendsto.eventually ((hW.inter hUopen).mem_nhds ⟨hzW, hzU⟩)
      have hnear' : ∀ᶠ η in nhdsWithin ε (Set.Ioi ε),
          γ v η t ∈ W ∩ U ∧ η < 1 :=
        (hnear.and (eventually_lt_nhds hε.2)).filter_mono nhdsWithin_le_nhds
      have hlarge : ∀ᶠ η in nhdsWithin ε (Set.Ioi ε), ε < η := self_mem_nhdsWithin
      obtain ⟨η, hη, ⟨hηW, hηU⟩, hη1⟩ := (hlarge.and hnear').exists
      refine ⟨γ v η t, hηW, hηU.1, ?_⟩
      intro hcut
      obtain ⟨w, hw, hηw⟩ := Set.mem_iUnion₂.mp hcut
      by_cases hwv : w = v
      · subst w
        have hratio := (hgammaOnCut v hvH η (lt_trans hε.1 hη) hη1 t).2.1
        have hle : ‖(γ v η t - v) / (γ v η t - star v)‖ ≤ ε := hηw.2
        rw [hratio] at hle
        exact (not_le_of_gt hη) hle
      · exact hηU.2 (Set.mem_iUnion₂.mpr ⟨w, ⟨hw, hwv⟩, hηw⟩)
    have hclosed : IsClosed {t : ℝ | γ v ε t ∈ frontier (Ω ε)} :=
      isClosed_frontier.preimage hγsmooth.continuous
    have hclosure := closure_minimal hfrontierArc hclosed
    rw [closure_Ioo (hcutAngles v hvH).2.1.ne] at hclosure
    have hLcont : Continuous (fun t : ℝ => L (γ v ε t)) := by
      apply continuous_iff_continuousAt.mpr
      intro t
      exact (hLan _ (hgammaOnCut v hvH ε hε.1 hε.2 t).1.1
        (hzero v hv.1 t)).continuousAt.comp hγsmooth.continuous.continuousAt
    exact ⟨hclosure, fun t => ((hγsmooth.differentiable (by norm_num)) t).hasDerivAt,
      (hLcont.mul hγsmooth.continuous_deriv_one).intervalIntegrable
        (cutStart v) (cutEnd v)⟩
  have hcutCircleCoverage : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ∀ v ∈ B,
        closure (Ω ε) ∩ Metric.sphere (cutCenter v ε) (cutRadius v ε) =
          γ v ε '' Set.Icc (cutEnd v) (cutStart v) := by
    filter_upwards [hsmallCuts, hcutArcs] with ε hε harcs
    intro v hv
    have hvH := hKH hv.1.1
    apply Set.Subset.antisymm
    · intro z hz
      have hzK := hcutClosureK ε hz.1
      obtain ⟨s, hs0, hsπ, hsz⟩ := hcutCircleRepresentation v hvH ε hε.1 hε.2 z hz.2
      have hends : γ v ε (-Real.pi) = γ v ε Real.pi := by
        simp [γ, neg_mul, Complex.exp_neg, Complex.exp_pi_mul_I]
      obtain ⟨t, ht0, htπ, htz, hleftπ, hright0⟩ :
          ∃ t : ℝ, -Real.pi ≤ t ∧ t ≤ Real.pi ∧ γ v ε t = z ∧
            (v.re = -1 / 2 → t < Real.pi) ∧
            (v.re = 1 / 2 → -Real.pi < t) := by
        by_cases he : v.re = -1 / 2 ∧ s = Real.pi
        · refine ⟨-Real.pi, le_rfl, by linarith [Real.pi_pos], ?_, ?_, ?_⟩
          · rw [hends, ← he.2, hsz]
          · intro _
            linarith [Real.pi_pos]
          · intro hright
            linarith [he.1]
        · refine ⟨s, hs0.le, hsπ, hsz, ?_, fun _ => hs0⟩
          intro hleft
          exact lt_of_le_of_ne hsπ (fun hs => he ⟨hleft, hs⟩)
      have hleft : v.re = -1 / 2 → t ≤ 0 := by
        intro hvL
        by_contra! htpos
        have hsin := Real.sin_pos_of_pos_of_lt_pi htpos (hleftπ hvL)
        have hlt := (hgammaSides v hvH ε hε.1 hε.2 t).1.mpr hsin
        rw [htz, hvL] at hlt
        have hlow := (abs_le.mp hzK.1).1
        linarith
      have hright : v.re = 1 / 2 → 0 ≤ t := by
        intro hvR
        by_contra! htneg
        have hsin := Real.sin_neg_of_neg_of_neg_pi_lt htneg (hright0 hvR)
        have hlt := (hgammaSides v hvH ε hε.1 hε.2 t).2.1.mpr hsin
        rw [htz, hvR] at hlt
        have hhigh := (abs_le.mp hzK.1).2
        linarith
      have hunit : ‖v‖ = 1 → v.arg - Real.pi ≤ t ∧ t ≤ v.arg := by
        intro hvN
        have hvim : 0 < v.im := hvH
        have harg0 : 0 < v.arg := by
          apply lt_of_le_of_ne (Complex.arg_nonneg_iff.mpr hvim.le)
          intro heq
          have him := Complex.norm_mul_sin_arg v
          rw [← heq, Real.sin_zero, mul_zero] at him
          linarith
        have hargπ : v.arg < Real.pi := Complex.arg_lt_pi_iff.mpr (Or.inr hvim.ne')
        have hcross : 0 ≤ v.im * Real.cos t - v.re * Real.sin t := by
          rcases eq_or_lt_of_le hzK.2.1 with heq | hlt
          · exact ((hgammaUnitCircle v hvH hvN ε hε.1 hε.2 t).2.mp
              (htz ▸ heq.symm)).ge
          · exact ((hgammaUnitCircle v hvH hvN ε hε.1 hε.2 t).1.mp
              (htz ▸ hlt)).le
        have hvre : v.re = Real.cos v.arg := by
          simpa only [hvN, one_mul] using (Complex.norm_mul_cos_arg v).symm
        have hvim' : v.im = Real.sin v.arg := by
          simpa only [hvN, one_mul] using (Complex.norm_mul_sin_arg v).symm
        rw [hvre, hvim', ← Real.sin_sub] at hcross
        have hupper : t ≤ v.arg := by
          by_contra! hn
          have hsneg := Real.sin_neg_of_neg_of_neg_pi_lt
            (by linarith : v.arg - t < 0) (by linarith : -Real.pi < v.arg - t)
          linarith
        have hlower : v.arg - Real.pi ≤ t := by
          by_contra! hn
          have hp : 0 < Real.sin (v.arg - t - Real.pi) :=
            Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
          rw [Real.sin_sub_pi] at hp
          linarith
        exact ⟨hlower, hupper⟩
      refine ⟨t, ⟨?_, ?_⟩, htz⟩
      · dsimp only [cutEnd]
        split_ifs with hvR hvN
        · exact hright hvR
        · exact (hunit hvN).1
        · exact ht0
      · dsimp only [cutStart]
        split_ifs with hvL hvN
        · exact hleft hvL
        · exact (hunit hvN).2
        · exact htπ
    · rintro z ⟨t, ht, rfl⟩
      exact ⟨frontier_subset_closure ((harcs v hv).1 ht),
        hgammaSphere v hvH ε hε.1 hε.2 t⟩
  have hparametrizedCutFrontier : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      frontier (Ω ε) =
        (⋃ i : Fin 4, closure (Ω ε) ∩ outerSupport i) ∪
          ⋃ v ∈ B, γ v ε '' Set.Icc (cutEnd v) (cutStart v) := by
    filter_upwards [hsmallCuts, hcutCircleCoverage] with ε hε hcoverage
    rw [hcutFrontier ε hε.1 hε.2]
    ext z
    constructor
    · intro hz
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
      rcases i with i | v
      · exact Or.inl (Set.mem_iUnion.mpr ⟨i, hi⟩)
      · exact Or.inr (Set.mem_iUnion₂.mpr ⟨v, v.property, (hcoverage v v.property) ▸ hi⟩)
    · rintro (hz | hz)
      · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
        exact Set.mem_iUnion.mpr ⟨Sum.inl i, hi⟩
      · obtain ⟨v, hv, hzv⟩ := Set.mem_iUnion₂.mp hz
        exact Set.mem_iUnion.mpr ⟨Sum.inr ⟨v, hv⟩, (hcoverage v hv).symm ▸ hzv⟩
  have hparametrizedExcisionBoundary :=
    (hsmallCuts.and (hparametrizedCutFrontier.and hfixedExcisionBoundary)).mono
      (fun ε h => by
        simpa only [← hcutFrontier ε h.1.1 h.1.2, h.2.1] using h.2.2)
  let indent : ℂ → (ℝ → ℝ) → (ℝ → ℝ) → ℝ → ℂ := fun v α β ε =>
    intervalIntegral (fun t : ℝ => L (γ v ε t) * deriv (γ v ε) t)
      (α ε) (β ε) MeasureTheory.volume
  have hindent : ∀ v ∈ H, ∀ (α β : ℝ → ℝ) (a b : ℝ),
      Filter.Tendsto α (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds a) →
      Filter.Tendsto β (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds b) →
      Filter.Tendsto (indent v α β) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (Complex.I * (analyticOrderNatAt F v : ℂ) * ((b - a : ℝ) : ℂ))) := by
    intro v hv α β a b hα hβ
    exact p10_17ae7b7d_valence_indentation_limit F v hv (hFan v hv)
      (hFfinite v hv) α β a b hα hβ
  have hclockwise : ∀ v ∈ H, ∀ (α β : ℝ → ℝ) (a θ : ℝ),
      Filter.Tendsto α (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds a) →
      Filter.Tendsto β (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (a - θ)) →
      Filter.Tendsto (indent v α β) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (-Complex.I * (analyticOrderNatAt F v : ℂ) * (θ : ℂ))) := by
    intro v hv α β a θ hα hβ
    convert hindent v hv α β a (a - θ) hα hβ using 1
    congr 1
    push_cast
    ring
  have hcutArcLimits : ∀ v ∈ B,
      Filter.Tendsto (indent v (fun _ => cutStart v) (fun _ => cutEnd v))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (-Complex.I * (analyticOrderNatAt F v : ℂ) *
          ((cutStart v - cutEnd v : ℝ) : ℂ))) := by
    intro v hv
    apply hclockwise v (hKH hv.1.1) (fun _ => cutStart v) (fun _ => cutEnd v)
      (cutStart v) (cutStart v - cutEnd v) tendsto_const_nhds
    simpa only [sub_sub_cancel] using
      (tendsto_const_nhds : Filter.Tendsto (fun _ : ℝ => cutEnd v)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (cutEnd v)))
  -- The three elliptic indentations contribute exactly the two weighted orders.
  have hellipticIndentationLimit :
      Filter.Tendsto (fun ε : ℝ =>
        indent Complex.I (fun _ => cutStart Complex.I) (fun _ => cutEnd Complex.I) ε +
        indent ρ (fun _ => cutStart ρ) (fun _ => cutEnd ρ) ε +
        indent (ρ + 1) (fun _ => cutStart (ρ + 1)) (fun _ => cutEnd (ρ + 1)) ε)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (-(2 * (Real.pi : ℂ) * Complex.I) *
          ((analyticOrderNatAt F Complex.I : ℂ) / 2 + (analyticOrderNatAt F ρ : ℂ) / 3))) := by
    have hi := hindent Complex.I hI (fun _ => cutStart Complex.I)
      (fun _ => cutEnd Complex.I) (cutStart Complex.I) (cutEnd Complex.I)
      tendsto_const_nhds tendsto_const_nhds
    have hl := hindent ρ hρH (fun _ => cutStart ρ) (fun _ => cutEnd ρ)
      (cutStart ρ) (cutEnd ρ) tendsto_const_nhds tendsto_const_nhds
    have hr := hindent (ρ + 1) hρOneH (fun _ => cutStart (ρ + 1))
      (fun _ => cutEnd (ρ + 1)) (cutStart (ρ + 1)) (cutEnd (ρ + 1))
      tendsto_const_nhds tendsto_const_nhds
    have heq :
        Complex.I * (analyticOrderNatAt F Complex.I : ℂ) *
            ((cutEnd Complex.I - cutStart Complex.I : ℝ) : ℂ) +
          Complex.I * (analyticOrderNatAt F ρ : ℂ) * ((cutEnd ρ - cutStart ρ : ℝ) : ℂ) +
          Complex.I * (analyticOrderNatAt F (ρ + 1) : ℂ) *
            ((cutEnd (ρ + 1) - cutStart (ρ + 1) : ℝ) : ℂ) =
        -(2 * (Real.pi : ℂ) * Complex.I) *
          ((analyticOrderNatAt F Complex.I : ℂ) / 2 + (analyticOrderNatAt F ρ : ℂ) / 3) := by
      rw [hcutEllipticAngles.1, hcutEllipticAngles.2.1, hcutEllipticAngles.2.2.1,
        hcutEllipticAngles.2.2.2.1, hcutEllipticAngles.2.2.2.2.1,
        hcutEllipticAngles.2.2.2.2.2, hρT]
      push_cast
      ring
    simpa only [heq] using (hi.add hl).add hr
  let boundaryWeight : ℂ → ℝ := fun v =>
    (analyticOrderNatAt F v : ℝ) * (cutStart v - cutEnd v) / (2 * Real.pi)
  have hboundaryWeightNonneg : ∀ v ∈ H, 0 ≤ boundaryWeight v := by
    intro v hv
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _)
      (sub_nonneg.mpr (hcutAngles v hv).2.1.le)) (by positivity)
  have hboundaryWeightZero : ∀ v ∈ K, v ∉ O → v ∉ B → boundaryWeight v = 0 := by
    intro v hv hvO hvB
    have horder : analyticOrderNatAt F v = 0 := by
      by_contra hn
      exact hvB ⟨⟨hv, apply_eq_zero_of_analyticOrderNatAt_ne_zero hn⟩, hvO⟩
    simp only [boundaryWeight, horder, Nat.cast_zero, zero_mul, zero_div]
  have hellipticBoundary : ∀ v ∈ ({Complex.I, ρ, ρ + 1} : Finset ℂ), v ∈ K ∧ v ∉ O := by
    have hrY : Real.sqrt 3 / 2 < Y := by
      have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
      have hp := Real.sqrt_nonneg 3
      nlinarith [hY]
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl
    · refine ⟨⟨?_, ?_, hI, hY.le⟩, ?_⟩
      · norm_num
      · simp
      · intro hO
        simpa only [Complex.norm_I, lt_self_iff_false] using hO.2.1
    · refine ⟨⟨?_, hρnorm.ge, hρH, ?_⟩, ?_⟩
      · norm_num [hρre]
      · simpa only [hρim] using hrY.le
      · intro hO
        exact (lt_irrefl (1 : ℝ)) (hρnorm ▸ hO.2.1)
    · refine ⟨⟨?_, hρOneNorm.ge, hρOneH, ?_⟩, ?_⟩
      · norm_num [Complex.add_re, hρre]
      · simpa only [Complex.add_im, Complex.one_im, add_zero, hρim] using hrY.le
      · intro hO
        exact (lt_irrefl (1 : ℝ)) (hρOneNorm ▸ hO.2.1)
  have hellipticWeight :
      boundaryWeight Complex.I = (analyticOrderNatAt F Complex.I : ℝ) / 2 ∧
      boundaryWeight ρ = (analyticOrderNatAt F ρ : ℝ) / 6 ∧
      boundaryWeight (ρ + 1) = (analyticOrderNatAt F ρ : ℝ) / 6 := by
    dsimp only [boundaryWeight]
    rw [hcutEllipticAngles.1, hcutEllipticAngles.2.1,
      hcutEllipticAngles.2.2.1, hcutEllipticAngles.2.2.2.1,
      hcutEllipticAngles.2.2.2.2.1, hcutEllipticAngles.2.2.2.2.2, hρT]
    constructor
    · field_simp
      ring
    constructor <;> field_simp <;> ring
  have hboundaryWeightBound :
      (analyticOrderNatAt F Complex.I : ℝ) / 2 + (analyticOrderNatAt F ρ : ℝ) / 3 ≤
        ∑ v ∈ hBfinite.toFinset, boundaryWeight v := by
    let E : Finset ℂ := {Complex.I, ρ, ρ + 1}
    have hIρ : Complex.I ≠ ρ := by
      intro heq
      have hre := congrArg Complex.re heq
      rw [Complex.I_re, hρre] at hre
      norm_num at hre
    have hIρOne : Complex.I ≠ ρ + 1 := by
      intro heq
      have hre := congrArg Complex.re heq
      rw [Complex.I_re, Complex.add_re, hρre, Complex.one_re] at hre
      norm_num at hre
    have hρρOne : ρ ≠ ρ + 1 := by
      intro heq
      have hre := congrArg Complex.re heq
      simp only [Complex.add_re, Complex.one_re] at hre
      linarith
    have hEsum : ∑ v ∈ E, boundaryWeight v =
        (analyticOrderNatAt F Complex.I : ℝ) / 2 + (analyticOrderNatAt F ρ : ℝ) / 3 := by
      simp only [E, Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton,
        hIρ, hIρOne, hρρOne, or_self, not_false_eq_true, Finset.sum_singleton,
        hellipticWeight.1, hellipticWeight.2.1, hellipticWeight.2.2]
      ring
    have hext : ∑ v ∈ hBfinite.toFinset, boundaryWeight v =
        ∑ v ∈ hBfinite.toFinset ∪ E, boundaryWeight v := by
      apply Finset.sum_subset Finset.subset_union_left
      intro v hv hvB
      have hvE : v ∈ E := (Finset.mem_union.mp hv).resolve_left hvB
      exact hboundaryWeightZero v (hellipticBoundary v hvE).1
        (hellipticBoundary v hvE).2 (by simpa only [Set.Finite.mem_toFinset] using hvB)
    rw [← hEsum, hext]
    apply Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_right
    intro v hv hvE
    have hvB := (Finset.mem_union.mp hv).resolve_right hvE
    exact hboundaryWeightNonneg v (hKH (hBfinite.mem_toFinset.mp hvB).1.1)
  have hboundaryRemainder : ∃ R : ℝ, 0 ≤ R ∧
      ∑ v ∈ hBfinite.toFinset, boundaryWeight v =
        (analyticOrderNatAt F Complex.I : ℝ) / 2 + (analyticOrderNatAt F ρ : ℝ) / 3 + R := by
    refine ⟨(∑ v ∈ hBfinite.toFinset, boundaryWeight v) -
      ((analyticOrderNatAt F Complex.I : ℝ) / 2 + (analyticOrderNatAt F ρ : ℝ) / 3),
      sub_nonneg.mpr hboundaryWeightBound, ?_⟩
    ring
  have hboundaryIndentationLimit :
      Filter.Tendsto (fun ε : ℝ => ∑ v ∈ hBfinite.toFinset,
        indent v (fun _ => cutStart v) (fun _ => cutEnd v) ε)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (-(2 * (Real.pi : ℂ) * Complex.I) *
          ((∑ v ∈ hBfinite.toFinset, boundaryWeight v : ℝ) : ℂ))) := by
    have hlim := tendsto_finsetSum hBfinite.toFinset
      (fun v hv => hcutArcLimits v (hBfinite.mem_toFinset.mp hv))
    have heach : ∀ v : ℂ,
        -Complex.I * (analyticOrderNatAt F v : ℂ) *
          ((cutStart v - cutEnd v : ℝ) : ℂ) =
        -(2 * (Real.pi : ℂ) * Complex.I) * (boundaryWeight v : ℂ) := by
      intro v
      dsimp only [boundaryWeight]
      push_cast
      field_simp
    simp_rw [heach] at hlim
    simpa only [Finset.mul_sum, Complex.ofReal_sum] using hlim
  -- Steps 17–18: the contour identity leaves only nonnegative zero orders.
  have hOzerosFinite : {z ∈ O | F z = 0}.Finite :=
    hKzeros.subset (fun _ hz => ⟨hOK hz.1, hz.2⟩)
  suffices hcount :
      (analyticOrderNatAt A 0 : ℝ) + (∑ v ∈ hBfinite.toFinset, boundaryWeight v) +
        (∑ v ∈ hOzerosFinite.toFinset, (analyticOrderNatAt F v : ℝ)) = (k : ℝ) / 12 by
    have hnonneg : 0 ≤ ∑ v ∈ hOzerosFinite.toFinset, (analyticOrderNatAt F v : ℝ) :=
      Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
    change (analyticOrderNatAt A 0 : ℝ) + (analyticOrderNatAt F Complex.I : ℝ) / 2 +
      (analyticOrderNatAt F ρ : ℝ) / 3 ≤ (k : ℝ) / 12
    linarith [hboundaryWeightBound]
  suffices hcontour : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      pairedLower ε + verticalContribution ε + top Y +
        (∑ v ∈ hBfinite.toFinset, indent v (fun _ => cutStart v) (fun _ => cutEnd v) ε) =
      2 * (Real.pi : ℂ) * Complex.I *
        ((∑ v ∈ hOzerosFinite.toFinset, (analyticOrderNatAt F v : ℝ) : ℝ) : ℂ) by
    have hverticalLimit : Filter.Tendsto verticalContribution
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) :=
      tendsto_const_nhds.congr' (hretainedVertical.mono (fun _ h => h.symm))
    have hlim := ((hpairedLowerLimit.add hverticalLimit).add_const (top Y)).add
      hboundaryIndentationLimit
    have hconstant : Filter.Tendsto (fun ε =>
        pairedLower ε + verticalContribution ε + top Y +
          ∑ v ∈ hBfinite.toFinset, indent v (fun _ => cutStart v) (fun _ => cutEnd v) ε)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (2 * (Real.pi : ℂ) * Complex.I *
          ((∑ v ∈ hOzerosFinite.toFinset, (analyticOrderNatAt F v : ℝ) : ℝ) : ℂ))) :=
      tendsto_const_nhds.congr' (hcontour.mono (fun _ h => h.symm))
    have heq := tendsto_nhds_unique hlim hconstant
    rw [add_zero, htopExact] at heq
    dsimp only [cInf] at heq
    have hprod : (2 * (Real.pi : ℂ) * Complex.I) *
        ((k : ℂ) / 12 - (analyticOrderNatAt A 0 : ℂ) -
          ((∑ v ∈ hBfinite.toFinset, boundaryWeight v : ℝ) : ℂ)) =
        (2 * (Real.pi : ℂ) * Complex.I) *
          ((∑ v ∈ hOzerosFinite.toFinset, (analyticOrderNatAt F v : ℝ) : ℝ) : ℂ) := by
      linear_combination heq
    have hne : 2 * (Real.pi : ℂ) * Complex.I ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num)
        (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
    have hz := mul_left_cancel₀ hne hprod
    have hresult : (analyticOrderNatAt A 0 : ℂ) +
        ((∑ v ∈ hBfinite.toFinset, boundaryWeight v : ℝ) : ℂ) +
        ((∑ v ∈ hOzerosFinite.toFinset, (analyticOrderNatAt F v : ℝ) : ℝ) : ℂ) =
        (k : ℂ) / 12 := by
      linear_combination -hz
    apply Complex.ofReal_injective
    push_cast at hresult ⊢
    exact hresult
  filter_upwards [hcutZeros, hparametrizedExcisionBoundary] with ε hzeros hexc
  obtain ⟨r, δ, hr, hδ, hVopen, hVcompact, hVzeroFree, hVfrontier,
    hcircles, hmesh, hcells⟩ := hexc
  have hexcisionSum :
      (∑ v ∈ hOzerosFinite.toFinset,
        intervalIntegral (fun t => L (circleMap v r t) * deriv (circleMap v r) t)
          (2 * Real.pi) 0 MeasureTheory.volume) =
      -(2 * (Real.pi : ℂ) * Complex.I *
        ((∑ v ∈ hOzerosFinite.toFinset, (analyticOrderNatAt F v : ℝ) : ℝ) : ℂ)) := by
    calc
      _ = ∑ v ∈ hOzerosFinite.toFinset,
          -(2 * (Real.pi : ℂ) * Complex.I * (analyticOrderNatAt F v : ℂ)) := by
        apply Finset.sum_congr rfl
        intro v hv
        have hvzero : v ∈ {z ∈ Ω ε | F z = 0} := by
          rw [hzeros]
          exact hOzerosFinite.mem_toFinset.mp hv
        exact (hcircles v hvzero).2.2
      _ = _ := by
        push_cast
        simp only [Finset.mul_sum, Finset.sum_neg_distrib]
  suffices hclosedContour :
      pairedLower ε + verticalContribution ε + top Y +
        (∑ v ∈ hBfinite.toFinset, indent v (fun _ => cutStart v) (fun _ => cutEnd v) ε) +
        (∑ v ∈ hOzerosFinite.toFinset,
          intervalIntegral (fun t => L (circleMap v r t) * deriv (circleMap v r) t)
            (2 * Real.pi) 0 MeasureTheory.volume) = 0 by
    simpa only [hexcisionSum, add_neg_eq_zero] using hclosedContour
  /- Remaining formal obligation: construct directed cell boundaries for the
  zero-free excised domain and cancel their primitive integrals. hVfrontier now
  identifies the actual cut arcs and excision circles; hcircles supplies their
  clockwise residue integrals. The finite cover and primitive-cycle cancellation
  do not yet construct the directed cell boundaries needed for hclosedContour.
  No global contour equality is assumed. -/

end Submission
