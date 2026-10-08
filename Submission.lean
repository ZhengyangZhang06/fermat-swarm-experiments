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
