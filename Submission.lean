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


theorem Submission.p10_17ae7b7d_rd_coeff_support :
    ∀ (w : ℕ) (P : ℂ → ℂ) (p : FormalMultilinearSeries ℂ ℂ ℂ),
      0 < w → HasFPowerSeriesAt P p 0 →
      (∃ s : ℝ, 0 < s ∧ ∀ t : ℂ, ‖t‖ < s →
        P (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (w : ℂ)) * t) = P t) →
      ∀ n : ℕ, ¬ w ∣ n → p.coeff n = 0 := by
  intro w P p hw hp hrot n hn
  obtain ⟨s, hs, hrot⟩ := hrot
  let ζ : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (w : ℂ))
  let L : ℂ →L[ℂ] ℂ := ζ • ContinuousLinearMap.id ℂ ℂ
  have hpL : HasFPowerSeriesAt P p (L 0) := by simpa only [map_zero] using hp
  have heq : p.compContinuousLinearMap L = p := by
    apply hpL.compContinuousLinearMap.eq_formalMultilinearSeries_of_eventually hp
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hs] with t ht
    have ht' : ‖t‖ < s := by simpa only [Metric.mem_ball, dist_zero_right] using ht
    simpa [Function.comp_def, L, ζ, smul_eq_mul] using hrot t ht'
  have hcoeff : ζ ^ n * p.coeff n = p.coeff n := by
    have h := congrArg
      (fun q : FormalMultilinearSeries ℂ ℂ ℂ => q n (fun _ => (1 : ℂ))) heq
    rw [FormalMultilinearSeries.compContinuousLinearMap_apply] at h
    simpa [Function.comp_def, L, smul_eq_mul] using h
  have hroot : ζ ^ n ≠ 1 := by
    intro h
    have hexp : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) / (w : ℂ)) = 1 := by
      calc
        _ = Complex.exp ((n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I / (w : ℂ))) := by
          congr 1
          ring
        _ = ζ ^ n := Complex.exp_nat_mul _ _
        _ = 1 := h
    exact hn ((Complex.exp_two_pi_mul_I_mul_div_eq_one_iff (Nat.ne_of_gt hw)).mp hexp)
  have hzero : (ζ ^ n - 1) * p.coeff n = 0 := by
    rw [sub_mul, one_mul, hcoeff, sub_self]
  exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hroot)
theorem Submission.p10_17ae7b7d_fi_unit_iterate_formula :
    ∀ (p a : ℕ), Nat.Prime p → 1 ≤ a → ∀ z : ZMod (p ^ a), p ∣ z.val →
      let F : ZMod (p ^ a) → ZMod (p ^ a) := fun w => w * (1 + w)⁻¹
      ∀ n : ℕ, IsUnit (1 + (n : ZMod (p ^ a)) * z) ∧
        (F^[n]) z = z * (1 + (n : ZMod (p ^ a)) * z)⁻¹ := by
  intro p a hp ha z hz
  have : NeZero (p ^ a) := ⟨pow_ne_zero a hp.ne_zero⟩
  have hunit (n : ℕ) : IsUnit (1 + (n : ZMod (p ^ a)) * z) := by
    have hnot : ¬ p ∣ 1 + n * z.val := by
      intro h
      apply hp.not_dvd_one
      simpa using Nat.dvd_sub h (dvd_mul_of_dvd_right hz n)
    have h := (ZMod.isUnit_natCast_iff_not_dvd_pow hp (show 0 < a from ha)).mpr hnot
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_mul, ZMod.natCast_zmod_val] using h
  dsimp only
  intro n
  refine ⟨hunit n, ?_⟩
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    let D : ZMod (p ^ a) := 1 + (n : ZMod (p ^ a)) * z
    let E : ZMod (p ^ a) := 1 + ((n + 1 : ℕ) : ZMod (p ^ a)) * z
    have hE : E = D + z := by
      dsimp [D, E]
      push_cast
      ring
    have hstep : 1 + z * D⁻¹ = E * D⁻¹ := by
      calc
        1 + z * D⁻¹ = D * D⁻¹ + z * D⁻¹ := by
          rw [ZMod.mul_inv_of_unit D (hunit n)]
        _ = (D + z) * D⁻¹ := by ring
        _ = E * D⁻¹ := by rw [hE]
    have hinv : (1 + z * D⁻¹)⁻¹ = D * E⁻¹ := by
      apply ZMod.inv_eq_of_mul_eq_one
      rw [hstep]
      calc
        E * D⁻¹ * (D * E⁻¹) = (D⁻¹ * D) * (E * E⁻¹) := by ring
        _ = 1 := by
          rw [ZMod.inv_mul_of_unit D (hunit n),
            ZMod.mul_inv_of_unit E (hunit (n + 1)), one_mul]
    change z * D⁻¹ * (1 + z * D⁻¹)⁻¹ = z * E⁻¹
    rw [hinv]
    calc
      z * D⁻¹ * (D * E⁻¹) = z * (D⁻¹ * D) * E⁻¹ := by ring
      _ = z * E⁻¹ := by rw [ZMod.inv_mul_of_unit D (hunit n), mul_one]
theorem Submission.p10_17ae7b7d_ccf_prime_power :
    ∀ (p a : ℕ), Nat.Prime p →
      ModularCurve.cuspCount (p ^ a) =
        (Finset.range (a + 1)).sum (fun j => Nat.totient (p ^ min j (a - j))) := by
  intro p a hp
  unfold ModularCurve.cuspCount
  rw [Nat.sum_divisors_prime_pow hp]
  apply Finset.sum_congr rfl
  intro j hj
  have hja : j ≤ a := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  rw [Nat.pow_div hja hp.pos]
  congr 1
  rcases le_total j (a - j) with h | h
  · rw [min_eq_left h]
    exact Nat.gcd_eq_left (pow_dvd_pow p h)
  · rw [min_eq_right h]
    exact Nat.gcd_eq_right (pow_dvd_pow p h)

theorem Submission.p10_17ae7b7d_crcard_quot_eq_unit :
    ∀ (R : Type) [CommRing R],
      let U := {v : R × R // ∃ x y : R, x * v.1 + y * v.2 = 1}
      let rel : U → U → Prop := fun v w =>
        ∃ u : Rˣ, (u : R) * v.1.1 = w.1.1 ∧ (u : R) * v.1.2 = w.1.2
      ∀ v w : U, Quot.mk rel v = Quot.mk rel w ↔ rel v w := by
  intro R _ U rel v w
  have hequiv : Equivalence rel := by
    refine ⟨fun a => ⟨1, by simp, by simp⟩, ?_, ?_⟩
    · rintro a b ⟨u, h1, h2⟩
      exact ⟨u⁻¹, by rw [← h1, Units.inv_mul_cancel_left],
        by rw [← h2, Units.inv_mul_cancel_left]⟩
    · rintro a b c ⟨u, h1, h2⟩ ⟨t, h1', h2'⟩
      exact ⟨t * u, by rw [Units.val_mul, mul_assoc, h1, h1'],
        by rw [Units.val_mul, mul_assoc, h2, h2']⟩
  exact hequiv.quot_mk_eq_iff v w
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


theorem Submission.p10_17ae7b7d_uce_normalized_quot_eq_iff :
    ∀ (R : Type) [CommRing R],
      let U := {v : R × R // ∃ x y : R, x * v.1 + y * v.2 = 1}
      let rel : U → U → Prop := fun v w =>
        ∃ u : Rˣ, (u : R) * v.1.1 = w.1.1 ∧ (u : R) * v.1.2 = w.1.2
      ∀ v w : U,
        (v.1.1 = 1 ∨ (¬ IsUnit v.1.1 ∧ v.1.2 = 1)) →
        (w.1.1 = 1 ∨ (¬ IsUnit w.1.1 ∧ w.1.2 = 1)) →
        (Quot.mk rel v = Quot.mk rel w ↔ v = w) := by
  intro R _ U rel v w hv hw
  constructor
  · intro hq
    have heqv : Equivalence rel := by
      refine ⟨fun a => ⟨1, by simp, by simp⟩, ?_, ?_⟩
      · rintro a b ⟨u, h₁, h₂⟩
        exact ⟨u⁻¹, by rw [← h₁, Units.inv_mul_cancel_left],
          by rw [← h₂, Units.inv_mul_cancel_left]⟩
      · rintro a b c ⟨u, h₁, h₂⟩ ⟨t, h₁', h₂'⟩
        exact ⟨t * u, by rw [Units.val_mul, mul_assoc, h₁, h₁'],
          by rw [Units.val_mul, mul_assoc, h₂, h₂']⟩
    obtain ⟨u, h₁, h₂⟩ := heqv.eqvGen_iff.mp (Quot.eq.mp hq)
    have hu : (u : R) = 1 := by
      rcases hv with hv | ⟨hv, hv₂⟩ <;> rcases hw with hw | ⟨hw, hw₂⟩
      · simpa only [hv, hw, mul_one] using h₁
      · exact False.elim (hw ⟨u, by simpa only [hv, mul_one] using h₁⟩)
      · apply False.elim
        apply hv
        refine ⟨u⁻¹, ?_⟩
        calc
          (↑u⁻¹ : R) = ↑u⁻¹ * w.1.1 := by rw [hw, mul_one]
          _ = v.1.1 := by rw [← h₁, Units.inv_mul_cancel_left]
      · simpa only [hv₂, hw₂, mul_one] using h₂
    apply Subtype.ext
    apply Prod.ext
    · simpa only [hu, one_mul] using h₁
    · simpa only [hu, one_mul] using h₂
  · exact congrArg (Quot.mk rel)


theorem Submission.p10_17ae7b7d_pp_fractional_iterates :
    ∀ (p a j : ℕ), Nat.Prime p → 1 ≤ j → j < a → ∀ z : ZMod (p ^ a),
      p ^ j ∣ z.val → ¬ p ^ (j + 1) ∣ z.val →
      let F : ZMod (p ^ a) → ZMod (p ^ a) := fun w => w * (1 + w)⁻¹
      ∀ n : ℕ, IsUnit (1 + (n : ZMod (p ^ a)) * z) ∧
        (F^[n]) z = z * (1 + (n : ZMod (p ^ a)) * z)⁻¹ ∧
        ((F^[n]) z = z ↔ p ^ (a - 2 * j) ∣ n) ∧
        p ^ j ∣ ((F^[n]) z).val ∧ ¬ p ^ (j + 1) ∣ ((F^[n]) z).val := by
  intro p a j hp hj hja z hz hznext
  dsimp only
  intro n
  have hpz : p ∣ z.val := (dvd_pow_self p (by omega : j ≠ 0)).trans hz
  obtain ⟨hunit, hformula⟩ :=
    Submission.p10_17ae7b7d_fi_unit_iterate_formula p a hp (by omega) z hpz n
  have hinv : IsUnit ((1 + (n : ZMod (p ^ a)) * z)⁻¹) := by
    obtain ⟨u, hu⟩ := hunit
    rw [← hu, ZMod.inv_coe_unit]
    exact Units.isUnit _
  refine ⟨hunit, hformula, ?_, ?_, ?_⟩
  · rw [hformula, ← Submission.p10_17ae7b7d_fi_square_annihilation p a j hp hja z
      hz hznext n]
    constructor
    · intro h
      have hmul := congrArg (fun w : ZMod (p ^ a) =>
        w * (1 + (n : ZMod (p ^ a)) * z)) h
      have hdenom : z = z * (1 + (n : ZMod (p ^ a)) * z) := by
        simpa only [mul_assoc, ZMod.inv_mul_of_unit _ hunit, mul_one] using hmul
      calc
        (n : ZMod (p ^ a)) * z ^ 2 =
            z * (1 + (n : ZMod (p ^ a)) * z) - z := by ring
        _ = 0 := by rw [← hdenom, sub_self]
    · intro h
      have hdenom : z * (1 + (n : ZMod (p ^ a)) * z) = z := by
        calc
          z * (1 + (n : ZMod (p ^ a)) * z) = z + (n : ZMod (p ^ a)) * z ^ 2 := by
            ring
          _ = z := by rw [h, add_zero]
      calc
        z * (1 + (n : ZMod (p ^ a)) * z)⁻¹ =
            (z * (1 + (n : ZMod (p ^ a)) * z)) *
              (1 + (n : ZMod (p ^ a)) * z)⁻¹ := by rw [hdenom]
        _ = z := by rw [mul_assoc, ZMod.mul_inv_of_unit _ hunit, mul_one]
  · rw [hformula]
    exact (Submission.p10_17ae7b7d_fi_unit_mul_dvd_val (p ^ a) (p ^ j)
      (pow_pos hp.pos _) (pow_dvd_pow p hja.le) z _ hinv).mpr hz
  · rw [hformula]
    intro h
    exact hznext ((Submission.p10_17ae7b7d_fi_unit_mul_dvd_val (p ^ a) (p ^ (j + 1))
      (pow_pos hp.pos _) (pow_dvd_pow p hja) z _ hinv).mp h)
theorem Submission.p10_17ae7b7d_cpd_rotation_descent :
    ∀ (w : ℕ) (P : ℂ → ℂ), 0 < w → AnalyticAt ℂ P 0 →
      (∃ s : ℝ, 0 < s ∧ ∀ t : ℂ, ‖t‖ < s →
        P (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (w : ℂ)) * t) = P t) →
      ∃ C : ℂ → ℂ, AnalyticAt ℂ C 0 ∧
        ∃ r : ℝ, 0 < r ∧ ∀ t : ℂ, ‖t‖ < r → P t = C (t ^ w) := by
  intro w P hw hP hrotation
  obtain ⟨p, hp⟩ := hP
  exact Submission.p10_17ae7b7d_rd_sparse_series_descent w P p hw hp
    (Submission.p10_17ae7b7d_rd_coeff_support w P p hw hp hrotation)

theorem Submission.p10_17ae7b7d_crcard_gamma0_row_criterion :
    ∀ (N : ℕ) [NeZero N] (A B : Matrix.SpecialLinearGroup (Fin 2) ℤ),
      B * A⁻¹ ∈ CongruenceSubgroup.Gamma0 N ↔
        ∃ u : (ZMod N)ˣ,
          (u : ZMod N) * (A 1 0 : ZMod N) = (B 1 0 : ZMod N) ∧
          (u : ZMod N) * (A 1 1 : ZMod N) = (B 1 1 : ZMod N) := by
  intro N _ A B
  constructor
  · intro h
    let C := B * A⁻¹
    have hzero : (C 1 0 : ZMod N) = 0 := CongruenceSubgroup.Gamma0_mem.mp h
    have hdet : (C 0 0 : ZMod N) * (C 1 1 : ZMod N) -
        (C 0 1 : ZMod N) * (C 1 0 : ZMod N) = 1 := by
      have hc := C.det_coe
      rw [Matrix.det_fin_two] at hc
      simpa only [Int.cast_sub, Int.cast_mul, Int.cast_one] using
        congrArg (fun z : ℤ => (z : ZMod N)) hc
    rw [hzero, mul_zero, sub_zero] at hdet
    let u : (ZMod N)ˣ := ⟨(C 1 1 : ZMod N), (C 0 0 : ZMod N),
      by rw [mul_comm]; exact hdet, hdet⟩
    have hCA : C * A = B := by
      dsimp [C]
      rw [mul_assoc, inv_mul_cancel, mul_one]
    have hrow (j : Fin 2) :
        (C 1 1 : ZMod N) * (A 1 j : ZMod N) = (B 1 j : ZMod N) := by
      have hc := congrArg (fun D : Matrix.SpecialLinearGroup (Fin 2) ℤ =>
        (D 1 j : ZMod N)) hCA
      change (((C.1 * A.1) 1 j : ℤ) : ZMod N) = (B 1 j : ZMod N) at hc
      simp only [Matrix.mul_apply, Fin.sum_univ_two, Int.cast_add, Int.cast_mul] at hc
      change (C 1 0 : ZMod N) * (A 0 j : ZMod N) +
        (C 1 1 : ZMod N) * (A 1 j : ZMod N) = (B 1 j : ZMod N) at hc
      simpa only [hzero, zero_mul, zero_add] using hc
    exact ⟨u, hrow 0, hrow 1⟩
  · rintro ⟨u, hc, hd⟩
    apply CongruenceSubgroup.Gamma0_mem.mpr
    change (((B.1 * (A⁻¹).1) 1 0 : ℤ) : ZMod N) = 0
    rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    change ((B 1 0 * A 1 1 + B 1 1 * -(A 1 0) : ℤ) : ZMod N) = 0
    push_cast
    rw [← hc, ← hd]
    ring
theorem Submission.p10_17ae7b7d_ccm_translation_period :
    ∀ (N : ℕ) [NeZero N]
      (q : (Matrix.SpecialLinearGroup (Fin 2) ℤ) ⧸ CongruenceSubgroup.Gamma0 N),
      (ModularGroup.T ^ N) • q = q := by
  intro N _ q
  refine QuotientGroup.induction_on q ?_
  intro A
  rw [MulAction.Quotient.smul_mk, smul_eq_mul]
  apply Eq.symm
  apply QuotientGroup.eq.mpr
  apply CongruenceSubgroup.Gamma0_mem.mpr
  have hT : (ModularGroup.T ^ N).1 = !![1, (N : ℤ); 0, 1] := by
    simpa only [zpow_natCast] using ModularGroup.coe_T_zpow (N : ℤ)
  have hentry : (A⁻¹ * (ModularGroup.T ^ N * A)) 1 0 =
      -(N : ℤ) * (A 1 0) ^ 2 := by
    change ((A⁻¹).1 * ((ModularGroup.T ^ N).1 * A.1)) 1 0 = _
    rw [Matrix.SpecialLinearGroup.SL2_inv_expl, hT]
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    change -(A 1 0) * (1 * A 0 0 + (N : ℤ) * A 1 0) +
      A 0 0 * (0 * A 0 0 + 1 * A 1 0) = _
    ring
  rw [hentry]
  simp
theorem Submission.p10_17ae7b7d_ccm_coset_crt_equivariant :
    ∀ (m n : ℕ) [NeZero m] [NeZero n], Nat.Coprime m n →
      let G := Matrix.SpecialLinearGroup (Fin 2) ℤ
      let Q := fun k : ℕ => G ⧸ CongruenceSubgroup.Gamma0 k
      ∃ e : Q (m * n) ≃ (Q m × Q n),
        ∀ (g : G) (q : Q (m * n)), e (g • q) = g • e q := by
  intro m n _ _ hmn
  classical
  let G := Matrix.SpecialLinearGroup (Fin 2) ℤ
  let Q := fun k : ℕ => G ⧸ CongruenceSubgroup.Gamma0 k
  let E := ZMod.chineseRemainder hmn
  have hcast (z : ℤ) : E (z : ZMod (m * n)) = ((z : ZMod m), (z : ZMod n)) := by
    exact map_intCast E z
  have hmem (C : G) : C ∈ CongruenceSubgroup.Gamma0 (m * n) ↔
      C ∈ CongruenceSubgroup.Gamma0 m ∧ C ∈ CongruenceSubgroup.Gamma0 n := by
    change (C 1 0 : ZMod (m * n)) = 0 ↔
      (C 1 0 : ZMod m) = 0 ∧ (C 1 0 : ZMod n) = 0
    rw [← E.injective.eq_iff, hcast, map_zero]
    exact Prod.ext_iff
  let F : Q (m * n) → Q m × Q n := Quotient.lift
    (fun A : G => (QuotientGroup.mk A, QuotientGroup.mk A)) (by
      intro A B hAB
      have h := (hmem (A⁻¹ * B)).mp
        (QuotientGroup.eq.mp (Quotient.sound hAB))
      exact Prod.ext (QuotientGroup.eq.mpr h.1) (QuotientGroup.eq.mpr h.2))
  have hF (A : G) : F (QuotientGroup.mk A) =
      (QuotientGroup.mk A, QuotientGroup.mk A) := rfl
  have hinj : Function.Injective F := by
    intro a b hab
    induction a using QuotientGroup.induction_on with | H A =>
      induction b using QuotientGroup.induction_on with | H B =>
        apply QuotientGroup.eq.mpr
        apply (hmem (A⁻¹ * B)).mpr
        exact ⟨QuotientGroup.eq.mp (congrArg Prod.fst hab),
          QuotientGroup.eq.mp (congrArg Prod.snd hab)⟩
  have hdet (L : ℕ) (C : G) :
      -(C 0 1 : ZMod L) * (C 1 0 : ZMod L) +
        (C 0 0 : ZMod L) * (C 1 1 : ZMod L) = 1 := by
    have h := C.det_coe
    rw [Matrix.det_fin_two] at h
    have h' := congrArg (fun z : ℤ => (z : ZMod L)) h
    push_cast at h'
    linear_combination h'
  have hsurj : Function.Surjective F := by
    rintro ⟨a, b⟩
    induction a using QuotientGroup.induction_on with | H A =>
      induction b using QuotientGroup.induction_on with | H B =>
        let r := E.symm ((A⁻¹ 1 0 : ZMod m), (B⁻¹ 1 0 : ZMod n))
        let s := E.symm ((A⁻¹ 1 1 : ZMod m), (B⁻¹ 1 1 : ZMod n))
        let x := E.symm (-(A⁻¹ 0 1 : ZMod m), -(B⁻¹ 0 1 : ZMod n))
        let y := E.symm ((A⁻¹ 0 0 : ZMod m), (B⁻¹ 0 0 : ZMod n))
        have hrow : x * r + y * s = 1 := by
          apply E.injective
          dsimp only [x, r, y, s]
          simp only [map_add, map_mul, map_one, RingEquiv.apply_symm_apply]
          exact Prod.ext (hdet m A⁻¹) (hdet n B⁻¹)
        obtain ⟨M, hMr, hMs⟩ :=
          Submission.p10_17ae7b7d_cc_lift_unimodular_row (m * n) r s ⟨x, y, hrow⟩
        have hr : ((M 1 0 : ZMod m), (M 1 0 : ZMod n)) =
            ((A⁻¹ 1 0 : ZMod m), (B⁻¹ 1 0 : ZMod n)) := by
          rw [← hcast, hMr]
          exact E.apply_symm_apply _
        have hs : ((M 1 1 : ZMod m), (M 1 1 : ZMod n)) =
            ((A⁻¹ 1 1 : ZMod m), (B⁻¹ 1 1 : ZMod n)) := by
          rw [← hcast, hMs]
          exact E.apply_symm_apply _
        have hcoset (L : ℕ) (C : G)
            (hc : (M 1 0 : ZMod L) = (C⁻¹ 1 0 : ZMod L))
            (hd : (M 1 1 : ZMod L) = (C⁻¹ 1 1 : ZMod L)) :
            (QuotientGroup.mk M⁻¹ : Q L) = QuotientGroup.mk C := by
          apply QuotientGroup.eq.mpr
          rw [inv_inv]
          apply CongruenceSubgroup.Gamma0_mem.mpr
          have heq : ((M * C) 1 0 : ZMod L) = ((C⁻¹ * C) 1 0 : ZMod L) := by
            change (((M.1 * C.1) 1 0 : ℤ) : ZMod L) =
              ((((C⁻¹).1 * C.1) 1 0 : ℤ) : ZMod L)
            simp only [Matrix.mul_apply, Fin.sum_univ_two, Int.cast_add, Int.cast_mul]
            rw [hc, hd]
          rw [heq, inv_mul_cancel]
          simp
        refine ⟨QuotientGroup.mk M⁻¹, ?_⟩
        rw [hF]
        exact Prod.ext (hcoset m A (congrArg Prod.fst hr) (congrArg Prod.fst hs))
          (hcoset n B (congrArg Prod.snd hr) (congrArg Prod.snd hs))
  refine ⟨Equiv.ofBijective F ⟨hinj, hsurj⟩, ?_⟩
  intro g q
  induction q using QuotientGroup.induction_on with | H A =>
    rfl

theorem Submission.p10_17ae7b7d_uce_unimodular_iff_unit_coord :
    ∀ (p a : ℕ), p.Prime → 0 < a → ∀ r s : ZMod (p ^ a),
      (∃ x y : ZMod (p ^ a), x * r + y * s = 1) ↔ IsUnit r ∨ IsUnit s := by
  intro p a hp ha r s
  let : NeZero (p ^ a) := ⟨pow_ne_zero _ hp.ne_zero⟩
  let : Fact p.Prime := ⟨hp⟩
  constructor
  · rintro ⟨x, y, hxy⟩
    by_contra h
    obtain ⟨hr, hs⟩ := not_or.mp h
    let f : ZMod (p ^ a) →+* ZMod p := ZMod.castHom (dvd_pow_self p ha.ne') (ZMod p)
    have hzero : ∀ t : ZMod (p ^ a), ¬ IsUnit t → f t = 0 := by
      intro t ht
      have hd : p ∣ t.val := by
        by_contra hd
        apply ht
        simpa only [ZMod.natCast_zmod_val] using
          (ZMod.isUnit_natCast_iff_not_dvd_pow (a := t.val) hp ha).mpr hd
      rw [← ZMod.natCast_zmod_val t, map_natCast]
      exact (ZMod.natCast_eq_zero_iff t.val p).mpr hd
    have hz := congrArg f hxy
    simp only [map_add, map_mul, map_one, hzero r hr, hzero s hs,
      mul_zero, add_zero] at hz
    exact zero_ne_one hz
  · rintro (⟨u, rfl⟩ | ⟨u, rfl⟩)
    · exact ⟨↑(u⁻¹), 0, by simp⟩
    · exact ⟨0, ↑(u⁻¹), by simp⟩
theorem Submission.p10_17ae7b7d_ccf_coprime_mul :
    ∀ (m n : ℕ), Nat.Coprime m n →
      ModularCurve.cuspCount (m * n) = ModularCurve.cuspCount m * ModularCurve.cuspCount n := by
  intro m n hmn
  classical
  by_cases hm : m = 0
  · simp [hm, ModularCurve.cuspCount]
  by_cases hn : n = 0
  · simp [hn, ModularCurve.cuspCount]
  unfold ModularCurve.cuspCount
  rw [Nat.divisors_mul, Finset.mul_def, Finset.sum_image hmn.mul_injOn_divisors,
    Finset.sum_product, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  have ham : a ∣ m := Nat.dvd_of_mem_divisors ha
  have hbn : b ∣ n := Nat.dvd_of_mem_divisors hb
  have hAm : m / a ∣ m := Nat.div_dvd_of_dvd ham
  have hBn : n / b ∣ n := Nat.div_dvd_of_dvd hbn
  have hab : a.Coprime b := hmn.of_dvd ham hbn
  have haB : (n / b).Coprime a := (hmn.of_dvd ham hBn).symm
  have hAb : (m / a).Coprime b := hmn.of_dvd hAm hbn
  rw [Nat.mul_div_mul_comm ham hbn, hab.mul_gcd,
    haB.gcd_mul_right_cancel_right, hAb.gcd_mul_left_cancel_right]
  exact Nat.totient_mul (hmn.of_dvd
    ((Nat.gcd_dvd_left a (m / a)).trans ham)
    ((Nat.gcd_dvd_left b (n / b)).trans hbn))
theorem Submission.p10_17ae7b7d_ccm_coprime_orbit_product :
    ∀ (G X Y : Type) [Group G] [MulAction G X] [MulAction G Y]
      (g : G) (m n : ℕ) [NeZero m] [NeZero n], Nat.Coprime m n →
      (∀ x : X, (g ^ m) • x = x) → (∀ y : Y, (g ^ n) • y = y) →
      Nat.card (Quotient (MulAction.orbitRel (Subgroup.zpowers g) (X × Y))) =
        Nat.card (Quotient (MulAction.orbitRel (Subgroup.zpowers g) X)) *
          Nat.card (Quotient (MulAction.orbitRel (Subgroup.zpowers g) Y)) := by
  intro G X Y _ _ _ g m n _ _ hmn hX hY
  have hperiod : ∀ (Z : Type) [MulAction G Z] (d : ℕ),
      (∀ z : Z, (g ^ d) • z = z) → ∀ a b : ℤ,
      (d : ℤ) ∣ a - b → ∀ z : Z, (g ^ a) • z = (g ^ b) • z := by
    intro Z _ d hd a b ⟨k, hk⟩ z
    have ha : a = (d : ℤ) * k + b := by omega
    rw [ha, zpow_add, mul_smul, zpow_mul, zpow_natCast]
    exact MulAction.mem_fixedBy_zpow (hd ((g ^ b) • z)) k
  have hbez : (1 : ℤ) = (m : ℤ) * Nat.gcdA m n + (n : ℤ) * Nat.gcdB m n := by
    simpa only [hmn.gcd_eq_one, Nat.cast_one] using Nat.gcd_eq_gcd_ab m n
  have hrel : MulAction.orbitRel (Subgroup.zpowers g) (X × Y) =
      (MulAction.orbitRel (Subgroup.zpowers g) X).prod
        (MulAction.orbitRel (Subgroup.zpowers g) Y) := by
    apply Setoid.ext
    intro p q
    change (∃ h : Subgroup.zpowers g, h • q = p) ↔
      (∃ h : Subgroup.zpowers g, h • q.1 = p.1) ∧
        (∃ h : Subgroup.zpowers g, h • q.2 = p.2)
    constructor
    · rintro ⟨h, hh⟩
      exact ⟨⟨h, congrArg Prod.fst hh⟩, ⟨h, congrArg Prod.snd hh⟩⟩
    · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp a.property
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp b.property
      change (a : G) • q.1 = p.1 at ha
      change (b : G) • q.2 = p.2 at hb
      rw [← hi] at ha
      rw [← hj] at hb
      let t : ℤ := i * (n : ℤ) * Nat.gcdB m n + j * (m : ℤ) * Nat.gcdA m n
      have hti : (m : ℤ) ∣ t - i := by
        refine ⟨Nat.gcdA m n * (j - i), ?_⟩
        dsimp [t]
        linear_combination -i * hbez
      have htj : (n : ℤ) ∣ t - j := by
        refine ⟨Nat.gcdB m n * (i - j), ?_⟩
        dsimp [t]
        linear_combination -j * hbez
      refine ⟨⟨g ^ t, Subgroup.zpow_mem_zpowers g t⟩, ?_⟩
      apply Prod.ext
      · exact (hperiod X m hX t i hti q.1).trans ha
      · exact (hperiod Y n hY t j htj q.2).trans hb
  rw [hrel]
  exact (Nat.card_congr (Setoid.prodQuotientEquiv
    (MulAction.orbitRel (Subgroup.zpowers g) X)
    (MulAction.orbitRel (Subgroup.zpowers g) Y)).symm).trans (Nat.card_prod _ _)


theorem Submission.p10_17ae7b7d_ppr_unit_chart_equiv :
    ∀ (p a : ℕ), p.Prime → 0 < a →
      let R := ZMod (p ^ a)
      Nonempty ((Quot (fun v w :
        {v : R × R // ∃ x y : R, x * v.1 + y * v.2 = 1} =>
          ∃ u : Rˣ, (u : R) * v.1.1 = w.1.1 ∧ (u : R) * v.1.2 = w.1.2)) ≃
        (R ⊕ {z : R // ¬ IsUnit z})) := by
  classical
  intro p a hp ha
  let R := ZMod (p ^ a)
  let U := {v : R × R // ∃ x y : R, x * v.1 + y * v.2 = 1}
  let rel : U → U → Prop := fun v w =>
    ∃ u : Rˣ, (u : R) * v.1.1 = w.1.1 ∧ (u : R) * v.1.2 = w.1.2
  let chart : R ⊕ {z : R // ¬ IsUnit z} → U := Sum.elim
    (fun t => ⟨(1, t), 1, 0, by simp⟩)
    (fun z => ⟨(z.1, 1), 0, 1, by simp⟩)
  have hnormal : ∀ c, (chart c).1.1 = 1 ∨
      (¬ IsUnit (chart c).1.1 ∧ (chart c).1.2 = 1) := by
    intro c
    cases c with
    | inl t => exact Or.inl rfl
    | inr z => exact Or.inr ⟨z.2, rfl⟩
  have hchart : Function.Injective chart := by
    intro c d h
    cases c with
    | inl t =>
      cases d with
      | inl t' =>
        exact congrArg Sum.inl (congrArg (fun v : U => v.1.2) h)
      | inr z =>
        have hz : (1 : R) = z.1 := congrArg (fun v : U => v.1.1) h
        exact (z.2 (hz ▸ isUnit_one)).elim
    | inr z =>
      cases d with
      | inl t =>
        have hz : z.1 = (1 : R) := congrArg (fun v : U => v.1.1) h
        exact (z.2 (hz.symm ▸ isUnit_one)).elim
      | inr z' =>
        exact congrArg Sum.inr (Subtype.ext (congrArg (fun v : U => v.1.1) h))
  let F : R ⊕ {z : R // ¬ IsUnit z} → Quot rel := fun c => Quot.mk rel (chart c)
  have hinj : Function.Injective F := by
    intro c d h
    exact hchart ((Submission.p10_17ae7b7d_uce_normalized_quot_eq_iff R
      (chart c) (chart d) (hnormal c) (hnormal d)).mp h)
  have hsurj : Function.Surjective F := by
    intro q
    refine Quot.inductionOn q ?_
    intro v
    by_cases hr : IsUnit v.1.1
    · obtain ⟨u, hu⟩ := hr
      refine ⟨Sum.inl ((↑u⁻¹ : R) * v.1.2), Quot.sound ?_⟩
      change ∃ w : Rˣ, (w : R) * 1 = v.1.1 ∧
        (w : R) * ((↑u⁻¹ : R) * v.1.2) = v.1.2
      exact ⟨u, by simpa only [mul_one] using hu, u.mul_inv_cancel_left _⟩
    · have hs : IsUnit v.1.2 :=
        ((Submission.p10_17ae7b7d_uce_unimodular_iff_unit_coord p a hp ha
          v.1.1 v.1.2).mp v.2).resolve_left hr
      obtain ⟨u, hu⟩ := hs
      have hz : ¬ IsUnit ((↑u⁻¹ : R) * v.1.1) := fun h =>
        hr ((Units.isUnit_units_mul u⁻¹ v.1.1).mp h)
      refine ⟨Sum.inr ⟨(↑u⁻¹ : R) * v.1.1, hz⟩, Quot.sound ?_⟩
      change ∃ w : Rˣ, (w : R) * ((↑u⁻¹ : R) * v.1.1) = v.1.1 ∧
        (w : R) * 1 = v.1.2
      exact ⟨u, u.mul_inv_cancel_left _, by simpa only [mul_one] using hu⟩
  exact ⟨(Equiv.ofBijective F ⟨hinj, hsurj⟩).symm⟩


theorem Submission.p10_17ae7b7d_idx_coset_row_card :
    ∀ (N : ℕ) [NeZero N],
      (∀ r s : ZMod N, (∃ x y : ZMod N, x * r + y * s = 1) →
        ∃ A : Matrix.SpecialLinearGroup (Fin 2) ℤ,
          (A 1 0 : ZMod N) = r ∧ (A 1 1 : ZMod N) = s) →
      let P := Quot (fun v w :
        {v : ZMod N × ZMod N // ∃ x y : ZMod N, x * v.1 + y * v.2 = 1} =>
          ∃ u : (ZMod N)ˣ,
            (u : ZMod N) * v.1.1 = w.1.1 ∧ (u : ZMod N) * v.1.2 = w.1.2)
      let Q := (Matrix.SpecialLinearGroup (Fin 2) ℤ) ⧸ CongruenceSubgroup.Gamma0 N
      Finite Q ∧ Nat.card Q = Nat.card P := by
  intro N _ hlift
  classical
  let U := {v : ZMod N × ZMod N // ∃ x y : ZMod N, x * v.1 + y * v.2 = 1}
  let rel : U → U → Prop := fun v w => ∃ u : (ZMod N)ˣ,
    (u : ZMod N) * v.1.1 = w.1.1 ∧ (u : ZMod N) * v.1.2 = w.1.2
  let P := Quot rel
  let H := CongruenceSubgroup.Gamma0 N
  let Qr := Quotient (QuotientGroup.rightRel H)
  let row : Matrix.SpecialLinearGroup (Fin 2) ℤ → U := fun A =>
    ⟨((A 1 0 : ZMod N), (A 1 1 : ZMod N)),
      (A.isCoprime_row 1).map (Int.castRingHom (ZMod N))⟩
  -- Bottom rows classify right cosets; the child criterion proves well-definedness.
  let f : Qr → P := Quotient.lift (fun A => Quot.mk rel (row A)) (by
    intro A B hAB
    apply Quot.sound
    exact (Submission.p10_17ae7b7d_crcard_gamma0_row_criterion N A B).mp
      (QuotientGroup.rightRel_apply.mp hAB))
  have hinj : Function.Injective f := by
    intro a b
    refine Quotient.inductionOn₂ a b ?_
    intro A B hAB
    apply Quotient.sound
    apply QuotientGroup.rightRel_apply.mpr
    apply (Submission.p10_17ae7b7d_crcard_gamma0_row_criterion N A B).mpr
    exact (Submission.p10_17ae7b7d_crcard_quot_eq_unit (ZMod N) (row A) (row B)).mp hAB
  have hsurj : Function.Surjective f := by
    intro p
    refine Quot.inductionOn p ?_
    intro v
    obtain ⟨A, hAr, hAs⟩ := hlift v.1.1 v.1.2 v.2
    refine ⟨Quotient.mk _ A, ?_⟩
    change Quot.mk rel (row A) = Quot.mk rel v
    apply congrArg (Quot.mk rel)
    apply Subtype.ext
    exact Prod.ext hAr hAs
  -- Inversion identifies the right-coset quotient with the specified left quotient.
  let e : ((Matrix.SpecialLinearGroup (Fin 2) ℤ) ⧸ H) ≃ P :=
    (QuotientGroup.quotientRightRelEquivQuotientLeftRel H).symm.trans
      (Equiv.ofBijective f ⟨hinj, hsurj⟩)
  exact ⟨Finite.of_equiv P e.symm, Nat.card_congr e⟩
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


theorem Submission.p10_17ae7b7d_to_cusp_count_factorization :
    ∀ (N : ℕ) [NeZero N], ModularCurve.cuspCount N =
      N.primeFactors.prod (fun p =>
        (Finset.range (N.factorization p + 1)).sum (fun j =>
          Nat.totient (p ^ min j (N.factorization p - j)))) := by
  intro N _
  calc
    ModularCurve.cuspCount N =
        N.factorization.prod (fun p a => ModularCurve.cuspCount (p ^ a)) :=
      Nat.multiplicative_factorization ModularCurve.cuspCount
        Submission.p10_17ae7b7d_ccf_coprime_mul ModularCurve.cuspCount_one (NeZero.ne N)
    _ = N.primeFactors.prod (fun p => ModularCurve.cuspCount (p ^ N.factorization p)) :=
      Nat.prod_factorization_eq_prod_primeFactors _
    _ = _ := by
      apply Finset.prod_congr rfl
      intro p hp
      exact Submission.p10_17ae7b7d_ccf_prime_power p (N.factorization p)
        (Nat.prime_of_mem_primeFactors hp)
theorem Submission.p10_17ae7b7d_tchart_unique_row :
    ∀ (p a : ℕ), Nat.Prime p → 1 ≤ a →
      let R := ZMod (p ^ a)
      ∀ r s : R, (∃ x y : R, x * r + y * s = 1) →
        ∃! c : R ⊕ {z : R // p ∣ z.val},
          match c with
          | Sum.inl t => ∃ u : Rˣ, r = (u : R) ∧ s = (u : R) * t
          | Sum.inr z => ∃ u : Rˣ, r = (u : R) * z.1 ∧ s = (u : R) := by
  intro p a hp ha
  have : NeZero (p ^ a) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have : Fact p.Prime := ⟨hp⟩
  dsimp only
  intro r s ⟨x, y, hxy⟩
  let ρ : ZMod (p ^ a) →+* ZMod p :=
    ZMod.castHom (dvd_pow_self p (by omega)) (ZMod p)
  have hρ (z : ZMod (p ^ a)) : ρ z = 0 ↔ p ∣ z.val := by
    have heq : ρ z = (z.val : ZMod p) := by
      conv_lhs => rw [← ZMod.natCast_zmod_val z]
      exact map_natCast ρ z.val
    rw [heq, ZMod.natCast_eq_zero_iff]
  have hunit (z : ZMod (p ^ a)) : IsUnit z ↔ ¬ p ∣ z.val := by
    simpa only [ZMod.natCast_zmod_val] using
      (ZMod.isUnit_natCast_iff_not_dvd_pow (a := z.val) hp (by omega : 0 < a))
  by_cases hr : IsUnit r
  · obtain ⟨u, hu⟩ := hr
    refine ⟨Sum.inl ((↑u⁻¹ : ZMod (p ^ a)) * s), ⟨u, hu.symm, ?_⟩, ?_⟩
    · simp only [Units.mul_inv_cancel_left]
    · intro c hc
      cases c with
      | inl t =>
          obtain ⟨v, hv, hvt⟩ := hc
          apply congrArg Sum.inl
          have huv : (v : ZMod (p ^ a)) = u := hv.symm.trans hu.symm
          rw [huv] at hvt
          rw [hvt, Units.inv_mul_cancel_left]
      | inr z =>
          obtain ⟨v, hv, _⟩ := hc
          have hrzero : ρ r = 0 := by
            rw [hv, map_mul, (hρ z.1).mpr z.2, mul_zero]
          exact False.elim ((hunit r).mp ⟨u, hu⟩ ((hρ r).mp hrzero))
  · have hrzero : ρ r = 0 := (hρ r).mpr (by simpa only [hunit, not_not] using hr)
    have hs : IsUnit s := by
      by_contra hs
      have hszero : ρ s = 0 := (hρ s).mpr (by simpa only [hunit, not_not] using hs)
      have heq := congrArg ρ hxy
      simp only [map_add, map_mul, map_one, hrzero, hszero, mul_zero, add_zero] at heq
      exact zero_ne_one heq
    obtain ⟨u, hu⟩ := hs
    have hz : p ∣ ((↑u⁻¹ : ZMod (p ^ a)) * r).val := by
      apply (hρ _).mp
      rw [map_mul, hrzero, mul_zero]
    refine ⟨Sum.inr ⟨(↑u⁻¹ : ZMod (p ^ a)) * r, hz⟩,
      ⟨u, ?_, hu.symm⟩, ?_⟩
    · simp only [Units.mul_inv_cancel_left]
    · intro c hc
      cases c with
      | inl t =>
          obtain ⟨v, hv, _⟩ := hc
          exact False.elim (hr ⟨v, hv.symm⟩)
      | inr z =>
          obtain ⟨v, hvz, hv⟩ := hc
          apply congrArg Sum.inr
          apply Subtype.ext
          have huv : (v : ZMod (p ^ a)) = u := hv.symm.trans hu.symm
          rw [huv] at hvz
          change z.1 = (↑u⁻¹ : ZMod (p ^ a)) * r
          rw [hvz, Units.inv_mul_cancel_left]

theorem Submission.p10_17ae7b7d_idx_prime_power_row_card :
    ∀ (p a : ℕ), p.Prime → 0 < a →
      Nat.card (Quot (fun v w :
        {v : ZMod (p ^ a) × ZMod (p ^ a) //
          ∃ x y : ZMod (p ^ a), x * v.1 + y * v.2 = 1} =>
        ∃ u : (ZMod (p ^ a))ˣ,
          (u : ZMod (p ^ a)) * v.1.1 = w.1.1 ∧
          (u : ZMod (p ^ a)) * v.1.2 = w.1.2)) = p ^ a + p ^ (a - 1) := by
  intro p a hp ha
  have : NeZero (p ^ a) := ⟨pow_ne_zero a hp.ne_zero⟩
  obtain ⟨e⟩ := Submission.p10_17ae7b7d_ppr_unit_chart_equiv p a hp ha
  rw [Nat.card_congr e, Nat.card_sum, Nat.card_zmod,
    Submission.p10_17ae7b7d_ppr_nonunit_card p a hp ha]


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


theorem Submission.p10_17ae7b7d_to_coprime_count_mul :
    ∀ (m n : ℕ) [NeZero m] [NeZero n], Nat.Coprime m n →
      Nat.card (Quotient (MulAction.orbitRel (Subgroup.zpowers ModularGroup.T)
        ((Matrix.SpecialLinearGroup (Fin 2) ℤ) ⧸ CongruenceSubgroup.Gamma0 (m * n)))) =
      Nat.card (Quotient (MulAction.orbitRel (Subgroup.zpowers ModularGroup.T)
        ((Matrix.SpecialLinearGroup (Fin 2) ℤ) ⧸ CongruenceSubgroup.Gamma0 m))) *
      Nat.card (Quotient (MulAction.orbitRel (Subgroup.zpowers ModularGroup.T)
        ((Matrix.SpecialLinearGroup (Fin 2) ℤ) ⧸ CongruenceSubgroup.Gamma0 n))) := by
  intro m n _ _ hmn
  let G := Matrix.SpecialLinearGroup (Fin 2) ℤ
  let Q := fun k : ℕ => G ⧸ CongruenceSubgroup.Gamma0 k
  let H := Subgroup.zpowers ModularGroup.T
  obtain ⟨e, he⟩ := Submission.p10_17ae7b7d_ccm_coset_crt_equivariant m n hmn
  have horbit : ∀ a b : Q (m * n),
      MulAction.orbitRel H (Q (m * n)) a b ↔
        MulAction.orbitRel H (Q m × Q n) (e a) (e b) := by
    intro a b
    simp only [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨g, hg⟩
      exact ⟨g, (he (g : G) b).symm.trans (congrArg e hg)⟩
    · rintro ⟨g, hg⟩
      exact ⟨g, e.injective ((he (g : G) b).trans hg)⟩
  calc
    _ = Nat.card (Quotient (MulAction.orbitRel H (Q m × Q n))) :=
      Nat.card_congr (Quotient.congr e horbit)
    _ = _ := Submission.p10_17ae7b7d_ccm_coprime_orbit_product
      G (Q m) (Q n) ModularGroup.T m n hmn
      (Submission.p10_17ae7b7d_ccm_translation_period m)
      (Submission.p10_17ae7b7d_ccm_translation_period n)

/-- Prime-power cosets in the two normalized bottom-row charts. -/
theorem Submission.p10_17ae7b7d_pp_translation_charts :
    ∀ (p a : ℕ), Nat.Prime p → 1 ≤ a →
      let R := ZMod (p ^ a)
      let Q := (Matrix.SpecialLinearGroup (Fin 2) ℤ) ⧸ CongruenceSubgroup.Gamma0 (p ^ a)
      ∃ e : Q ≃ (R ⊕ {z : R // p ∣ z.val}),
        (∀ t : R, e (ModularGroup.T⁻¹ • e.symm (Sum.inl t)) = Sum.inl (t + 1)) ∧
        (∀ z : {z : R // p ∣ z.val}, ∃ w : {z : R // p ∣ z.val},
          e (ModularGroup.T⁻¹ • e.symm (Sum.inr z)) = Sum.inr w ∧
            w.1 = z.1 * (1 + z.1)⁻¹) := by
  classical
  intro p a hp ha
  have : NeZero (p ^ a) := ⟨pow_ne_zero _ hp.ne_zero⟩
  let R := ZMod (p ^ a)
  let Q := (Matrix.SpecialLinearGroup (Fin 2) ℤ) ⧸ CongruenceSubgroup.Gamma0 (p ^ a)
  let C := R ⊕ {z : R // p ∣ z.val}
  let x : C → R := fun c => match c with
    | Sum.inl _ => 1
    | Sum.inr z => z.1
  let y : C → R := fun c => match c with
    | Sum.inl t => t
    | Sum.inr _ => 1
  -- The child supplies uniqueness of the parameter of every matrix row.
  have hnorm (A : Matrix.SpecialLinearGroup (Fin 2) ℤ) : ∃! c : C, ∃ u : Rˣ,
      (A 1 0 : R) = (u : R) * x c ∧ (A 1 1 : R) = (u : R) * y c := by
    have hdet : (A 0 0 : R) * (A 1 1 : R) -
        (A 0 1 : R) * (A 1 0 : R) = 1 := by
      change (A 0 0 : ZMod (p ^ a)) * (A 1 1 : ZMod (p ^ a)) -
        (A 0 1 : ZMod (p ^ a)) * (A 1 0 : ZMod (p ^ a)) = 1
      have h := A.det_coe
      rw [Matrix.det_fin_two] at h
      simpa only [Int.cast_sub, Int.cast_mul, Int.cast_one] using
        congrArg (fun z : ℤ => (z : ZMod (p ^ a))) h
    have hrow : ∃ r s : R, r * (A 1 0 : R) + s * (A 1 1 : R) = 1 :=
      ⟨-(A 0 1 : R), (A 0 0 : R), by linear_combination hdet⟩
    have h := Submission.p10_17ae7b7d_tchart_unique_row p a hp ha
      (A 1 0 : R) (A 1 1 : R) hrow
    change ∃! c : C, _ at h
    convert h using 1
    ext c
    cases c <;> simp only [x, y, mul_one] <;> rfl
  -- Choose a lift of each normalized row, and use its inverse coset.
  have hlift (c : C) : ∃ A : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      (A 1 0 : R) = x c ∧ (A 1 1 : R) = y c := by
    apply Submission.p10_17ae7b7d_cc_lift_unimodular_row
    cases c with
    | inl t => exact ⟨1, 0, by simp [x, y]⟩
    | inr z => exact ⟨0, 1, by simp [x, y]⟩
  let L : C → Matrix.SpecialLinearGroup (Fin 2) ℤ := fun c => (hlift c).choose
  have hL (c : C) : (L c 1 0 : R) = x c ∧ (L c 1 1 : R) = y c :=
    (hlift c).choose_spec
  let g : C → Q := fun c => QuotientGroup.mk (L c)⁻¹
  have hclass (A : Matrix.SpecialLinearGroup (Fin 2) ℤ) (c : C)
      (hc : ∃ u : Rˣ, (A 1 0 : R) = (u : R) * x c ∧
        (A 1 1 : R) = (u : R) * y c) : (QuotientGroup.mk A⁻¹ : Q) = g c := by
    apply Eq.symm
    apply (Submission.p10_17ae7b7d_efp_inverse_coset_eq_iff (p ^ a) (L c) A).mpr
    simpa only [(hL c).1, (hL c).2] using hc
  have hinj : Function.Injective g := by
    intro c d hcd
    obtain ⟨u, hu, hv⟩ :=
      (Submission.p10_17ae7b7d_efp_inverse_coset_eq_iff (p ^ a) (L c) (L d)).mp hcd
    apply (hnorm (L d)).unique
    · exact ⟨u, by simpa only [(hL c).1] using hu,
        by simpa only [(hL c).2] using hv⟩
    · exact ⟨1, by simpa using (hL d).1, by simpa using (hL d).2⟩
  have hsurj : Function.Surjective g := by
    intro q
    refine Quotient.inductionOn q ?_
    intro A
    obtain ⟨c, hc, _⟩ := hnorm A⁻¹
    refine ⟨c, ?_⟩
    simpa only [inv_inv] using (hclass A⁻¹ c hc).symm
  let e : Q ≃ C := (Equiv.ofBijective g ⟨hinj, hsurj⟩).symm
  -- Left translation of an inverse coset is right translation of its row.
  have haction (c : C) : ModularGroup.T⁻¹ • g c =
      (QuotientGroup.mk (L c * ModularGroup.T)⁻¹ : Q) := by
    change QuotientGroup.mk (ModularGroup.T⁻¹ * (L c)⁻¹) = _
    rw [mul_inv_rev]
  have hrowT (A : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
      ((A * ModularGroup.T) 1 0 : R) = (A 1 0 : R) ∧
      ((A * ModularGroup.T) 1 1 : R) = (A 1 0 : R) + (A 1 1 : R) := by
    change (((A.1 * ModularGroup.T.1) 1 0 : ℤ) : R) = _ ∧
      (((A.1 * ModularGroup.T.1) 1 1 : ℤ) : R) = _
    simp [ModularGroup.coe_T, Matrix.mul_apply, Fin.sum_univ_two]
  refine ⟨e, ?_, ?_⟩
  · intro t
    apply e.symm.injective
    rw [e.symm_apply_apply]
    change ModularGroup.T⁻¹ • g (Sum.inl t) = g (Sum.inl (t + 1))
    refine (haction (Sum.inl t)).trans
      (hclass (L (Sum.inl t) * ModularGroup.T) (Sum.inl (t + 1)) ?_)
    refine ⟨1, ?_, ?_⟩
    · simp only [(hrowT (L (Sum.inl t))).1, (hL (Sum.inl t)).1, x,
        Units.val_one, one_mul]
    · simp only [(hrowT (L (Sum.inl t))).2, (hL (Sum.inl t)).1,
        (hL (Sum.inl t)).2, x, y, Units.val_one, one_mul]
      exact add_comm 1 t
  · intro z
    obtain ⟨c, ⟨u, hu, hv⟩, _⟩ := hnorm (L (Sum.inr z) * ModularGroup.T)
    rw [(hrowT (L (Sum.inr z))).1, (hL (Sum.inr z)).1] at hu
    rw [(hrowT (L (Sum.inr z))).2, (hL (Sum.inr z)).1, (hL (Sum.inr z)).2] at hv
    cases c with
    | inl t =>
        have hz : IsUnit z.1 := by
          have heq : z.1 = (u : R) := by simpa only [x, mul_one] using hu
          rw [heq]
          exact u.isUnit
        have hnot : ¬ p ∣ z.1.val := by
          apply (ZMod.isUnit_natCast_iff_not_dvd_pow hp (by omega : 0 < a)).mp
          simpa only [ZMod.natCast_zmod_val] using hz
        exact (hnot z.2).elim
    | inr w =>
        refine ⟨w, ?_, ?_⟩
        · apply e.symm.injective
          rw [e.symm_apply_apply]
          change ModularGroup.T⁻¹ • g (Sum.inr z) = g (Sum.inr w)
          refine (haction (Sum.inr z)).trans
            (hclass (L (Sum.inr z) * ModularGroup.T) (Sum.inr w) ?_)
          refine ⟨u, ?_, ?_⟩
          · simpa only [(hrowT (L (Sum.inr z))).1, (hL (Sum.inr z)).1] using hu
          · simpa only [(hrowT (L (Sum.inr z))).2, (hL (Sum.inr z)).1,
              (hL (Sum.inr z)).2] using hv
        · have hu' : z.1 = (u : R) * w.1 := hu
          have hv' : 1 + z.1 = (u : R) := by
            simpa only [x, y, mul_one, add_comm] using hv
          rw [hv', hu', ZMod.inv_coe_unit]
          calc
            w.1 = w.1 * (u : R) * (↑(u⁻¹) : R) :=
              (Units.mul_inv_cancel_right w.1 u).symm
            _ = ((u : R) * w.1) * (↑(u⁻¹) : R) := by rw [mul_comm w.1 (u : R)]
theorem Submission.p10_17ae7b7d_cc_index :
    ∀ (N : ℕ) [NeZero N],
      let Q := (Matrix.SpecialLinearGroup (Fin 2) ℤ) ⧸ CongruenceSubgroup.Gamma0 N
      Finite Q ∧ Nat.card Q = ModularCurve.dedekindPsi N := by
  intro N _
  obtain ⟨hfinite, hcard⟩ := Submission.p10_17ae7b7d_idx_coset_row_card N
    (Submission.p10_17ae7b7d_cc_lift_unimodular_row N)
  refine ⟨hfinite, ?_⟩
  rw [hcard, Submission.p10_17ae7b7d_idx_crt_row_card N,
    Submission.p10_17ae7b7d_idx_dedekind_psi_product N]
  apply Finset.prod_congr rfl
  intro p hp
  have hpPrime := Nat.prime_of_mem_primeFactors hp
  exact Submission.p10_17ae7b7d_idx_prime_power_row_card p (N.factorization p) hpPrime
    (hpPrime.factorization_pos_of_dvd (NeZero.ne N) (Nat.dvd_of_mem_primeFactors hp))
namespace Submission

open Filter
open scoped Topology

theorem p10_17ae7b7d_norm_cyclic_product_descent :
    ∀ (w : ℕ) (A : ℂ → ℂ), 0 < w → AnalyticAt ℂ A 0 →
      analyticOrderAt A 0 ≠ ⊤ →
      ∃ C : ℂ → ℂ, AnalyticAt ℂ C 0 ∧ analyticOrderAt C 0 ≠ ⊤ ∧
        analyticOrderNatAt C 0 = analyticOrderNatAt A 0 ∧
        ∃ r : ℝ, 0 < r ∧ ∀ t : ℂ, ‖t‖ < r →
          (∏ j ∈ Finset.range w,
            A (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (w : ℂ)) ^ j * t)) =
              C (t ^ w) := by
  intro w A hw hA hAfinite
  let ζ : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (w : ℂ))
  have hζ : ζ ^ w = 1 := by
    dsimp [ζ]
    rw [← Complex.exp_nat_mul]
    have hexp := (Complex.exp_two_pi_mul_I_mul_div_eq_one_iff
      (Nat.ne_of_gt hw)).2 (dvd_refl w)
    convert hexp using 1
    congr 1
    ring
  let P : ℂ → ℂ := fun t => ∏ j ∈ Finset.range w, A (ζ ^ j * t)
  obtain ⟨hP, hPfinite, hPorder, hProt⟩ :=
    Submission.p10_17ae7b7d_cpd_orbit_product_order w ζ A hw hζ hA hAfinite
  obtain ⟨C, hC, r, hr, hPC⟩ :=
    Submission.p10_17ae7b7d_cpd_rotation_descent w P hw hP
      ⟨1, zero_lt_one, fun t _ => hProt t⟩
  have hPCevent : P =ᶠ[𝓝 (0 : ℂ)] (fun t => C (t ^ w)) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hr] with t ht
    exact hPC t (by simpa using ht)
  -- Composition with the power map multiplies the descended order by w.
  have hzero : (0 : ℂ) ^ w = 0 := zero_pow (Nat.ne_of_gt hw)
  have hpow : AnalyticAt ℂ (fun t : ℂ => t ^ w) 0 := analyticAt_id.pow w
  have hpoworder : analyticOrderAt (fun t : ℂ => t ^ w) 0 = (w : ℕ∞) := by
    have hfun : ((fun t : ℂ => t - 0) ^ w) = (fun t : ℂ => t ^ w) := by
      funext t
      simp
    rw [← hfun]
    exact analyticOrderAt_centeredMonomial
  have hCpow : AnalyticAt ℂ C ((0 : ℂ) ^ w) := by
    simpa only [hzero] using hC
  have horder : analyticOrderAt P 0 = analyticOrderAt C 0 * (w : ℕ∞) := by
    calc
      analyticOrderAt P 0 = analyticOrderAt (C ∘ fun t : ℂ => t ^ w) 0 :=
        analyticOrderAt_congr hPCevent
      _ = analyticOrderAt C 0 * (w : ℕ∞) := by
        simpa only [hzero, sub_zero, hpoworder] using
          (hCpow.analyticOrderAt_comp (g := fun t : ℂ => t ^ w) hpow)
  have hCfinite : analyticOrderAt C 0 ≠ ⊤ := by
    intro htop
    apply hPfinite
    rw [horder, htop]
    exact ENat.top_mul (by exact_mod_cast Nat.ne_of_gt hw)
  have hNatorder : analyticOrderNatAt P 0 = analyticOrderNatAt C 0 * w := by
    simpa only [analyticOrderNatAt, ENat.toNat_mul, ENat.toNat_natCast] using
      congrArg ENat.toNat horder
  refine ⟨C, hC, hCfinite, ?_, r, hr, hPC⟩
  apply Nat.eq_of_mul_eq_mul_left hw
  calc
    w * analyticOrderNatAt C 0 = analyticOrderNatAt P 0 := by
      rw [hNatorder, Nat.mul_comm]
    _ = w * analyticOrderNatAt A 0 := hPorder

end Submission
/-- Prime-power translation-orbit count, assembled from the two chart interfaces. -/
theorem Submission.p10_17ae7b7d_to_prime_power_count :
    ∀ (p a : ℕ), Nat.Prime p → 1 ≤ a →
      Nat.card (Quotient (MulAction.orbitRel (Subgroup.zpowers ModularGroup.T)
        ((Matrix.SpecialLinearGroup (Fin 2) ℤ) ⧸ CongruenceSubgroup.Gamma0 (p ^ a)))) =
      (Finset.range (a + 1)).sum (fun j => Nat.totient (p ^ min j (a - j))) := by
  classical
  intro p a hp ha
  let R := ZMod (p ^ a)
  let Q := (Matrix.SpecialLinearGroup (Fin 2) ℤ) ⧸ CongruenceSubgroup.Gamma0 (p ^ a)
  let H := Subgroup.zpowers ModularGroup.T
  let O := Quotient (MulAction.orbitRel H Q)
  let : NeZero (p ^ a) := ⟨pow_ne_zero _ hp.ne_zero⟩
  obtain ⟨e, heL, heR⟩ := Submission.p10_17ae7b7d_pp_translation_charts p a hp ha
  let : Fintype Q := Fintype.ofEquiv (R ⊕ {z : R // p ∣ z.val}) e.symm
  let : Fintype O := Fintype.ofFinite O
  let f : Q → Q := fun q => ModularGroup.T⁻¹ • q
  let W : Q → ℚ := fun q => (Nat.card (MulAction.orbit H q) : ℚ)⁻¹
  have hcard (q : Q) : Nat.card (MulAction.orbit H q) = Function.minimalPeriod f q := by
    change Nat.card (MulAction.orbit (Subgroup.zpowers ModularGroup.T) q) = _
    calc
      _ = Nat.card (ZMod (Function.minimalPeriod (fun r : Q => ModularGroup.T • r) q)) :=
        Nat.card_congr (MulAction.orbitZPowersEquiv ModularGroup.T q)
      _ = Function.minimalPeriod (fun r : Q => ModularGroup.T • r) q := Nat.card_zmod _
      _ = Function.minimalPeriod f q := (MulAction.period_inv ModularGroup.T q).symm
  -- Summing reciprocal orbit sizes counts each orbit once.
  have hcount : (Nat.card O : ℚ) = ∑ q : Q, W q := by
    rw [← Fintype.sum_fiberwise (fun q : Q => (Quotient.mk'' q : O)) W]
    calc
      (Nat.card O : ℚ) = ∑ _o : O, (1 : ℚ) := by simp [Nat.card_eq_fintype_card]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro o _
        refine Quotient.inductionOn o ?_
        intro q
        let E : {r : Q // (Quotient.mk'' r : O) = Quotient.mk'' q} ≃
            MulAction.orbit H q :=
          Equiv.subtypeEquivRight (fun r => Quotient.eq'')
        have hw (r : {r : Q // (Quotient.mk'' r : O) = Quotient.mk'' q}) : W r = W q := by
          have horb : MulAction.orbit H r.val = MulAction.orbit H q :=
            MulAction.orbit_eq_iff.mpr (Quotient.exact r.property)
          simp only [W, horb]
        simp_rw [hw]
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          Fintype.card_congr E, ← Nat.card_eq_fintype_card]
        have hn : Nat.card (MulAction.orbit H q) ≠ 0 := by
          let : Nonempty (MulAction.orbit H q) := ⟨⟨q, MulAction.mem_orbit_self q⟩⟩
          exact Nat.card_pos.ne'
        exact (mul_inv_cancel₀ (by exact_mod_cast hn)).symm
  have hperiod (q : Q) (L : ℕ) (h : ∀ n : ℕ, (f^[n]) q = q ↔ L ∣ n) :
      Function.minimalPeriod f q = L := by
    apply Nat.dvd_antisymm
    · exact Function.isPeriodicPt_iff_minimalPeriod_dvd.mp ((h L).mpr (dvd_refl L))
    · exact (h _).mp (Function.iterate_minimalPeriod (f := f) (x := q))
  have hstepL (t : R) : f (e.symm (Sum.inl t)) = e.symm (Sum.inl (t + 1)) := by
    apply e.injective
    simpa only [Equiv.apply_symm_apply] using heL t
  have hiterL (n : ℕ) (t : R) :
      (f^[n]) (e.symm (Sum.inl t)) = e.symm (Sum.inl (t + (n : R))) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply', ih, hstepL]
      simp only [Nat.cast_add, Nat.cast_one, add_assoc]
  have hWL (t : R) : W (e.symm (Sum.inl t)) = (p ^ a : ℚ)⁻¹ := by
    have hper : Function.minimalPeriod f (e.symm (Sum.inl t)) = p ^ a := by
      apply hperiod
      intro n
      rw [hiterL, e.symm.injective.eq_iff, Sum.inl.injEq]
      simpa only [add_eq_left] using (ZMod.natCast_eq_zero_iff n (p ^ a))
    simp only [W, hcard, hper, Nat.cast_pow]
  let F : R → R := fun z => z * (1 + z)⁻¹
  have hiterR (n : ℕ) (z : {z : R // p ∣ z.val}) :
      ∃ w : {z : R // p ∣ z.val},
        (f^[n]) (e.symm (Sum.inr z)) = e.symm (Sum.inr w) ∧
          w.val = (F^[n]) z.val := by
    induction n with
    | zero => exact ⟨z, rfl, rfl⟩
    | succ n ih =>
      obtain ⟨w, hw, hwv⟩ := ih
      obtain ⟨v, hv, hvv⟩ := heR w
      refine ⟨v, ?_, ?_⟩
      · rw [Function.iterate_succ_apply', hw]
        exact e.injective (hv.trans (e.apply_symm_apply _).symm)
      · rw [Function.iterate_succ_apply', ← hwv]
        exact hvv
  have hreturnR (n : ℕ) (z : {z : R // p ∣ z.val}) :
      (f^[n]) (e.symm (Sum.inr z)) = e.symm (Sum.inr z) ↔ (F^[n]) z.val = z.val := by
    obtain ⟨w, hw, hwv⟩ := hiterR n z
    rw [hw, e.symm.injective.eq_iff, Sum.inr.injEq, Subtype.ext_iff, hwv]
  let z0 : {z : R // p ∣ z.val} := ⟨0, by simp⟩
  have hW0 : W (e.symm (Sum.inr z0)) = 1 := by
    have hfix : f (e.symm (Sum.inr z0)) = e.symm (Sum.inr z0) := by
      exact (hreturnR 1 z0).mpr (by simp [F, z0])
    have hper := Function.minimalPeriod_eq_one_iff_isFixedPt.mpr hfix
    simp only [W, hcard, hper, Nat.cast_one, inv_one]
  have hWR (j : ℕ) (hj : 1 ≤ j) (hja : j < a)
      (z : {z : R // p ∣ z.val})
      (hz : p ^ j ∣ z.val.val ∧ ¬ p ^ (j + 1) ∣ z.val.val) :
      W (e.symm (Sum.inr z)) = (p ^ (a - 2 * j) : ℚ)⁻¹ := by
    have hper : Function.minimalPeriod f (e.symm (Sum.inr z)) = p ^ (a - 2 * j) := by
      apply hperiod
      intro n
      rw [hreturnR]
      exact (Submission.p10_17ae7b7d_pp_fractional_iterates p a j hp hj hja
        z.val hz.1 hz.2 n).2.2.1
    simp only [W, hcard, hper, Nat.cast_pow]
  -- A nonzero point in the second chart belongs to exactly one interior stratum.
  have hvaluation (z : {z : R // p ∣ z.val}) (hz : z ≠ z0) :
      ∃! j : ℕ, 1 ≤ j ∧ j < a ∧ p ^ j ∣ z.val.val ∧ ¬ p ^ (j + 1) ∣ z.val.val := by
    have hn : z.val.val ≠ 0 := by
      intro h
      apply hz
      apply Subtype.ext
      simpa only [h, Nat.cast_zero] using (ZMod.natCast_zmod_val z.val).symm
    let j := z.val.val.factorization p
    have hj : 1 ≤ j := (hp.dvd_iff_one_le_factorization hn).mp z.property
    have hja : j < a := by
      by_contra h
      have hd := (hp.pow_dvd_iff_le_factorization hn).mpr (Nat.le_of_not_gt h)
      exact (not_le_of_gt (ZMod.val_lt z.val)) (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hd)
    refine ⟨j, ⟨hj, hja, (hp.pow_dvd_iff_le_factorization hn).mpr le_rfl, ?_⟩, ?_⟩
    · rw [hp.pow_dvd_iff_le_factorization hn]
      omega
    · intro k hk
      have hk₁ := (hp.pow_dvd_iff_le_factorization hn).mp hk.2.2.1
      have hk₂ : ¬ k + 1 ≤ j := by
        intro h
        exact hk.2.2.2 ((hp.pow_dvd_iff_le_factorization hn).mpr h)
      omega
  have hstratum (j : ℕ) (hj : j ∈ Finset.Ico 1 a) :
      (∑ z : {z : R // p ∣ z.val},
        if p ^ j ∣ z.val.val ∧ ¬ p ^ (j + 1) ∣ z.val.val
        then W (e.symm (Sum.inr z)) else 0) = (Nat.totient (p ^ min j (a - j)) : ℚ) := by
    obtain ⟨hj, hja⟩ := Finset.mem_Ico.mp hj
    let S := {z : R // p ^ j ∣ z.val ∧ ¬ p ^ (j + 1) ∣ z.val}
    let E : {z : {z : R // p ∣ z.val} //
        p ^ j ∣ z.val.val ∧ ¬ p ^ (j + 1) ∣ z.val.val} ≃ S :=
      { toFun := fun z => ⟨z.val.val, z.property⟩
        invFun := fun z => ⟨⟨z.val, dvd_trans (by simpa using pow_dvd_pow p hj) z.property.1⟩,
          z.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [← Finset.sum_filter, Finset.sum_subtype _
      (p := fun z : {z : R // p ∣ z.val} =>
        p ^ j ∣ z.val.val ∧ ¬ p ^ (j + 1) ∣ z.val.val) (by simp)]
    have hw (z : {z : {z : R // p ∣ z.val} //
        p ^ j ∣ z.val.val ∧ ¬ p ^ (j + 1) ∣ z.val.val}) :
        W (e.symm (Sum.inr z.val)) = (p ^ (a - 2 * j) : ℚ)⁻¹ :=
      hWR j hj hja z.val z.property
    simp_rw [hw]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_congr E,
      ← Nat.card_eq_fintype_card]
    have hS := Submission.p10_17ae7b7d_pp_stratum_card p a j hp hj hja
    change Nat.card S = _ at hS
    rw [hS, Nat.cast_mul, Nat.cast_pow, mul_assoc, mul_inv_cancel₀, mul_one]
    exact pow_ne_zero _ (by exact_mod_cast hp.ne_zero)
  have hsumR : (∑ z : {z : R // p ∣ z.val}, W (e.symm (Sum.inr z))) =
      1 + ∑ j ∈ Finset.Ico 1 a, (Nat.totient (p ^ min j (a - j)) : ℚ) := by
    have hpoint (z : {z : R // p ∣ z.val}) :
        W (e.symm (Sum.inr z)) = (if z = z0 then 1 else 0) +
          ∑ j ∈ Finset.Ico 1 a,
            if p ^ j ∣ z.val.val ∧ ¬ p ^ (j + 1) ∣ z.val.val
            then W (e.symm (Sum.inr z)) else 0 := by
      by_cases hz : z = z0
      · subst z
        simp [z0, hW0]
      · obtain ⟨j, hj, hu⟩ := hvaluation z hz
        rw [if_neg hz, zero_add]
        symm
        rw [Finset.sum_eq_single j]
        · simp [hj.2.2]
        · intro k hk hkj
          rw [if_neg]
          intro h
          exact hkj (hu k ⟨(Finset.mem_Ico.mp hk).1, (Finset.mem_Ico.mp hk).2, h⟩)
        · intro hjnot
          exact (hjnot (Finset.mem_Ico.mpr ⟨hj.1, hj.2.1⟩)).elim
    calc
      _ = ∑ z : {z : R // p ∣ z.val}, ((if z = z0 then (1 : ℚ) else 0) +
          ∑ j ∈ Finset.Ico 1 a,
            if p ^ j ∣ z.val.val ∧ ¬ p ^ (j + 1) ∣ z.val.val
            then W (e.symm (Sum.inr z)) else 0) :=
        Finset.sum_congr rfl (fun z _ => hpoint z)
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_comm]
        apply congrArg₂ (fun x y : ℚ => x + y)
        · exact Fintype.sum_ite_eq' z0 (fun _ => (1 : ℚ))
        · exact Finset.sum_congr rfl hstratum
  have htotal : (Nat.card O : ℚ) =
      1 + (1 + ∑ j ∈ Finset.Ico 1 a, (Nat.totient (p ^ min j (a - j)) : ℚ)) := by
    rw [hcount, ← e.symm.sum_comp W, Fintype.sum_sum_type]
    simp_rw [hWL]
    rw [hsumR]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ZMod.card]
    rw [Nat.cast_pow, mul_inv_cancel₀]
    exact pow_ne_zero _ (by exact_mod_cast hp.ne_zero)
  have hsumN : (Finset.range (a + 1)).sum (fun j => Nat.totient (p ^ min j (a - j))) =
      1 + (1 + ∑ j ∈ Finset.Ico 1 a, Nat.totient (p ^ min j (a - j))) := by
    rw [Finset.sum_range_succ, Finset.range_eq_Ico,
      Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < a)]
    simp only [Nat.zero_min, pow_zero, Nat.totient_one, Nat.sub_self, Nat.min_zero, Nat.zero_add]
    omega
  change Nat.card O = _
  rw [hsumN]
  exact_mod_cast htotal

theorem Submission.p10_17ae7b7d_cc_translation_orbits :
    ∀ (N : ℕ) [NeZero N],
      let Q := (Matrix.SpecialLinearGroup (Fin 2) ℤ) ⧸ CongruenceSubgroup.Gamma0 N
      Nat.card (Quotient (MulAction.orbitRel (Subgroup.zpowers ModularGroup.T) Q)) =
        ModularCurve.cuspCount N := by
  intro N _
  classical
  let count := fun n : ℕ =>
    Nat.card (Quotient (MulAction.orbitRel (Subgroup.zpowers ModularGroup.T)
      ((Matrix.SpecialLinearGroup (Fin 2) ℤ) ⧸ CongruenceSubgroup.Gamma0 n)))
  -- The empty prime-power product has a single coset and hence a single orbit.
  have hOne : count 1 = 1 := by
    have hGamma : CongruenceSubgroup.Gamma0 1 = ⊤ := by
      ext A
      simp only [CongruenceSubgroup.Gamma0_mem, Subgroup.mem_top, iff_true]
      exact Subsingleton.elim _ _
    dsimp [count]
    rw [hGamma]
    have : Subsingleton ((Matrix.SpecialLinearGroup (Fin 2) ℤ) ⧸
        (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))) :=
      QuotientGroup.subsingleton_quotient_top
    exact Nat.card_unique
  -- Assemble the local counts over any subset of the prime factors of N.
  have hProduct : ∀ s : Finset ℕ, s ⊆ N.primeFactors →
      count (s.prod (fun p => p ^ N.factorization p)) =
        s.prod (fun p => (Finset.range (N.factorization p + 1)).sum
          (fun j => Nat.totient (p ^ min j (N.factorization p - j)))) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        intro _
        simpa only [Finset.prod_empty] using hOne
    | @insert p s hp ih =>
        intro hs
        have hpN : p ∈ N.primeFactors := hs (Finset.mem_insert_self p s)
        have hsN : s ⊆ N.primeFactors := fun q hq => hs (Finset.mem_insert_of_mem hq)
        have hPrime : p.Prime := Nat.prime_of_mem_primeFactors hpN
        have hExponent : 1 ≤ N.factorization p :=
          hPrime.factorization_pos_of_dvd (NeZero.ne N)
            (Nat.dvd_of_mem_primeFactors hpN)
        have : NeZero (p ^ N.factorization p) := ⟨pow_ne_zero _ hPrime.ne_zero⟩
        have : NeZero (s.prod (fun q => q ^ N.factorization q)) :=
          ⟨Finset.prod_ne_zero_iff.mpr (fun q hq =>
            pow_ne_zero _ (Nat.prime_of_mem_primeFactors (hsN hq)).ne_zero)⟩
        have hCoprime : Nat.Coprime (p ^ N.factorization p)
            (s.prod (fun q => q ^ N.factorization q)) := by
          apply Nat.coprime_prod_right_iff.mpr
          intro q hq
          apply Nat.Coprime.pow
          apply (Nat.coprime_primes hPrime (Nat.prime_of_mem_primeFactors (hsN hq))).mpr
          intro hpq
          exact hp (hpq.symm ▸ hq)
        rw [Finset.prod_insert hp, Finset.prod_insert hp]
        calc
          count (p ^ N.factorization p * s.prod (fun q => q ^ N.factorization q)) =
              count (p ^ N.factorization p) *
                count (s.prod (fun q => q ^ N.factorization q)) :=
            Submission.p10_17ae7b7d_to_coprime_count_mul _ _ hCoprime
          _ = _ := congrArg₂ Nat.mul
            (Submission.p10_17ae7b7d_to_prime_power_count p (N.factorization p)
              hPrime hExponent) (ih hsN)
  change count N = ModularCurve.cuspCount N
  rw [Submission.p10_17ae7b7d_to_cusp_count_factorization N]
  calc
    count N = count (N.primeFactors.prod (fun p => p ^ N.factorization p)) :=
      congrArg count (Nat.prod_primeFactors_pow_factorization (NeZero.ne N))
    _ = _ := hProduct N.primeFactors (Finset.Subset.refl _)


theorem Submission.p10_17ae7b7d_gamma0_coset_counts :
    ∀ (N : ℕ) [NeZero N],
      let Q := (Matrix.SpecialLinearGroup (Fin 2) ℤ) ⧸ CongruenceSubgroup.Gamma0 N
      Finite Q ∧ Nat.card Q = ModularCurve.dedekindPsi N ∧
        Nat.card {q : Q // ModularGroup.S • q = q} = ModularCurve.nuTwo N ∧
        Nat.card {q : Q // (ModularGroup.S * ModularGroup.T) • q = q} =
          ModularCurve.nuThree N ∧
        Nat.card (Quotient (MulAction.orbitRel (Subgroup.zpowers ModularGroup.T) Q)) =
          ModularCurve.cuspCount N := by
  intro N _
  obtain ⟨hfinite, hindex⟩ := Submission.p10_17ae7b7d_cc_index N
  obtain ⟨htwo, hthree⟩ := Submission.p10_17ae7b7d_cc_elliptic_fixed_points N
  exact ⟨hfinite, hindex, htwo, hthree, Submission.p10_17ae7b7d_cc_translation_orbits N⟩
namespace Submission

open scoped MatrixGroups ModularForm Topology
open UpperHalfPlane

set_option backward.isDefEq.respectTransparency false in
/-- The norm of a nonzero weight-two cusp form, with its cusp and elliptic orders. -/
theorem p10_17ae7b7d_gamma0_norm_vanishing
    (N : ℕ) [NeZero N] (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2)
    (hf : f ≠ 0) :
    ∃ F A : ℂ → ℂ,
      DifferentiableOn ℂ F {z : ℂ | 0 < z.im} ∧
      (∃ z : ℂ, 0 < z.im ∧ F z ≠ 0) ∧
      (∀ z : ℂ, 0 < z.im → F (z + 1) = F z) ∧
      (∀ z : ℂ, 0 < z.im →
        F (-1 / z) = z ^ (2 * ModularCurve.dedekindPsi N) * F z) ∧
      AnalyticAt ℂ A 0 ∧
      (∃ Y : ℝ, ∀ z : ℂ, 0 < z.im → Y ≤ z.im →
        F z = A (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * z))) ∧
      ModularCurve.cuspCount N ≤ analyticOrderNatAt A 0 ∧
      ModularCurve.nuTwo N ≤ analyticOrderNatAt F Complex.I ∧
      2 * ModularCurve.nuThree N ≤
        analyticOrderNatAt F ((-1 + (Real.sqrt 3 : ℂ) * Complex.I) / 2) := by
  classical
  -- Inversion identifies a left coset aH with the right coset Ha⁻¹.
  let H := CongruenceSubgroup.Gamma0 N
  let Q := (SL(2, ℤ)) ⧸ H
  obtain ⟨hfinite, hcard, hS_count, hU_count, hT_count⟩ :=
    p10_17ae7b7d_gamma0_coset_counts N
  let : Finite Q := hfinite
  let : Fintype Q := Fintype.ofFinite Q
  have hcard' : Fintype.card Q = ModularCurve.dedekindPsi N := by
    simpa only [Nat.card_eq_fintype_card] using hcard
  have hf_fun : (f : ℍ → ℂ) ≠ 0 := by
    intro h
    apply hf
    exact CuspForm.ext (fun z => congrFun h z)
  have hinvariant (a : SL(2, ℤ)) (ha : a ∈ H) :
      (f : ℍ → ℂ) ∣[(2 : ℤ)] a = f := by
    exact SlashInvariantForm.slash_action_eqn f _
      (show (a : GL (Fin 2) ℝ) ∈
          (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) from
        ⟨a, ha, rfl⟩)
  have hcoset (a b : SL(2, ℤ)) (hab : (a : Q) = (b : Q)) :
      (f : ℍ → ℂ) ∣[(2 : ℤ)] a⁻¹ = (f : ℍ → ℂ) ∣[(2 : ℤ)] b⁻¹ := by
    have hm : b⁻¹ * a ∈ H := by
      simpa using H.inv_mem (QuotientGroup.eq.mp hab)
    calc
      (f : ℍ → ℂ) ∣[(2 : ℤ)] a⁻¹ =
          ((f : ℍ → ℂ) ∣[(2 : ℤ)] (b⁻¹ * a)) ∣[(2 : ℤ)] a⁻¹ := by
            rw [hinvariant _ hm]
      _ = (f : ℍ → ℂ) ∣[(2 : ℤ)] b⁻¹ := by
        rw [← SlashAction.slash_mul]
        simp only [mul_inv_cancel_right]
  let h : Q → ℍ → ℂ := fun q => (f : ℍ → ℂ) ∣[(2 : ℤ)] q.out⁻¹
  have hmk (a : SL(2, ℤ)) : h (a : Q) = (f : ℍ → ℂ) ∣[(2 : ℤ)] a⁻¹ :=
    hcoset _ _ (QuotientGroup.out_eq' _)
  have hslash (q : Q) (a : SL(2, ℤ)) :
      (h q) ∣[(2 : ℤ)] a = h (a⁻¹ • q) := by
    induction q using Quotient.inductionOn' with
    | h b =>
      change (h (b : Q)) ∣[(2 : ℤ)] a = h ((a⁻¹ * b : SL(2, ℤ)) : Q)
      rw [hmk, hmk, ← SlashAction.slash_mul]
      congr 1
      change b⁻¹ * a = (a⁻¹ * b)⁻¹
      group
  have htransform (q : Q) (a : SL(2, ℤ)) (z : ℍ) :
      h q (a • z) = denom a z ^ (2 : ℕ) * h (a⁻¹ • q) z := by
    have hs := congrFun (hslash q a) z
    rw [ModularForm.SL_slash_apply] at hs
    have hd := denom_ne_zero (a : GL (Fin 2) ℝ) z
    rw [zpow_neg, zpow_ofNat] at hs
    simpa only [mul_comm] using (mul_inv_eq_iff_eq_mul₀ (pow_ne_zero 2 hd)).mp hs
  let g : Q → ℂ → ℂ := fun q => h q ∘ UpperHalfPlane.ofComplex
  have gholo (q : Q) : DifferentiableOn ℂ (g q) {z : ℂ | 0 < z.im} :=
    UpperHalfPlane.mdifferentiable_iff.mp
      ((ModularFormClass.holo f).slash 2 (q.out⁻¹ : SL(2, ℤ)))
  have gana (q : Q) : AnalyticOnNhd ℂ (g q) {z : ℂ | 0 < z.im} :=
    (gholo q).analyticOnNhd isOpen_upperHalfPlaneSet
  have gnonzero (q : Q) : ∃ z : ℂ, 0 < z.im ∧ g q z ≠ 0 := by
    have hn : h q ≠ 0 :=
      (SlashAction.slash_eq_zero_iff 2 (q.out⁻¹ : SL(2, ℤ)) (f : ℍ → ℂ)).not.mpr hf_fun
    obtain ⟨z, hz⟩ : ∃ z : ℍ, h q z ≠ 0 := by
      by_contra! he
      exact hn (funext he)
    exact ⟨z, z.im_pos, by simpa [g] using hz⟩
  have halfplane_preconnected : IsPreconnected {z : ℂ | 0 < z.im} :=
    (convex_halfSpace_im_gt 0).isPreconnected
  have gfinite (q : Q) (z : ℂ) (hz : 0 < z.im) : analyticOrderAt (g q) z ≠ ⊤ := by
    obtain ⟨w, hw, hn⟩ := gnonzero q
    exact (gana q).analyticOrderAt_ne_top_of_isPreconnected halfplane_preconnected hw hz
      (by rw [(gana q w hw).analyticOrderAt_eq_zero.mpr hn]; exact ENat.zero_ne_top)
  have gdecay (q : Q) : ∀ ε : ℝ, 0 < ε → ∃ Y : ℝ,
      ∀ z : ℂ, 0 < z.im → Y ≤ z.im → ‖g q z‖ ≤ ε := by
    intro ε hε
    obtain ⟨Y, hY⟩ := UpperHalfPlane.isZeroAtImInfty_iff.mp
      (CuspFormClass.zero_at_infty_slash f (q.out⁻¹ : SL(2, ℤ))) ε hε
    refine ⟨Y, fun z hz hYz => ?_⟩
    simpa [g, h, UpperHalfPlane.ofComplex_apply_of_im_pos hz] using hY ⟨z, hz⟩ hYz
  let F : ℂ → ℂ := fun z => ∏ q : Q, g q z
  have Fana : AnalyticOnNhd ℂ F {z : ℂ | 0 < z.im} :=
    Finset.analyticOnNhd_fun_prod _ (fun q _ => gana q)
  have Fholo : DifferentiableOn ℂ F {z : ℂ | 0 < z.im} := Fana.differentiableOn
  have prod_order (s : Finset Q) (z : ℂ) (hz : 0 < z.im) :
      analyticOrderAt (fun w => ∏ q ∈ s, g q w) z =
        ∑ q ∈ s, analyticOrderAt (g q) z := by
    induction s using Finset.induction_on with
    | empty => simp [analyticOrderAt_eq_zero]
    | @insert q s hqs ih =>
      simp only [Finset.prod_insert hqs, Finset.sum_insert hqs]
      exact (analyticOrderAt_mul (gana q z hz)
        (s.analyticAt_fun_prod (fun a _ => gana a z hz))).trans (congrArg _ ih)
  have Ffinite (z : ℂ) (hz : 0 < z.im) : analyticOrderAt F z ≠ ⊤ := by
    rw [prod_order _ z hz]
    exact ENat.sum_ne_top.mpr (fun q _ => gfinite q z hz)
  have Fnonzero : ∃ z : ℂ, 0 < z.im ∧ F z ≠ 0 := by
    by_contra! he
    apply Ffinite Complex.I (by simp)
    apply analyticOrderAt_eq_top.mpr
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds (show 0 < Complex.I.im by simp)]
      with z hz using he z hz
  have Ftransform (a : SL(2, ℤ)) (z : ℍ) :
      F ((a • z : ℍ) : ℂ) = denom a z ^ (2 * ModularCurve.dedekindPsi N) * F z := by
    have hp : (∏ q : Q, h (a⁻¹ • q) z) = ∏ q : Q, h q z :=
      Equiv.prod_comp (MulAction.toPerm a⁻¹ : Q ≃ Q) (fun q => h q z)
    calc
      F ((a • z : ℍ) : ℂ) = ∏ q : Q, h q (a • z) := by simp [F, g]
      _ = ∏ q : Q, (denom a z ^ (2 : ℕ) * h (a⁻¹ • q) z) := by
        apply Finset.prod_congr rfl
        intro q _
        exact htransform q a z
      _ = denom a z ^ (2 * ModularCurve.dedekindPsi N) * F z := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← pow_mul,
          hcard', hp]
        simp [F, g]
  have Tcoe (z : ℍ) : ((ModularGroup.T • z : ℍ) : ℂ) = z + 1 := by
    rw [UpperHalfPlane.modular_T_smul]
    simp only [UpperHalfPlane.coe_vadd, Complex.ofReal_one, add_comm]
  have Scoe (z : ℍ) : ((ModularGroup.S • z : ℍ) : ℂ) = -1 / z := by
    rw [UpperHalfPlane.modular_S_smul]
    simp only [inv_neg, neg_div, one_div]
  have STcoe (z : ℍ) : (((ModularGroup.S * ModularGroup.T) • z : ℍ) : ℂ) =
      -1 / (z + 1) := by rw [mul_smul, Scoe, Tcoe]
  have Tdenom (z : ℍ) : denom ModularGroup.T z = 1 := by
    norm_num [UpperHalfPlane.denom, ModularGroup.T, Matrix.SpecialLinearGroup.toGL,
      Matrix.SpecialLinearGroup.map]
  have STdenom (z : ℍ) :
      denom (ModularGroup.S * ModularGroup.T : SL(2, ℤ)) z = z + 1 := by
    norm_num [UpperHalfPlane.denom, ModularGroup.S, ModularGroup.T,
      Matrix.SpecialLinearGroup.toGL, Matrix.SpecialLinearGroup.map,
      Matrix.mul_apply, Fin.sum_univ_two]
  have FT (z : ℂ) (hz : 0 < z.im) : F (z + 1) = F z := by
    have ht := Ftransform ModularGroup.T ⟨z, hz⟩
    rw [Tcoe, Tdenom] at ht
    simpa only [UpperHalfPlane.coe_mk, one_pow, one_mul] using ht
  have FS (z : ℂ) (hz : 0 < z.im) :
      F (-1 / z) = z ^ (2 * ModularCurve.dedekindPsi N) * F z := by
    have hs := Ftransform ModularGroup.S ⟨z, hz⟩
    rw [Scoe, ModularGroup.denom_S] at hs
    exact hs
  have gtransform (q : Q) (a : SL(2, ℤ)) (z : ℍ) :
      g q ((a • z : ℍ) : ℂ) = denom a z ^ (2 : ℕ) * g (a⁻¹ • q) z := by
    simpa only [g, Function.comp_apply, UpperHalfPlane.ofComplex_apply] using htransform q a z
  have Fnat_order (z : ℂ) (hz : 0 < z.im) :
      analyticOrderNatAt F z = ∑ q : Q, analyticOrderNatAt (g q) z := by
    dsimp only [analyticOrderNatAt, F]
    rw [prod_order _ z hz]
    exact ENat.toNat_sum (fun q _ => gfinite q z hz)
  have gS (q : Q) (hq : ModularGroup.S • q = q) (z : ℂ) (hz : 0 < z.im) :
      g q (-1 / z) = z ^ (2 : ℕ) * g q z := by
    have hqi : ModularGroup.S⁻¹ • q = q := inv_smul_eq_iff.mpr hq.symm
    have hh := gtransform q ModularGroup.S ⟨z, hz⟩
    rw [hqi, Scoe, ModularGroup.denom_S] at hh
    exact hh
  have gS_order (q : Q) (hq : ModularGroup.S • q = q) :
      1 ≤ analyticOrderNatAt (g q) Complex.I := by
    have hi : 0 < Complex.I.im := by simp
    have hd : HasDerivAt (fun z : ℂ => -1 / z) (-1) Complex.I := by
      convert! (hasDerivAt_const Complex.I (-1 : ℂ)).div (hasDerivAt_id Complex.I)
        Complex.I_ne_zero using 1
      norm_num
    have hψ : AnalyticAt ℂ (fun z : ℂ => -1 / z) Complex.I := by
      exact analyticAt_const.div analyticAt_id Complex.I_ne_zero
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
      (isOpen_upperHalfPlaneSet.mem_nhds hi)
    have hm := p10_17ae7b7d_norm_local_multiplier_order
      (g q) (fun z : ℂ => -1 / z) (fun z : ℂ => z ^ (2 : ℕ)) Complex.I
      (gana q _ hi) (gfinite q _ hi) hψ (by norm_num)
      (by rw [hd.deriv]; norm_num) (analyticAt_id.pow 2)
      ⟨r, hr, fun z hz => gS q hq z (hball (by simpa [Metric.mem_ball, dist_eq_norm] using hz))⟩
    rw [hd.deriv] at hm
    by_contra! hn
    have hz : analyticOrderNatAt (g q) Complex.I = 0 := by omega
    norm_num [hz] at hm
  have FS_order : ModularCurve.nuTwo N ≤ analyticOrderNatAt F Complex.I := by
    rw [Fnat_order _ (by simp), ← hS_count, Nat.card_eq_fintype_card]
    calc
      Fintype.card {q : Q // ModularGroup.S • q = q} =
          ∑ q : Q, if ModularGroup.S • q = q then 1 else 0 := by
            rw [Fintype.card_subtype]
            exact (Finset.sum_boole _ _).symm
      _ ≤ ∑ q : Q, analyticOrderNatAt (g q) Complex.I := by
        apply Finset.sum_le_sum
        intro q _
        split_ifs with hq
        · exact gS_order q hq
        · exact Nat.zero_le _
  let ρ : ℂ := (-1 + (Real.sqrt 3 : ℂ) * Complex.I) / 2
  have ρim : 0 < ρ.im := by dsimp [ρ]; simp
  have ρne : ρ ≠ 0 := fun hρ => by simp [hρ] at ρim
  have ρone : ρ ≠ 1 := fun hρ => by simp [hρ] at ρim
  have ρadd : ρ + 1 ≠ 0 := by
    intro he
    have hh := congrArg Complex.im he
    simp only [Complex.add_im, Complex.one_im, Complex.zero_im, add_zero] at hh
    exact (ne_of_gt ρim) hh
  have ρeq : ρ ^ 2 + ρ + 1 = 0 := by
    have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    apply Complex.ext <;> simp [ρ, Complex.mul_re, Complex.mul_im, pow_two] <;> nlinarith
  have ρmult : (ρ + 1) ^ 2 = ρ := by
    linear_combination ρeq
  have ρfix : -1 / (ρ + 1) = ρ := by
    apply (div_eq_iff ρadd).mpr
    linear_combination -ρeq
  have ρderiv : HasDerivAt (fun z : ℂ => -1 / (z + 1)) (ρ ^ 2) ρ := by
    have hd := (hasDerivAt_const ρ (-1 : ℂ)).div
      ((hasDerivAt_id ρ).add_const 1) ρadd
    convert! hd using 1
    change ρ ^ 2 = (0 * (ρ + 1) - -1 * 1) / (ρ + 1) ^ 2
    simp only [zero_mul, neg_one_mul, zero_sub, neg_neg]
    apply (eq_div_iff (pow_ne_zero 2 ρadd)).mpr
    linear_combination (ρ ^ 2 + ρ - 1) * ρeq
  have gU (q : Q) (hq : (ModularGroup.S * ModularGroup.T) • q = q)
      (z : ℂ) (hz : 0 < z.im) :
      g q (-1 / (z + 1)) = (z + 1) ^ (2 : ℕ) * g q z := by
    have hqi : (ModularGroup.S * ModularGroup.T)⁻¹ • q = q := inv_smul_eq_iff.mpr hq.symm
    have hh := gtransform q (ModularGroup.S * ModularGroup.T) ⟨z, hz⟩
    rw [hqi, STcoe, STdenom] at hh
    exact hh
  have gU_order (q : Q) (hq : (ModularGroup.S * ModularGroup.T) • q = q) :
      2 ≤ analyticOrderNatAt (g q) ρ := by
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
      (isOpen_upperHalfPlaneSet.mem_nhds ρim)
    have hm := p10_17ae7b7d_norm_local_multiplier_order
      (g q) (fun z : ℂ => -1 / (z + 1)) (fun z : ℂ => (z + 1) ^ (2 : ℕ)) ρ
      (gana q _ ρim) (gfinite q _ ρim)
      (analyticAt_const.div (analyticAt_id.add analyticAt_const) ρadd) ρfix
      (by rw [ρderiv.deriv]; exact pow_ne_zero _ ρne)
      ((analyticAt_id.add analyticAt_const).pow 2)
      ⟨r, hr, fun z hz => gU q hq z (hball (by simpa [Metric.mem_ball, dist_eq_norm] using hz))⟩
    rw [ρderiv.deriv, ρmult] at hm
    by_contra! hn
    interval_cases hmorder : analyticOrderNatAt (g q) ρ
    · exact ρone (by simpa [hmorder] using hm.symm)
    · have hρ : ρ ^ 2 = ρ := by simpa [hmorder] using hm
      have he : ρ * (ρ - 1) = 0 := by linear_combination hρ
      exact ρone (sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left ρne))
  have FU_order : 2 * ModularCurve.nuThree N ≤ analyticOrderNatAt F ρ := by
    rw [Fnat_order _ ρim, ← hU_count, Nat.card_eq_fintype_card]
    calc
      2 * Fintype.card {q : Q // (ModularGroup.S * ModularGroup.T) • q = q} =
          ∑ q : Q, if (ModularGroup.S * ModularGroup.T) • q = q then 2 else 0 := by
            rw [Fintype.card_subtype, ← Finset.sum_filter]
            simp only [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ q : Q, analyticOrderNatAt (g q) ρ := by
        apply Finset.sum_le_sum
        intro q _
        split_ifs with hq
        · exact gU_order q hq
        · exact Nat.zero_le _
  -- Regroup the norm by translation orbits. Each orbit product has period one
  -- and decays at infinity, so the disk extension has positive order.
  let O := Quotient (MulAction.orbitRel (Subgroup.zpowers ModularGroup.T) Q)
  let π : Q → O := Quotient.mk''
  let : Fintype O := Fintype.ofFinite O
  let s : O → Finset Q := fun o => Finset.univ.filter (fun q => π q = o)
  have smem (o : O) (q : Q) : q ∈ s o ↔ π q = o := by simp [s]
  have snonempty (o : O) : (s o).Nonempty := by
    refine ⟨o.out, (smem o _).mpr ?_⟩
    exact Quotient.out_eq' o
  have πT (q : Q) : π (ModularGroup.T • q) = π q := by
    exact MulAction.orbitRel.Quotient.quotient_smul_eq
      (g := (⟨ModularGroup.T, Subgroup.mem_zpowers _⟩ : Subgroup.zpowers ModularGroup.T))
  have πTi (q : Q) : π (ModularGroup.T⁻¹ • q) = π q := by
    exact MulAction.orbitRel.Quotient.quotient_smul_eq
      (g := (⟨ModularGroup.T⁻¹, (Subgroup.zpowers _).inv_mem (Subgroup.mem_zpowers _)⟩ :
        Subgroup.zpowers ModularGroup.T))
  let P : O → ℂ → ℂ := fun o z => ∏ q ∈ s o, g q z
  have Pana (o : O) : AnalyticOnNhd ℂ (P o) {z : ℂ | 0 < z.im} :=
    (s o).analyticOnNhd_fun_prod (fun q _ => gana q)
  have Pnonzero (o : O) : ∃ z : ℂ, 0 < z.im ∧ P o z ≠ 0 := by
    by_contra! he
    have hp : analyticOrderAt (P o) Complex.I ≠ ⊤ := by
      rw [prod_order (s o) _ (by simp)]
      exact ENat.sum_ne_top.mpr (fun q _ => gfinite q _ (by simp))
    apply hp
    apply analyticOrderAt_eq_top.mpr
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds (show 0 < Complex.I.im by simp)]
      with z hz using he z hz
  have gT (q : Q) (z : ℂ) (hz : 0 < z.im) :
      g q (z + 1) = g (ModularGroup.T⁻¹ • q) z := by
    have ht := gtransform q ModularGroup.T ⟨z, hz⟩
    rw [Tcoe, Tdenom] at ht
    simpa only [UpperHalfPlane.coe_mk, one_pow, one_mul] using ht
  have PT (o : O) (z : ℂ) (hz : 0 < z.im) : P o (z + 1) = P o z := by
    change (∏ q ∈ s o, g q (z + 1)) = ∏ q ∈ s o, g q z
    simp_rw [gT _ z hz]
    apply Finset.prod_bij (fun q _ => ModularGroup.T⁻¹ • q)
    · intro q hq
      rw [smem, πTi]
      exact (smem o q).mp hq
    · intro q _ q' _ he
      exact (MulAction.injective _ he)
    · intro q hq
      refine ⟨ModularGroup.T • q, ?_, inv_smul_smul _ _⟩
      rw [smem, πT]
      exact (smem o q).mp hq
    · intro q _
      rfl
  have Pdecay (o : O) : ∀ ε : ℝ, 0 < ε → ∃ Y : ℝ,
      ∀ z : ℂ, 0 < z.im → Y ≤ z.im → ‖P o z‖ ≤ ε := by
    intro ε hε
    obtain ⟨q₀, hq₀⟩ := snonempty o
    choose Y hY using fun q : Q =>
      gdecay q (if q = q₀ then ε else 1) (by split_ifs <;> positivity)
    refine ⟨Finset.univ.sup' Finset.univ_nonempty Y, fun z hz hYz => ?_⟩
    calc
      ‖P o z‖ = ∏ q ∈ s o, ‖g q z‖ := norm_prod _ _
      _ ≤ ∏ q ∈ s o, (if q = q₀ then ε else 1) :=
        Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun q _ =>
          hY q z hz ((Finset.le_sup' Y (Finset.mem_univ q)).trans hYz))
      _ = ε := Finset.prod_ite_eq_of_mem' (s o) q₀ (fun _ => ε) hq₀
  have Pexp (o : O) : ∃ B : ℂ → ℂ, AnalyticAt ℂ B 0 ∧ analyticOrderAt B 0 ≠ ⊤ ∧
      1 ≤ analyticOrderNatAt B 0 ∧ ∀ z : ℂ, 0 < z.im →
        P o z = B (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * z)) := by
    obtain ⟨Y, hY⟩ := Pdecay o 1 zero_lt_one
    obtain ⟨B, hB, he, hfin, hpos⟩ := p10_17ae7b7d_periodic_disk_extension
      1 (P o) zero_lt_one (Pana o).differentiableOn (Pnonzero o)
      (by simpa using PT o) ⟨1, Y, hY⟩
    exact ⟨B, hB.analyticAt (Metric.isOpen_ball.mem_nhds (by simp)), hfin,
      hpos (Pdecay o), fun z hz => by simpa using he z hz⟩
  choose B Bana Bfinite Bpositive Bexp using Pexp
  let C : ℂ → ℂ := fun z => ∏ o : O, B o z
  have Cana : AnalyticAt ℂ C 0 := Finset.univ.analyticAt_fun_prod (fun o _ => Bana o)
  have Cqexp (z : ℂ) (hz : 0 < z.im) :
      F z = C (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * z)) := by
    change (∏ q : Q, g q z) = ∏ o : O, B o _
    rw [← Finset.prod_fiberwise Finset.univ π (fun q => g q z)]
    exact Finset.prod_congr rfl (fun o _ => Bexp o z hz)
  have Corder (t : Finset O) : analyticOrderAt (fun z => ∏ o ∈ t, B o z) 0 =
      ∑ o ∈ t, analyticOrderAt (B o) 0 := by
    induction t using Finset.induction_on with
    | empty => simp [analyticOrderAt_eq_zero]
    | @insert o t hot ih =>
      simp only [Finset.prod_insert hot, Finset.sum_insert hot]
      exact (analyticOrderAt_mul (Bana o)
        (t.analyticAt_fun_prod (fun a _ => Bana a))).trans (congrArg _ ih)
  have Cnat_order : analyticOrderNatAt C 0 = ∑ o : O, analyticOrderNatAt (B o) 0 := by
    dsimp only [analyticOrderNatAt, C]
    rw [Corder Finset.univ]
    exact ENat.toNat_sum (fun o _ => Bfinite o)
  have Ccusp_order : ModularCurve.cuspCount N ≤ analyticOrderNatAt C 0 := by
    rw [Cnat_order, ← hT_count]
    change Nat.card O ≤ ∑ o : O, analyticOrderNatAt (B o) 0
    rw [Nat.card_eq_fintype_card]
    calc
      Fintype.card O = ∑ _o : O, (1 : ℕ) := by simp
      _ ≤ ∑ o : O, analyticOrderNatAt (B o) 0 := Finset.sum_le_sum (fun o _ => Bpositive o)
  exact ⟨F, C, Fholo, Fnonzero, FT, FS, Cana,
    ⟨0, fun z hz _ => Cqexp z hz⟩, Ccusp_order, FS_order, FU_order⟩

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
              (∀ i ∈ cells, Complex.IsExactOn L (square d i)) ∧
              S.Pairwise (fun v w => Disjoint (Metric.closedBall v r) (Metric.closedBall w r)) ∧
              ∀ v ∈ S, Metric.closedBall v r ⊆ Ω ε := by
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
      refine ⟨d, hd, hfiniteCells, ?_, ?_, hpairs, fun v hv => (hcircles v hv).1⟩
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
  -- Step 6: choose a translated grid in general position and retain its local primitives.
  have hcircleVerticalFinite (c : ℂ) (r x : ℝ) :
      {z : ℂ | ‖z - c‖ = r ∧ z.re = x}.Finite := by
    classical
    let y := Real.sqrt (r ^ 2 - (x - c.re) ^ 2)
    apply (Set.toFinite ({(x : ℂ) + ((c.im + y : ℝ) : ℂ) * Complex.I,
      (x : ℂ) + ((c.im - y : ℝ) : ℂ) * Complex.I} : Set ℂ)).subset
    intro z hz
    have hs := Complex.sq_norm_sub_sq_re (z - c)
    rw [hz.1, Complex.sub_re, Complex.sub_im, hz.2] at hs
    have hsqrt : y = |z.im - c.im| := by
      dsimp [y]
      rw [hs, Real.sqrt_sq_eq_abs]
    by_cases h : 0 ≤ z.im - c.im
    · rw [abs_of_nonneg h] at hsqrt
      apply Or.inl
      apply Complex.ext
      · simpa using hz.2
      · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
          Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_add]
        linarith
    · rw [abs_of_neg (lt_of_not_ge h)] at hsqrt
      apply Or.inr
      apply Complex.ext
      · simpa using hz.2
      · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
          Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_add]
        linarith

  have hcircleHorizontalFinite (c : ℂ) (r y : ℝ) :
      {z : ℂ | ‖z - c‖ = r ∧ z.im = y}.Finite := by
    classical
    let x := Real.sqrt (r ^ 2 - (y - c.im) ^ 2)
    apply (Set.toFinite ({((c.re + x : ℝ) : ℂ) + (y : ℂ) * Complex.I,
      ((c.re - x : ℝ) : ℂ) + (y : ℂ) * Complex.I} : Set ℂ)).subset
    intro z hz
    have hs := Complex.sq_norm_sub_sq_re (z - c)
    rw [hz.1, Complex.sub_re, Complex.sub_im, hz.2] at hs
    have hs' : r ^ 2 - (y - c.im) ^ 2 = (z.re - c.re) ^ 2 := by linarith
    have hsqrt : x = |z.re - c.re| := by
      dsimp [x]
      rw [hs', Real.sqrt_sq_eq_abs]
    by_cases h : 0 ≤ z.re - c.re
    · rw [abs_of_nonneg h] at hsqrt
      apply Or.inl
      apply Complex.ext
      · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
          Complex.I_re, mul_zero]
        linarith
      · simpa using hz.2
    · rw [abs_of_neg (lt_of_not_ge h)] at hsqrt
      apply Or.inr
      apply Complex.ext
      · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
          Complex.I_re, mul_zero]
        linarith
      · simpa using hz.2

  have hcircleTransverse (c z : ℂ) (r : ℝ) (hz : ‖z - c‖ = r) :
      (z.re ≠ c.re + r → z.re ≠ c.re - r → z.im ≠ c.im) ∧
      (z.im ≠ c.im + r → z.im ≠ c.im - r → z.re ≠ c.re) := by
    have hs := Complex.sq_norm_sub_sq_re (z - c)
    rw [hz, Complex.sub_re, Complex.sub_im] at hs
    constructor
    · intro hplus hminus heq
      have he : (z.re - c.re) ^ 2 = r ^ 2 := by rw [heq] at hs; nlinarith [hs]
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp he with h | h
      · exact hplus (by linarith)
      · exact hminus (by linarith)
    · intro hplus hminus heq
      have he : (z.im - c.im) ^ 2 = r ^ 2 := by rw [heq] at hs; nlinarith [hs]
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp he with h | h
      · exact hplus (by linarith)
      · exact hminus (by linarith)
  -- Transverse circle crossings determine the occupied side and endpoint sign.
  have hlineCircleCrossing : ∀ (p c u : ℂ) (r : ℝ), 0 ≤ r → ‖p - c‖ = r →
      (p - c).re * u.re + (p - c).im * u.im ≠ 0 →
      ∀ᶠ s : ℝ in nhds 0,
        (r < ‖p + (s : ℂ) * u - c‖ ↔
          0 < s * ((p - c).re * u.re + (p - c).im * u.im)) := by
    classical
    have hrealSignedCrossing (f : ℝ → ℝ) (t d : ℝ)
        (hf : HasDerivAt f d t) (hd : d ≠ 0) :
        ∀ᶠ x in nhds t, (0 < f x - f t ↔ 0 < (x - t) * d) := by
      let q : ℝ → ℝ := Function.update (fun x => (f x - f t) / (x - t)) t d
      have hq : ContinuousAt q t := hf.continuousAt_div
      have hpos : ∀ᶠ x in nhds t, 0 < d * q x := by
        apply (continuousAt_const.mul hq).tendsto.eventually (isOpen_Ioi.mem_nhds _)
        simpa [q] using mul_self_pos.mpr hd
      filter_upwards [hpos] with x hx
      have heq : f x - f t = (x - t) * q x := by
        by_cases hxt : x = t
        · simp [hxt]
        · simp only [q, Function.update_of_ne hxt]
          field_simp
      rw [heq]
      rcases mul_pos_iff.mp hx with ⟨hdp, hqp⟩ | ⟨hdn, hqn⟩
      · simp only [mul_pos_iff_of_pos_right hqp, mul_pos_iff_of_pos_right hdp]
      · simp only [mul_pos_iff, not_lt.mpr hqn.le, not_lt.mpr hdn.le, hqn, hdn,
          and_false, and_true, false_or]
    intro p c u r hr hpr htrans
    let D : ℝ := (p - c).re * u.re + (p - c).im * u.im
    let f : ℝ → ℝ := fun s => 2 * D * s + Complex.normSq u * s ^ 2
    have hf : HasDerivAt f (2 * D) 0 := by
      convert! (((hasDerivAt_id (0 : ℝ)).const_mul (2 * D)).add
        (((hasDerivAt_id (0 : ℝ)).pow 2).const_mul (Complex.normSq u))) using 1
      norm_num
    have hD : 2 * D ≠ 0 := mul_ne_zero (by norm_num) htrans
    filter_upwards [hrealSignedCrossing f 0 (2 * D) hf hD] with s hs
    have hnorm : ‖p + (s : ℂ) * u - c‖ ^ 2 - r ^ 2 = f s := by
      rw [← hpr]
      simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.sub_re,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
        Complex.add_im, Complex.sub_im, Complex.mul_im, f, D]
      ring
    have hsq : r < ‖p + (s : ℂ) * u - c‖ ↔ 0 < f s := by
      constructor
      · intro h
        nlinarith only [hnorm, hr, h]
      · intro h
        nlinarith only [hnorm, hr, norm_nonneg (p + (s : ℂ) * u - c), h]
    rw [hsq]
    have hf0 : f 0 = 0 := by simp [f]
    rw [hf0, sub_zero, sub_zero] at hs
    rw [hs]
    change 0 < s * (2 * D) ↔ 0 < s * D
    rw [show s * (2 * D) = 2 * (s * D) by ring, mul_pos_iff_of_pos_left (by norm_num : (0 : ℝ) < 2)]
  have hpuncturedExterior (U : Set ℂ) (hU : IsOpen U) (S : Set ℂ) (hS : S.Finite) (r : ℝ)
      (hballs : ∀ v ∈ S, Metric.closedBall v r ⊆ U)
      (hpairs : S.Pairwise (fun v w => Disjoint (Metric.closedBall v r) (Metric.closedBall w r)))
      (v : ℂ) (hv : v ∈ S) (z : ℂ) (hz : z ∈ Metric.sphere v r) :
      ∀ᶠ w in nhds z, (w ∈ U \ ⋃ c ∈ S, Metric.closedBall c r ↔ r < ‖w - v‖) := by
    have hzball := Metric.sphere_subset_closedBall hz
    have hopen : IsOpen (U \ ⋃ c ∈ S \ {v}, Metric.closedBall c r) :=
      hU.sdiff ((hS.sdiff : (S \ {v}).Finite).isClosed_biUnion
        (fun _ _ => Metric.isClosed_closedBall))
    have hzother : z ∈ U \ ⋃ c ∈ S \ {v}, Metric.closedBall c r := by
      refine ⟨hballs v hv hzball, ?_⟩
      intro hmem
      obtain ⟨c, hc, hzc⟩ := Set.mem_iUnion₂.mp hmem
      exact Set.disjoint_left.mp (hpairs hv hc.1 (Ne.symm hc.2)) hzball hzc
    filter_upwards [hopen.mem_nhds hzother] with w hw
    constructor
    · intro hmem
      have hn : w ∉ Metric.closedBall v r := fun h =>
        hmem.2 (Set.mem_iUnion₂.mpr ⟨v, hv, h⟩)
      simpa only [Metric.mem_closedBall, dist_eq_norm, not_le] using hn
    · intro hnorm
      refine ⟨hw.1, ?_⟩
      intro hmem
      obtain ⟨c, hc, hwc⟩ := Set.mem_iUnion₂.mp hmem
      by_cases hcv : c = v
      · subst c
        exact (not_le_of_gt hnorm) (by simpa only [Metric.mem_closedBall, dist_eq_norm] using hwc)
      · exact hw.2 (Set.mem_iUnion₂.mpr ⟨c, ⟨hc, hcv⟩, hwc⟩)
  have hoccupiedEndpointSigns (η : ℝ → ℂ) (V : Set ℂ) (t D : ℝ) (a b : ℝ) (hab : a < b)
      (hmem : ∀ x ∈ Set.Ioo a b, η x ∈ V)
      (hcross : ∀ᶠ x in nhds t, (η x ∈ V ↔ 0 < (x - t) * D)) :
      (a = t → 0 < D) ∧ (b = t → D < 0) := by
    constructor
    · rintro rfl
      have hnear : ∀ᶠ x in nhdsWithin a (Set.Ioi a),
          (η x ∈ V ↔ 0 < (x - a) * D) ∧ x < b :=
        (hcross.and (eventually_lt_nhds hab)).filter_mono nhdsWithin_le_nhds
      have hside : ∀ᶠ x in nhdsWithin a (Set.Ioi a), a < x := self_mem_nhdsWithin
      obtain ⟨x, hx, hsign, hxb⟩ := (hside.and hnear).exists
      have hpos := hsign.mp (hmem x ⟨hx, hxb⟩)
      exact (mul_pos_iff_of_pos_left (sub_pos.mpr hx)).mp hpos
    · rintro rfl
      have hnear : ∀ᶠ x in nhdsWithin b (Set.Iio b),
          (η x ∈ V ↔ 0 < (x - b) * D) ∧ a < x :=
        (hcross.and (eventually_gt_nhds hab)).filter_mono nhdsWithin_le_nhds
      have hside : ∀ᶠ x in nhdsWithin b (Set.Iio b), x < b := self_mem_nhdsWithin
      obtain ⟨x, hx, hsign, hax⟩ := (hside.and hnear).exists
      have hpos := hsign.mp (hmem x ⟨hax, hx⟩)
      exact neg_of_mul_pos_right hpos (sub_nonpos.mpr hx.le)
  have hgridChoice (d : ℝ) (P : Set ℂ) (C : Set (ℂ × ℝ))
      (hP : P.Countable) (hC : C.Countable) :
      ∃ a : ℂ,
        (∀ p ∈ P, ∀ n : ℤ, a.re + n * d ≠ p.re ∧ a.im + n * d ≠ p.im) ∧
        (∀ c ∈ C, ∀ n : ℤ,
          a.re + n * d ≠ c.1.re + c.2 ∧ a.re + n * d ≠ c.1.re - c.2 ∧
          a.im + n * d ≠ c.1.im + c.2 ∧ a.im + n * d ≠ c.1.im - c.2) ∧
        (∀ c ∈ C, ∀ n m : ℤ,
          ‖((a.re + n * d : ℝ) : ℂ) + ((a.im + m * d : ℝ) : ℂ) * Complex.I - c.1‖ ≠
            c.2) := by
    classical
    have havoid : ∀ S : Set ℝ, S.Countable → ∃ x : ℝ, x ∉ S := by
      intro S hS
      by_contra! h
      exact Set.not_countable_univ (hS.mono (fun x _ => h x))
    let X : Set ℝ :=
      (⋃ p ∈ P, ⋃ n : ℤ, {p.re - n * d}) ∪
      (⋃ c ∈ C, ⋃ n : ℤ, {c.1.re + c.2 - n * d, c.1.re - c.2 - n * d})
    have hX : X.Countable :=
      (hP.biUnion (fun _ _ => Set.countable_iUnion (fun _ => Set.countable_singleton _))).union
        (hC.biUnion (fun _ _ => Set.countable_iUnion (fun _ => Set.to_countable _)))
    obtain ⟨x, hx⟩ := havoid X hX
    let W : Set ℝ :=
      (⋃ p ∈ P, ⋃ n : ℤ, {p.im - n * d}) ∪
      (⋃ c ∈ C, ⋃ n : ℤ, {c.1.im + c.2 - n * d, c.1.im - c.2 - n * d}) ∪
      (⋃ c ∈ C, ⋃ n : ℤ, ⋃ m : ℤ,
        {c.1.im + Real.sqrt (c.2 ^ 2 - (x + n * d - c.1.re) ^ 2) - m * d,
         c.1.im - Real.sqrt (c.2 ^ 2 - (x + n * d - c.1.re) ^ 2) - m * d})
    have hW : W.Countable :=
      ((hP.biUnion (fun _ _ => Set.countable_iUnion (fun _ => Set.countable_singleton _))).union
        (hC.biUnion (fun _ _ => Set.countable_iUnion (fun _ => Set.to_countable _)))).union
        (hC.biUnion (fun _ _ => Set.countable_iUnion (fun _ =>
          Set.countable_iUnion (fun _ => Set.to_countable _))))
    obtain ⟨y, hy⟩ := havoid W hW
    refine ⟨(x : ℂ) + (y : ℂ) * Complex.I, ?_, ?_, ?_⟩
    · intro p hp n
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, sub_zero, add_zero,
        Complex.add_im, Complex.mul_im, mul_one, zero_add]
      constructor
      · intro heq
        apply hx
        exact Or.inl (Set.mem_iUnion₂.mpr ⟨p, hp,
          Set.mem_iUnion.mpr ⟨n, by simp only [Set.mem_singleton_iff]; linarith⟩⟩)
      · intro heq
        apply hy
        exact Or.inl (Or.inl (Set.mem_iUnion₂.mpr ⟨p, hp,
          Set.mem_iUnion.mpr ⟨n, by simp only [Set.mem_singleton_iff]; linarith⟩⟩))
    · intro c hc n
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, sub_zero, add_zero,
        Complex.add_im, Complex.mul_im, mul_one, zero_add]
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro heq
        apply hx
        exact Or.inr (Set.mem_iUnion₂.mpr ⟨c, hc,
          Set.mem_iUnion.mpr ⟨n, Or.inl (by linarith)⟩⟩)
      · intro heq
        apply hx
        exact Or.inr (Set.mem_iUnion₂.mpr ⟨c, hc,
          Set.mem_iUnion.mpr ⟨n, Or.inr (by simp only [Set.mem_singleton_iff]; linarith)⟩⟩)
      · intro heq
        apply hy
        exact Or.inl (Or.inr (Set.mem_iUnion₂.mpr ⟨c, hc,
          Set.mem_iUnion.mpr ⟨n, Or.inl (by linarith)⟩⟩))
      · intro heq
        apply hy
        exact Or.inl (Or.inr (Set.mem_iUnion₂.mpr ⟨c, hc,
          Set.mem_iUnion.mpr ⟨n, Or.inr (by simp only [Set.mem_singleton_iff]; linarith)⟩⟩))
    · intro c hc n m
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, sub_zero, add_zero,
        Complex.add_im, Complex.mul_im, mul_one, zero_add]
      intro heq
      have hs := Complex.sq_norm_sub_sq_re
        ((((x + n * d : ℝ) : ℂ) + ((y + m * d : ℝ) : ℂ) * Complex.I) - c.1)
      rw [heq] at hs
      simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.ofReal_re,
        Complex.add_im, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
        Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero, zero_add] at hs
      have hsqrt : Real.sqrt (c.2 ^ 2 - (x + n * d - c.1.re) ^ 2) =
          |y + m * d - c.1.im| := by
        rw [hs, Real.sqrt_sq_eq_abs]
      apply hy
      apply Or.inr
      refine Set.mem_iUnion₂.mpr ⟨c, hc, Set.mem_iUnion.mpr ⟨n,
        Set.mem_iUnion.mpr ⟨m, ?_⟩⟩⟩
      by_cases h : 0 ≤ y + m * d - c.1.im
      · rw [abs_of_nonneg h] at hsqrt
        exact Or.inl (by linarith)
      · rw [abs_of_neg (lt_of_not_ge h)] at hsqrt
        exact Or.inr (by simp only [Set.mem_singleton_iff]; linarith)
  have htranslatedMesh (Q : Set ℂ) (hQ : IsCompact Q) (δ d : ℝ)
      (hd : 0 < d) (hdδ : 2 * d < δ)
      (hmesh : ∀ z ∈ Q, Complex.IsExactOn L (Metric.ball z δ)) :
      let square : ℂ → ℤ × ℤ → Set ℂ := fun a i => {z |
        a.re + (i.1 : ℝ) * d ≤ z.re ∧ z.re ≤ a.re + ((i.1 : ℝ) + 1) * d ∧
        a.im + (i.2 : ℝ) * d ≤ z.im ∧ z.im ≤ a.im + ((i.2 : ℝ) + 1) * d}
      ∀ a : ℂ,
        let cells : Set (ℤ × ℤ) := {i | (Q ∩ square a i).Nonempty}
        cells.Finite ∧ Q ⊆ ⋃ i ∈ cells, square a i ∧
          ∀ i ∈ cells, Complex.IsExactOn L (square a i) := by
    classical
    intro square a cells
    have hcover : ∀ z : ℂ, ∃ i : ℤ × ℤ, z ∈ square a i := by
      intro z
      refine ⟨(⌊(z.re - a.re) / d⌋, ⌊(z.im - a.im) / d⌋), ?_⟩
      have hlo (x : ℝ) : (⌊x / d⌋ : ℝ) * d ≤ x := by
        simpa only [div_mul_cancel₀ _ hd.ne'] using
          mul_le_mul_of_nonneg_right (Int.floor_le (x / d)) hd.le
      have hhi (x : ℝ) : x ≤ ((⌊x / d⌋ : ℝ) + 1) * d := by
        simpa only [div_mul_cancel₀ _ hd.ne'] using
          mul_le_mul_of_nonneg_right (Int.lt_floor_add_one (x / d)).le hd.le
      exact ⟨by linarith [hlo (z.re - a.re)], by linarith [hhi (z.re - a.re)],
        by linarith [hlo (z.im - a.im)], by linarith [hhi (z.im - a.im)]⟩
    have hfinite : cells.Finite := by
      obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp hQ.isBounded
      obtain ⟨N, hN⟩ := exists_nat_gt ((R + ‖a‖ + d) / d)
      have hNd : R + ‖a‖ + d < (N : ℝ) * d := by
        simpa only [div_mul_cancel₀ _ hd.ne'] using mul_lt_mul_of_pos_right hN hd
      apply (Set.finite_Icc ((-(N : ℤ), -(N : ℤ))) ((N : ℤ), (N : ℤ))).subset
      intro i hi
      obtain ⟨z, hz, hzi⟩ := hi
      have hzre := abs_le.mp ((Complex.abs_re_le_norm z).trans (hR z hz))
      have hzim := abs_le.mp ((Complex.abs_im_le_norm z).trans (hR z hz))
      have hare := abs_le.mp (Complex.abs_re_le_norm a)
      have haim := abs_le.mp (Complex.abs_im_le_norm a)
      have hi1lo : -(N : ℝ) ≤ (i.1 : ℝ) := by nlinarith [hzi.2.1]
      have hi1hi : (i.1 : ℝ) ≤ (N : ℝ) := by nlinarith [hzi.1]
      have hi2lo : -(N : ℝ) ≤ (i.2 : ℝ) := by nlinarith [hzi.2.2.2]
      have hi2hi : (i.2 : ℝ) ≤ (N : ℝ) := by nlinarith [hzi.2.2.1]
      exact ⟨⟨by exact_mod_cast hi1lo, by exact_mod_cast hi2lo⟩,
        ⟨by exact_mod_cast hi1hi, by exact_mod_cast hi2hi⟩⟩
    refine ⟨hfinite, ?_, ?_⟩
    · intro z hz
      obtain ⟨i, hzi⟩ := hcover z
      exact Set.mem_iUnion₂.mpr ⟨i, ⟨z, hz, hzi⟩, hzi⟩
    · intro i hi
      obtain ⟨z, hz, hzi⟩ := hi
      obtain ⟨g, hg⟩ := hmesh z hz
      refine ⟨g, fun w hwi => hg w ?_⟩
      have hre : |(w - z).re| ≤ d := by
        rw [Complex.sub_re, abs_le]
        constructor <;> linarith [hzi.1, hzi.2.1, hwi.1, hwi.2.1]
      have him : |(w - z).im| ≤ d := by
        rw [Complex.sub_im, abs_le]
        constructor <;> linarith [hzi.2.2.1, hzi.2.2.2, hwi.2.2.1, hwi.2.2.2]
      rw [Metric.mem_ball, dist_eq_norm]
      exact lt_of_le_of_lt
        ((Complex.norm_le_abs_re_add_abs_im (w - z)).trans (add_le_add hre him))
        (by linarith)
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
  have hcircleTangent (v u : ℂ) (r s : ℝ) :
      (deriv (circleMap v r) s * star u).im =
        (circleMap v r s - v).re * u.re + (circleMap v r s - v).im * u.im := by
    rw [deriv_circleMap, circleMap_sub_center]
    simp [Complex.mul_im, Complex.mul_re]
    ring
  have hmobiusTangent (v w : ℂ) (e : ℝ) (he : 0 < e) (he1 : e < 1) (hw : ‖w‖ = e) :
      (v - star v) * Complex.I * w / (1 - w) ^ 2 =
        (((1 - e ^ 2) / Complex.normSq (1 - w) : ℝ) : ℂ) * Complex.I *
          ((v - star v * w) / (1 - w) -
            (v - star v * (e : ℂ) ^ 2) / (1 - (e : ℂ) ^ 2)) := by
    have hden : 1 - w ≠ 0 := by
      intro h
      have hw1 : w = 1 := (sub_eq_zero.mp h).symm
      rw [hw1, norm_one] at hw
      linarith
    have hnorm : Complex.normSq (1 - w) ≠ 0 :=
      mt Complex.normSq_eq_zero.mp hden
    have ha : (1 : ℂ) - (e : ℂ) ^ 2 ≠ 0 := by
      have hreal : (1 : ℝ) - e ^ 2 ≠ 0 := ne_of_gt (by nlinarith only [he, he1])
      exact_mod_cast hreal
    have hwstar : w * star w = (e : ℂ) ^ 2 := by
      simpa only [Complex.star_def, Complex.normSq_eq_norm_sq, hw, Complex.ofReal_pow]
        using Complex.mul_conj w
    have hn : (Complex.normSq (1 - w) : ℂ) = (1 - w) * (1 - star w) := by
      simpa using (Complex.mul_conj (1 - w)).symm
    push_cast
    field_simp [hden, ha, Complex.ofReal_ne_zero.mpr hnorm]
    rw [hn, ← hwstar]
    ring
  have hgammaDerivative (v : ℂ) (e : ℝ) (he : 0 < e) (he1 : e < 1) (t : ℝ) :
      deriv (fun s : ℝ =>
        (v - star v * ((e : ℂ) * Complex.exp ((s : ℂ) * Complex.I))) /
          (1 - (e : ℂ) * Complex.exp ((s : ℂ) * Complex.I))) t =
        (v - star v) * Complex.I * ((e : ℂ) * Complex.exp ((t : ℂ) * Complex.I)) /
          (1 - (e : ℂ) * Complex.exp ((t : ℂ) * Complex.I)) ^ 2 := by
    let w : ℝ → ℂ := fun s => (e : ℂ) * Complex.exp ((s : ℂ) * Complex.I)
    have hw : HasDerivAt w (Complex.I * w t) t := by
      convert hasDerivAt_circleMap 0 e t using 1
      · ext s
        simp [w, circleMap]
      · simp [w, circleMap, mul_comm]
    have hn : ‖w t‖ = e := by
      rw [show w = circleMap 0 e from by ext s; simp [w, circleMap]]
      simp [norm_circleMap_zero, abs_of_pos he]
    have hden : 1 - w t ≠ 0 := by
      intro hz
      have hw1 : w t = 1 := (sub_eq_zero.mp hz).symm
      rw [hw1, norm_one] at hn
      linarith
    have hquot := (((hw.const_mul (star v)).const_sub v).div (hw.const_sub 1) hden).deriv
    change deriv (fun s : ℝ => (v - star v * w s) / (1 - w s)) t = _
    calc
      _ = (-(star v * (Complex.I * w t)) * (1 - w t) -
          (v - star v * w t) * -(Complex.I * w t)) / (1 - w t) ^ 2 := by
        convert! hquot using 1
      _ = (v - star v) * Complex.I * w t / (1 - w t) ^ 2 := by
        congr 1
        ring
  have hgammaCenter (v : ℂ) (e : ℝ) (he : 0 < e) (he1 : e < 1) :
      (v.re : ℂ) + ((v.im * (1 + e ^ 2) / (1 - e ^ 2) : ℝ) : ℂ) * Complex.I =
        (v - star v * (e : ℂ) ^ 2) / (1 - (e : ℂ) ^ 2) := by
    have ha : (1 : ℂ) - (e : ℂ) ^ 2 ≠ 0 := by
      have hreal : (1 : ℝ) - e ^ 2 ≠ 0 := ne_of_gt (by nlinarith only [he, he1])
      exact_mod_cast hreal
    push_cast
    field_simp [ha]
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring
  have hgammaTangent (v : ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (t : ℝ) :
      ∃ speed : ℝ, 0 < speed ∧ deriv (γ v ε) t =
        (speed : ℂ) * Complex.I * (γ v ε t - cutCenter v ε) := by
    let w : ℂ := (ε : ℂ) * Complex.exp ((t : ℂ) * Complex.I)
    refine ⟨(1 - ε ^ 2) / Complex.normSq (1 - w),
      div_pos (by nlinarith only [hε, hε1])
        (Complex.normSq_pos.mpr (hphaseDen ε hε hε1 t)), ?_⟩
    have hcenter : cutCenter v ε =
        (v - star v * (ε : ℂ) ^ 2) / (1 - (ε : ℂ) ^ 2) := hgammaCenter v ε hε hε1
    rw [hcenter]
    change deriv (fun s : ℝ => (v - star v * ((ε : ℂ) * Complex.exp ((s : ℂ) * Complex.I))) /
      (1 - (ε : ℂ) * Complex.exp ((s : ℂ) * Complex.I))) t = _
    rw [hgammaDerivative v ε hε hε1 t]
    exact hmobiusTangent v w ε hε hε1 (hphaseNorm ε hε t)
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
  -- The retained integrands are integrable although L has poles on the original
  -- boundary: the open cut interiors contain all of those poles.
  have hretainedIntegrable (η η' : ℝ → ℂ) (a b : ℝ)
      (hη : Continuous η) (hη' : Continuous η')
      (hboundary : ∀ t ∈ Set.uIcc a b, η t ∈ K ∧ η t ∉ O)
      (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
      IntervalIntegrable (fun t => if η t ∈ removed ε then 0 else L (η t) * η' t)
        MeasureTheory.volume a b := by
    let W : Set ℂ := ⋃ v ∈ B, interior (D v ε)
    let R : Set ℝ := Set.uIcc a b \ η ⁻¹' W
    have hW : IsOpen W := isOpen_biUnion (fun _ _ => isOpen_interior)
    have hR : IsCompact R := isCompact_uIcc.diff (hW.preimage hη)
    have hzeroFree : ∀ t ∈ R, F (η t) ≠ 0 := by
      intro t ht hzero
      have hB : η t ∈ B := ⟨⟨(hboundary t ht.1).1, hzero⟩, (hboundary t ht.1).2⟩
      exact ht.2 (Set.mem_iUnion₂.mpr
        ⟨η t, hB, hcenterInterior (η t) (hKH hB.1.1) ε hε⟩)
    have hcont : ContinuousOn (fun t => L (η t) * η' t) R := by
      intro t ht
      exact (((hLan (η t) (hKH (hboundary t ht.1).1) (hzeroFree t ht)).continuousAt.comp
        hη.continuousAt).mul hη'.continuousAt).continuousWithinAt
    let T : Set ℝ := (η ⁻¹' removed ε)ᶜ
    have hT : MeasurableSet T :=
      ((hremovedClosed ε hε hε1).preimage hη).isOpen_compl.measurableSet
    have hsub : T ∩ Set.uIcc a b ⊆ R := by
      intro t ht
      refine ⟨ht.2, fun hmem => ?_⟩
      obtain ⟨v, hv, htv⟩ := Set.mem_iUnion₂.mp hmem
      exact ht.1 (Set.mem_iUnion₂.mpr ⟨v, hv, interior_subset htv⟩)
    have hint := (MeasureTheory.integrableOn_indicator_iff hT).mpr
      ((hcont.integrableOn_compact (μ := MeasureTheory.volume) hR).mono_set hsub)
    rw [intervalIntegrable_iff']
    convert hint using 1
    ext t
    simp only [T, Set.indicator, Set.mem_compl_iff, Set.mem_preimage]
    split_ifs <;> rfl
  have hfullArcMem : ∀ t ∈ Set.Icc (Real.pi / 3) (2 * Real.pi / 3),
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
    have hhi := Real.cos_le_cos_of_nonneg_of_le_pi (by positivity : 0 ≤ Real.pi / 3)
      htπ.le ht.1
    rw [hcos] at hlo
    rw [Real.cos_pi_div_three] at hhi
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
  let retainedArc : ℝ → ℝ → ℂ := fun ε t =>
    if circleMap 0 1 t ∈ removed ε then 0 else
      L (circleMap 0 1 t) * (Complex.I * circleMap 0 1 t)
  have hretainedArcIntegrable : ∀ ε : ℝ, 0 < ε → ε < 1 →
      IntervalIntegrable (retainedArc ε) MeasureTheory.volume
        (2 * Real.pi / 3) (Real.pi / 3) := by
    intro ε hε hε1
    apply hretainedIntegrable (circleMap 0 1) (fun t => Complex.I * circleMap 0 1 t)
      (2 * Real.pi / 3) (Real.pi / 3) (by fun_prop) (by fun_prop) _ ε hε hε1
    simpa only [Set.uIcc_of_ge (by linarith [Real.pi_pos] : Real.pi / 3 ≤ 2 * Real.pi / 3)]
      using hfullArcMem
  let pairedLower : ℝ → ℂ := fun ε => intervalIntegral
    (fun t : ℝ => if circleMap 0 1 t ∈ removed ε then 0 else
      (L (circleMap 0 1 t) - L (-1 / circleMap 0 1 t) / (circleMap 0 1 t) ^ 2) *
        (Complex.I * circleMap 0 1 t))
    (2 * Real.pi / 3) (Real.pi / 2) MeasureTheory.volume
  have hpairedLowerIntegral : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      pairedLower ε = intervalIntegral (retainedArc ε)
        (2 * Real.pi / 3) (Real.pi / 3) MeasureTheory.volume := by
    filter_upwards [hsmallCuts, hpairedRemoved] with ε hε hpaired
    have hreflect (t : ℝ) : circleMap 0 1 (Real.pi - t) = -1 / circleMap 0 1 t := by
      simp only [circleMap, Complex.ofReal_one, one_mul, zero_add,
        Complex.ofReal_sub, sub_mul, Complex.exp_sub, Complex.exp_pi_mul_I]
    have hint := hretainedArcIntegrable ε hε.1 hε.2
    have hleft : IntervalIntegrable (retainedArc ε) MeasureTheory.volume
        (2 * Real.pi / 3) (Real.pi / 2) :=
      hint.mono_set (c := 2 * Real.pi / 3) (d := Real.pi / 2) (by
        simp only [Set.uIcc_of_ge (by linarith [Real.pi_pos] : Real.pi / 3 ≤ 2 * Real.pi / 3),
          Set.uIcc_of_ge (by linarith [Real.pi_pos] : Real.pi / 2 ≤ 2 * Real.pi / 3)]
        exact Set.Icc_subset_Icc (by linarith [Real.pi_pos]) le_rfl)
    have hright : IntervalIntegrable (retainedArc ε) MeasureTheory.volume
        (Real.pi / 2) (Real.pi / 3) :=
      hint.mono_set (c := Real.pi / 2) (d := Real.pi / 3) (by
        simp only [Set.uIcc_of_ge (by linarith [Real.pi_pos] : Real.pi / 3 ≤ 2 * Real.pi / 3),
          Set.uIcc_of_ge (by linarith [Real.pi_pos] : Real.pi / 3 ≤ Real.pi / 2)]
        exact Set.Icc_subset_Icc le_rfl (by linarith [Real.pi_pos]))
    have hreflectInt : IntervalIntegrable (fun t => retainedArc ε (Real.pi - t))
        MeasureTheory.volume (2 * Real.pi / 3) (Real.pi / 2) := by
      convert hright.symm.comp_sub_left Real.pi using 1 <;> ring
    calc
      pairedLower ε = intervalIntegral
          (fun t => retainedArc ε t + retainedArc ε (Real.pi - t))
          (2 * Real.pi / 3) (Real.pi / 2) MeasureTheory.volume := by
        apply intervalIntegral.integral_congr
        intro t _
        have hnorm : ‖circleMap 0 1 t‖ = 1 := by simp [norm_circleMap_zero]
        have hne : circleMap 0 1 t ≠ 0 := norm_ne_zero_iff.mp (by rw [hnorm]; norm_num)
        have hcut : circleMap 0 1 t ∈ removed ε ↔
            circleMap 0 1 (Real.pi - t) ∈ removed ε := by
          rw [hreflect]
          exact hpaired.1 _ hnorm
        dsimp only [retainedArc]
        by_cases ht : circleMap 0 1 t ∈ removed ε
        · simp only [if_pos ht, if_pos (hcut.mp ht), add_zero]
        · simp only [if_neg ht, if_neg (mt hcut.mpr ht)]
          rw [hreflect]
          field_simp [hne]
          ring
      _ = intervalIntegral (retainedArc ε) (2 * Real.pi / 3) (Real.pi / 2)
            MeasureTheory.volume +
          intervalIntegral (retainedArc ε) (Real.pi / 2) (Real.pi / 3)
            MeasureTheory.volume := by
        rw [intervalIntegral.integral_add hleft hreflectInt,
          intervalIntegral.integral_comp_sub_left]
        congr 2 <;> ring
      _ = _ := intervalIntegral.integral_add_adjacent_intervals hleft hright
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
  filter_upwards [hsmallCuts, hcutZeros, hparametrizedExcisionBoundary, hpairedLowerIntegral,
    hcutsBelowTop, hcutsDisjoint, hcutArcInterior, hcutCircleCoverage] with ε hε hzeros hexc hlower hbelowTop
      hboundaryDisjoint hboundaryArcInterior hboundaryCircleCoverage
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
  rw [hlower]
  -- Instantiate the general-position grid for the actual excised boundary.
  let S : Set ℂ := {z ∈ Ω ε | F z = 0}
  let V : Set ℂ := Ω ε \ ⋃ v ∈ S, Metric.closedBall v r
  let gridCorners : Set ℂ :=
    {ρ, ρ + 1, (-1 / 2 : ℂ) + (Y : ℂ) * Complex.I,
      (1 / 2 : ℂ) + (Y : ℂ) * Complex.I} ∪
    (fun v => γ v ε (cutStart v)) '' B ∪ (fun v => γ v ε (cutEnd v)) '' B
  have hgridCornersFinite : gridCorners.Finite :=
    ((Set.toFinite _).union (hBfinite.image _)).union (hBfinite.image _)
  -- Use a grid scale separating the finitely many genuine contour joins.
  have hseparation : ∀ᶠ d : ℝ in nhdsWithin 0 (Set.Ioi 0),
      ∀ p ∈ gridCorners, ∀ q ∈ gridCorners, p ≠ q → 2 * d < dist p q := by
    rw [hgridCornersFinite.eventually_all]
    intro p _
    rw [hgridCornersFinite.eventually_all]
    intro q _
    by_cases heq : p = q
    · exact Filter.Eventually.of_forall (fun _ h => (h heq).elim)
    · have hpos : (0 : ℝ) < dist p q / 2 := div_pos (dist_pos.mpr heq) (by norm_num)
      filter_upwards [(eventually_lt_nhds hpos).filter_mono nhdsWithin_le_nhds] with d hd
      intro _
      linarith only [hd]
  obtain ⟨d, hd, hdHalf, hsep⟩ := ((show ∀ᶠ d : ℝ in nhdsWithin 0 (Set.Ioi 0), 0 < d from self_mem_nhdsWithin).and
    (((eventually_lt_nhds (show (0 : ℝ) < δ / 2 from by positivity)).filter_mono
      nhdsWithin_le_nhds).and hseparation)).exists
  have hdδ : 2 * d < δ := by linarith only [hdHalf]
  let gridCircles : Set (ℂ × ℝ) :=
    {(0, 1)} ∪ (fun v => (cutCenter v ε, cutRadius v ε)) '' B ∪
      (fun v => (v, r)) '' S
  have hSfinite : S.Finite := by
    simpa only [S, hzeros] using hOzerosFinite
  obtain ⟨_, _, _, _, _, hexcisionDisjoint, hexcisionInside⟩ := hcells
  have hexcisionLocalExterior (v : ℂ) (hv : v ∈ S) (z : ℂ)
      (hz : z ∈ Metric.sphere v r) :
      ∀ᶠ w in nhds z, (w ∈ V ↔ r < ‖w - v‖) :=
    hpuncturedExterior (Ω ε) (hcutOpen ε hε.1 hε.2) S hSfinite r
      hexcisionInside hexcisionDisjoint v hv z hz
  have hexcisionAway (z : ℂ) (hz : z ∉ Ω ε) :
      ∀ᶠ w in nhds z, (w ∈ V ↔ w ∈ Ω ε) := by
    have hopen : IsOpen (⋃ v ∈ S, Metric.closedBall v r)ᶜ :=
      (hSfinite.isClosed_biUnion (fun _ _ => Metric.isClosed_closedBall)).isOpen_compl
    have hzout : z ∈ (⋃ v ∈ S, Metric.closedBall v r)ᶜ := by
      intro hzmem
      obtain ⟨v, hv, hzv⟩ := Set.mem_iUnion₂.mp hzmem
      exact hz (hexcisionInside v hv hzv)
    filter_upwards [hopen.mem_nhds hzout] with w hw
    exact ⟨fun h => h.1, fun h => ⟨h, hw⟩⟩
  have hboundaryCutLocalExterior (v : ℂ) (hv : v ∈ B) (z : ℂ) (hzO : z ∈ O)
      (hz : z ∈ Metric.sphere (cutCenter v ε) (cutRadius v ε)) :
      ∀ᶠ w in nhds z, (w ∈ V ↔ cutRadius v ε < ‖w - cutCenter v ε‖) := by
    have hdisk : D v ε = Metric.closedBall (cutCenter v ε) (cutRadius v ε) :=
      (hdisks v ε (hKH hv.1.1) hε.1 hε.2).1
    have hzD : z ∈ D v ε := by
      rw [hdisk]
      exact Metric.sphere_subset_closedBall hz
    have hznot : z ∉ Ω ε := fun h => h.2 (Set.mem_iUnion₂.mpr ⟨v, hv, hzD⟩)
    let W := O \ ⋃ w ∈ B \ {v}, D w ε
    have hWopen : IsOpen W := by
      apply hOopen.sdiff
      apply (hBfinite.sdiff : (B \ {v}).Finite).isClosed_biUnion
      intro w hw
      rw [show D w ε = Metric.closedBall (cutCenter w ε) (cutRadius w ε) from
        (hdisks w ε (hKH hw.1.1.1) hε.1 hε.2).1]
      exact Metric.isClosed_closedBall
    have hzW : z ∈ W := by
      refine ⟨hzO, ?_⟩
      intro hzother
      obtain ⟨w, hw, hzw⟩ := Set.mem_iUnion₂.mp hzother
      exact Set.disjoint_left.mp
        (hboundaryDisjoint hv.1 hw.1.1 (Ne.symm hw.2)) hzD hzw
    filter_upwards [hWopen.mem_nhds hzW, hexcisionAway z hznot] with w hw haw
    rw [haw]
    constructor
    · intro hmem
      have hn : w ∉ D v ε := fun h => hmem.2 (Set.mem_iUnion₂.mpr ⟨v, hv, h⟩)
      simpa only [hdisk, Metric.mem_closedBall, dist_eq_norm, not_le] using hn
    · intro hnorm
      refine ⟨hw.1, ?_⟩
      intro hmem
      obtain ⟨c, hc, hwc⟩ := Set.mem_iUnion₂.mp hmem
      by_cases hcv : c = v
      · subst c
        exact (not_le_of_gt hnorm)
          (by simpa only [hdisk, Metric.mem_closedBall, dist_eq_norm] using hwc)
      · exact hw.2 (Set.mem_iUnion₂.mpr ⟨c, ⟨hc, hcv⟩, hwc⟩)
  have hgridCornersCountable : gridCorners.Countable :=
    ((Set.to_countable _).union (hBfinite.countable.image _)).union
      (hBfinite.countable.image _)
  have hgridCirclesFinite : gridCircles.Finite :=
    ((Set.finite_singleton _).union (hBfinite.image _)).union (hSfinite.image _)
  -- Include the finite circle seams in the same general-position choice.
  -- Their first and last subdivision pieces then use a single cell primitive.
  obtain ⟨a, hgridAvoid, hgridTangencies, hgridVertices⟩ :=
    hgridChoice d (gridCorners ∪ (fun v => circleMap v r 0) '' S) gridCircles
      (hgridCornersCountable.union (hSfinite.countable.image _)) hgridCirclesFinite.countable
  have hgridCorners (p : ℂ) (hp : p ∈ gridCorners) (n : ℤ) :
      a.re + n * d ≠ p.re ∧ a.im + n * d ≠ p.im := hgridAvoid p (Or.inl hp) n
  have hgridCircleSeams (v : ℂ) (hv : v ∈ S) (n : ℤ) :
      a.re + n * d ≠ (circleMap v r 0).re ∧ a.im + n * d ≠ (circleMap v r 0).im :=
    hgridAvoid (circleMap v r 0) (Or.inr ⟨v, hv, rfl⟩) n
  let gridSquare : ℤ × ℤ → Set ℂ := fun i => {z |
    a.re + (i.1 : ℝ) * d ≤ z.re ∧ z.re ≤ a.re + ((i.1 : ℝ) + 1) * d ∧
    a.im + (i.2 : ℝ) * d ≤ z.im ∧ z.im ≤ a.im + ((i.2 : ℝ) + 1) * d}
  have hgridCornerUnique (i : ℤ × ℤ) (p q : ℂ) (hp : p ∈ gridCorners) (hq : q ∈ gridCorners)
      (hpi : p ∈ gridSquare i) (hqi : q ∈ gridSquare i) : p = q := by
    by_contra hne
    have hre : |p.re - q.re| ≤ d := abs_le.mpr ⟨by linarith only [hpi.1, hqi.2.1],
      by linarith only [hpi.2.1, hqi.1]⟩
    have him : |p.im - q.im| ≤ d := abs_le.mpr ⟨by linarith only [hpi.2.2.1, hqi.2.2.2],
      by linarith only [hpi.2.2.2, hqi.2.2.1]⟩
    have hbound : dist p q ≤ 2 * d := by
      rw [dist_eq_norm]
      calc
        _ ≤ |(p - q).re| + |(p - q).im| := Complex.norm_le_abs_re_add_abs_im _
        _ ≤ d + d := add_le_add hre him
        _ = 2 * d := by ring
    exact (not_lt_of_ge hbound) (hsep p hp q hq hne)
  have hgridCellUnique (z : ℂ)
      (havoid : ∀ n : ℤ, a.re + n * d ≠ z.re ∧ a.im + n * d ≠ z.im)
      (i j : ℤ × ℤ) (hi : z ∈ gridSquare i) (hj : z ∈ gridSquare j) : i = j := by
    have hindex (x o : ℝ) (m n : ℤ)
        (hm : o + (m : ℝ) * d ≤ x ∧ x ≤ o + ((m : ℝ) + 1) * d)
        (hn : o + (n : ℝ) * d ≤ x ∧ x ≤ o + ((n : ℝ) + 1) * d)
        (hnot : ∀ q : ℤ, o + q * d ≠ x) : m = n := by
      have hmUpper : x < o + ((m : ℝ) + 1) * d :=
        lt_of_le_of_ne hm.2 (by simpa only [Int.cast_add, Int.cast_one] using (hnot (m + 1)).symm)
      have hnUpper : x < o + ((n : ℝ) + 1) * d :=
        lt_of_le_of_ne hn.2 (by simpa only [Int.cast_add, Int.cast_one] using (hnot (n + 1)).symm)
      apply le_antisymm
      · by_contra hmn
        have hle : n + 1 ≤ m := by omega
        have hmul : ((n : ℝ) + 1) * d ≤ (m : ℝ) * d :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hle) hd.le
        linarith only [hm.1, hnUpper, hmul]
      · by_contra hnm
        have hle : m + 1 ≤ n := by omega
        have hmul : ((m : ℝ) + 1) * d ≤ (n : ℝ) * d :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hle) hd.le
        linarith only [hn.1, hmUpper, hmul]
    exact Prod.ext
      (hindex z.re a.re i.1 j.1 ⟨hi.1, hi.2.1⟩ ⟨hj.1, hj.2.1⟩ (fun n => (havoid n).1))
      (hindex z.im a.im i.2 j.2 ⟨hi.2.2.1, hi.2.2.2⟩ ⟨hj.2.2.1, hj.2.2.2⟩
        (fun n => (havoid n).2))
  let gridCells : Set (ℤ × ℤ) := {i | (closure V ∩ gridSquare i).Nonempty}
  obtain ⟨hgridFinite, hgridCover, hgridPrimitives⟩ :
      gridCells.Finite ∧ closure V ⊆ ⋃ i ∈ gridCells, gridSquare i ∧
        ∀ i ∈ gridCells, Complex.IsExactOn L (gridSquare i) :=
    htranslatedMesh (closure V) hVcompact δ d hd hdδ hmesh a
  -- Fix one primitive in each occupied cell, normalized at its unique
  -- genuine contour join when the cell contains one.
  let cellAnchor : (ℤ × ℤ) → ℂ := fun i =>
    if h : ∃ z ∈ gridCorners, z ∈ gridSquare i then Classical.choose h else 0
  let cellPrimitive : (ℤ × ℤ) → ℂ → ℂ := fun i =>
    if hi : i ∈ gridCells then fun z => Classical.choose (hgridPrimitives i hi) z -
      Classical.choose (hgridPrimitives i hi) (cellAnchor i)
    else fun _ => 0
  have hcellPrimitive (i : ℤ × ℤ) (hi : i ∈ gridCells) :
      ∀ z ∈ gridSquare i, HasDerivAt (cellPrimitive i) (L z) z := by
    intro z hz
    simpa only [cellPrimitive, dif_pos hi] using
      (Classical.choose_spec (hgridPrimitives i hi) z hz).sub_const
        (Classical.choose (hgridPrimitives i hi) (cellAnchor i))
  have hcellPrimitiveJoin (i : ℤ × ℤ) (z : ℂ) (hz : z ∈ gridCorners)
      (hzi : z ∈ gridSquare i) : cellPrimitive i z = 0 := by
    have hex : ∃ w ∈ gridCorners, w ∈ gridSquare i := ⟨z, hz, hzi⟩
    have hanchor : cellAnchor i = z := by
      dsimp only [cellAnchor]
      rw [dif_pos hex]
      exact hgridCornerUnique i _ z (Classical.choose_spec hex).1 hz
        (Classical.choose_spec hex).2 hzi
    by_cases hi : i ∈ gridCells
    · simp only [cellPrimitive, dif_pos hi, hanchor, sub_self]
    · simp only [cellPrimitive, dif_neg hi]
  let gridVertex : ℤ × ℤ → ℂ := fun i =>
    ((a.re + i.1 * d : ℝ) : ℂ) + ((a.im + i.2 * d : ℝ) : ℂ) * Complex.I
  have hgridVerticalLeft : ∀ n : ℤ, a.re + n * d ≠ -1 / 2 := by
    intro n
    simpa only [hρre] using
      (hgridCorners ρ (Or.inl (Or.inl (by simp))) n).1
  have hgridVerticalRight : ∀ n : ℤ, a.re + n * d ≠ 1 / 2 := by
    intro n
    have hp := (hgridCorners (ρ + 1) (Or.inl (Or.inl (by simp))) n).1
    have hre : (ρ + 1).re = 1 / 2 := by rw [Complex.add_re, hρre, Complex.one_re]; ring
    simpa only [hre] using hp
  have hgridHorizontalTop : ∀ n : ℤ, a.im + n * d ≠ Y := by
    intro n
    simpa using
      (hgridCorners ((1 / 2 : ℂ) + (Y : ℂ) * Complex.I)
        (Or.inl (Or.inl (by simp))) n).2
  have hgridBoundarySupport : frontier V ⊆
      (({z : ℂ | z.re = -1 / 2} ∪ {z : ℂ | z.re = 1 / 2}) ∪ {z : ℂ | z.im = Y}) ∪
        ⋃ c ∈ gridCircles, {z : ℂ | ‖z - c.1‖ = c.2} := by
    intro z hi
    have hfront : frontier V =
        ((⋃ i : Fin 4, closure (Ω ε) ∩ outerSupport i) ∪
          ⋃ v ∈ B, γ v ε '' Set.Icc (cutEnd v) (cutStart v)) ∪
        ⋃ v ∈ S, Metric.sphere v r := by
      simpa only [V, S, Set.mem_ofPred_eq] using hVfrontier
    rw [hfront] at hi
    rcases hi with (hi | hi) | hi
    · obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hi
      fin_cases j
      · exact Or.inr (Set.mem_iUnion₂.mpr ⟨(0, 1), Or.inl (Or.inl (by simp)),
          by simpa only [Set.mem_ofPred_eq, sub_zero] using (show ‖z‖ = 1 from hj.2)⟩)
      · exact Or.inl (Or.inl (Or.inr hj.2))
      · exact Or.inl (Or.inr hj.2)
      · exact Or.inl (Or.inl (Or.inl hj.2))
    · obtain ⟨v, hv, t, _, ht⟩ := Set.mem_iUnion₂.mp hi
      have hsphere := hgammaSphere v (hKH hv.1.1) ε hε.1 hε.2 t
      rw [ht] at hsphere
      exact Or.inr (Set.mem_iUnion₂.mpr ⟨(cutCenter v ε, cutRadius v ε),
        Or.inl (Or.inr ⟨v, hv, rfl⟩),
        by simpa only [Set.mem_ofPred_eq, Metric.mem_sphere, dist_eq_norm] using hsphere⟩)
    · obtain ⟨v, hv, hsphere⟩ := Set.mem_iUnion₂.mp hi
      exact Or.inr (Set.mem_iUnion₂.mpr ⟨(v, r), Or.inr ⟨v, hv, rfl⟩,
        by simpa only [Set.mem_ofPred_eq, Metric.mem_sphere, dist_eq_norm] using hsphere⟩)
  have hgridVerticesAvoidFrontier : ∀ i : ℤ × ℤ, gridVertex i ∉ frontier V := by
    intro i hi
    rcases hgridBoundarySupport hi with ((hi | hi) | hi) | hi
    · exact hgridVerticalLeft i.1 (by simpa [gridVertex] using hi)
    · exact hgridVerticalRight i.1 (by simpa [gridVertex] using hi)
    · exact hgridHorizontalTop i.2 (by simpa [gridVertex] using hi)
    · obtain ⟨c, hc, hi⟩ := Set.mem_iUnion₂.mp hi
      exact hgridVertices c hc i.1 i.2 hi
  have hgridTransverse : ∀ c ∈ gridCircles, ∀ n : ℤ, ∀ z ∈ Metric.sphere c.1 c.2,
      (z.re = a.re + n * d → z.im ≠ c.1.im) ∧
      (z.im = a.im + n * d → z.re ≠ c.1.re) := by
    intro c hc n z hz
    have ht := hgridTangencies c hc n
    have hs := hcircleTransverse c.1 z c.2
      (by simpa only [Metric.mem_sphere, dist_eq_norm] using hz)
    constructor
    · intro heq
      exact hs.1 (by simpa only [heq] using ht.1) (by simpa only [heq] using ht.2.1)
    · intro heq
      exact hs.2 (by simpa only [heq] using ht.2.2.1) (by simpa only [heq] using ht.2.2.2)
  have hgridVerticalIntersections : ∀ n : ℤ,
      {z ∈ frontier V | z.re = a.re + n * d}.Finite := by
    intro n
    let x := a.re + n * d
    have htop : {z : ℂ | z.im = Y ∧ z.re = x}.Finite := by
      apply (Set.finite_singleton ((x : ℂ) + (Y : ℂ) * Complex.I)).subset
      intro z hz
      apply Complex.ext
      · simpa using hz.2
      · simpa using hz.1
    apply (htop.union (hgridCirclesFinite.biUnion
      (fun c _ => hcircleVerticalFinite c.1 c.2 x))).subset
    rintro z ⟨hz, hzx⟩
    rcases hgridBoundarySupport hz with ((hl | hr) | ht) | hc
    · exact False.elim (hgridVerticalLeft n (hzx ▸ hl))
    · exact False.elim (hgridVerticalRight n (hzx ▸ hr))
    · exact Or.inl ⟨ht, hzx⟩
    · obtain ⟨c, hc, hzc⟩ := Set.mem_iUnion₂.mp hc
      exact Or.inr (Set.mem_iUnion₂.mpr ⟨c, hc, hzc, hzx⟩)
  have hgridHorizontalIntersections : ∀ n : ℤ,
      {z ∈ frontier V | z.im = a.im + n * d}.Finite := by
    intro n
    let y := a.im + n * d
    have hside (x : ℝ) : {z : ℂ | z.re = x ∧ z.im = y}.Finite := by
      apply (Set.finite_singleton ((x : ℂ) + (y : ℂ) * Complex.I)).subset
      intro z hz
      apply Complex.ext
      · simpa using hz.1
      · simpa using hz.2
    apply (((hside (-1 / 2)).union (hside (1 / 2))).union
      (hgridCirclesFinite.biUnion (fun c _ => hcircleHorizontalFinite c.1 c.2 y))).subset
    rintro z ⟨hz, hzy⟩
    rcases hgridBoundarySupport hz with ((hl | hr) | ht) | hc
    · exact Or.inl (Or.inl ⟨hl, hzy⟩)
    · exact Or.inl (Or.inr ⟨hr, hzy⟩)
    · exact False.elim (hgridHorizontalTop n (hzy ▸ ht))
    · obtain ⟨c, hc, hzc⟩ := Set.mem_iUnion₂.mp hc
      exact Or.inr (Set.mem_iUnion₂.mpr ⟨c, hc, hzc, hzy⟩)
  have hgridCrossingsFinite : (⋃ i ∈ gridCells,
      ({z ∈ frontier V | z.re = a.re + (i.1 : ℝ) * d} ∪
       {z ∈ frontier V | z.re = a.re + ((i.1 + 1 : ℤ) : ℝ) * d}) ∪
      ({z ∈ frontier V | z.im = a.im + (i.2 : ℝ) * d} ∪
       {z ∈ frontier V | z.im = a.im + ((i.2 + 1 : ℤ) : ℝ) * d})).Finite :=
    hgridFinite.biUnion (fun i _ =>
      ((hgridVerticalIntersections i.1).union (hgridVerticalIntersections (i.1 + 1))).union
        ((hgridHorizontalIntersections i.2).union (hgridHorizontalIntersections (i.2 + 1))))
  -- Give the translated squares their counterclockwise edge parameterizations.
  let cellNext : Equiv.Perm (Fin 4) := Equiv.addRight 1
  let cellVertex : (ℤ × ℤ) → Fin 4 → ℂ := fun i =>
    ![gridVertex i, gridVertex (i.1 + 1, i.2),
      gridVertex (i.1 + 1, i.2 + 1), gridVertex (i.1, i.2 + 1)]
  let cellEdge : (ℤ × ℤ) → Fin 4 → ℝ → ℂ := fun i j t =>
    cellVertex i j + (t : ℂ) * (cellVertex i (cellNext j) - cellVertex i j)
  let cellVelocity : (ℤ × ℤ) → Fin 4 → ℂ := fun i j =>
    cellVertex i (cellNext j) - cellVertex i j
  have hcellConvex (i : ℤ × ℤ) : Convex ℝ (gridSquare i) :=
    (convex_halfSpace_re_ge _).inter ((convex_halfSpace_re_le _).inter
      ((convex_halfSpace_im_ge _).inter (convex_halfSpace_im_le _)))
  have hcellVertices (i : ℤ × ℤ) (j : Fin 4) : cellVertex i j ∈ gridSquare i := by
    fin_cases j <;> norm_num [cellVertex, gridVertex, gridSquare] <;>
      (try constructor) <;> nlinarith [hd]
  have hcellEdgeMem (i : ℤ × ℤ) (j : Fin 4) (t : ℝ) (ht : t ∈ Set.Icc 0 1) :
      cellEdge i j t ∈ gridSquare i := by
    have h := hcellConvex i (hcellVertices i j) (hcellVertices i (cellNext j))
      (sub_nonneg.mpr ht.2) ht.1 (by ring : 1 - t + t = 1)
    convert h using 1
    simp only [cellEdge, Complex.real_smul, Complex.ofReal_sub, Complex.ofReal_one]
    ring
  have hcellEdgeDeriv (i : ℤ × ℤ) (j : Fin 4) (t : ℝ) :
      HasDerivAt (cellEdge i j) (cellVelocity i j) t := by
    simpa only [cellEdge, cellVelocity, Complex.ofReal_one, one_mul, id_eq] using
      (((hasDerivAt_id t).ofReal_comp).mul_const
        (cellVertex i (cellNext j) - cellVertex i j)).const_add (cellVertex i j)
  have hcellEdgeEndpoints (i : ℤ × ℤ) (j : Fin 4) :
      cellEdge i j 0 = cellVertex i j ∧
        cellEdge i j 1 = cellVertex i (cellNext j) := by
    simp [cellEdge]
  have hcellEdgeBalance (i : ℤ × ℤ) (j : Fin 4) :
      cellEdge i j 1 = cellEdge i (cellNext j) 0 := by
    rw [(hcellEdgeEndpoints i j).2, (hcellEdgeEndpoints i (cellNext j)).1]
  have hcellBoundarySides (i : ℤ × ℤ) :
      (⋃ j : Fin 4, cellEdge i j '' Set.Icc 0 1) =
        {z ∈ gridSquare i | z.re = a.re + (i.1 : ℝ) * d ∨
          z.re = a.re + ((i.1 : ℝ) + 1) * d ∨
          z.im = a.im + (i.2 : ℝ) * d ∨
          z.im = a.im + ((i.2 : ℝ) + 1) * d} := by
    have hedge (j : Fin 4) (t : ℝ) : cellEdge i j t =
        ![gridVertex i + (t * d : ℝ),
          gridVertex (i.1 + 1, i.2) + (t * d : ℝ) * Complex.I,
          gridVertex (i.1 + 1, i.2 + 1) - (t * d : ℝ),
          gridVertex (i.1, i.2 + 1) - (t * d : ℝ) * Complex.I] j := by
      fin_cases j <;> norm_num [cellEdge, cellVertex, cellNext, Equiv.addRight,
        gridVertex, Fin.add_def]
      all_goals ring_nf
      all_goals simp
    ext z
    constructor
    · intro hz
      obtain ⟨j, t, ht, rfl⟩ := Set.mem_iUnion.mp hz
      refine ⟨hcellEdgeMem i j t ht, ?_⟩
      rw [hedge]
      fin_cases j <;> simp [gridVertex]
    · rintro ⟨hz, hside⟩
      have hx : a.re + (i.1 : ℝ) * d ≤ z.re ∧
          z.re ≤ a.re + ((i.1 : ℝ) + 1) * d := ⟨hz.1, hz.2.1⟩
      have hy : a.im + (i.2 : ℝ) * d ≤ z.im ∧
          z.im ≤ a.im + ((i.2 : ℝ) + 1) * d := hz.2.2
      have hquot (x l : ℝ) (hl : l ≤ x) (hu : x ≤ l + d) :
          (x - l) / d ∈ Set.Icc 0 1 :=
        ⟨div_nonneg (sub_nonneg.mpr hl) hd.le, (div_le_one hd).mpr (by linarith)⟩
      rcases hside with hx0 | hx1 | hy0 | hy1
      · refine Set.mem_iUnion.mpr ⟨3,
          (a.im + ((i.2 : ℝ) + 1) * d - z.im) / d, ?_, ?_⟩
        · constructor
          · exact div_nonneg (sub_nonneg.mpr hy.2) hd.le
          · apply (div_le_one hd).mpr
            linarith [hy.1]
        · rw [hedge]
          apply Complex.ext <;> simp [gridVertex, hx0, div_mul_cancel₀ _ hd.ne']
      · refine Set.mem_iUnion.mpr ⟨1, (z.im - (a.im + (i.2 : ℝ) * d)) / d,
          hquot _ _ hy.1 (by nlinarith [hy.2]), ?_⟩
        rw [hedge]
        apply Complex.ext <;> simp [gridVertex, hx1, div_mul_cancel₀ _ hd.ne']
      · refine Set.mem_iUnion.mpr ⟨0, (z.re - (a.re + (i.1 : ℝ) * d)) / d,
          hquot _ _ hx.1 (by nlinarith [hx.2]), ?_⟩
        rw [hedge]
        apply Complex.ext <;> simp [gridVertex, hy0, div_mul_cancel₀ _ hd.ne']
      · refine Set.mem_iUnion.mpr ⟨2,
          (a.re + ((i.1 : ℝ) + 1) * d - z.re) / d, ?_, ?_⟩
        · constructor
          · exact div_nonneg (sub_nonneg.mpr hx.2) hd.le
          · apply (div_le_one hd).mpr
            linarith [hx.1]
        · rw [hedge]
          apply Complex.ext <;> simp [gridVertex, hy1, div_mul_cancel₀ _ hd.ne']
  -- A relevant square missing the genuine boundary is wholly occupied.
  have hcellFrontier (i : ℤ × ℤ) :
      frontier (gridSquare i) = ⋃ j : Fin 4, cellEdge i j '' Set.Icc 0 1 := by
    have hx : a.re + (i.1 : ℝ) * d ≤ a.re + ((i.1 : ℝ) + 1) * d := by linarith
    have hy : a.im + (i.2 : ℝ) * d ≤ a.im + ((i.2 : ℝ) + 1) * d := by linarith
    have hrect : gridSquare i = Complex.reProdIm
        (Set.Icc (a.re + (i.1 : ℝ) * d) (a.re + ((i.1 : ℝ) + 1) * d))
        (Set.Icc (a.im + (i.2 : ℝ) * d) (a.im + ((i.2 : ℝ) + 1) * d)) := by
      ext z
      simp only [gridSquare, Set.mem_ofPred_eq, Complex.mem_reProdIm, Set.mem_Icc]
      tauto
    rw [hcellBoundarySides, hrect, Complex.frontier_reProdIm,
      closure_Icc, closure_Icc, frontier_Icc hx, frontier_Icc hy]
    ext z
    simp only [Set.mem_union, Complex.mem_reProdIm, Set.mem_Icc, Set.mem_insert_iff,
      Set.mem_singleton_iff, Set.mem_ofPred_eq]
    constructor
    · rintro (⟨hzx, hzy | hzy⟩ | ⟨hzx | hzx, hzy⟩)
      · exact ⟨⟨hzx, by rw [hzy]; exact ⟨le_rfl, hy⟩⟩, Or.inr (Or.inr (Or.inl hzy))⟩
      · exact ⟨⟨hzx, by rw [hzy]; exact ⟨hy, le_rfl⟩⟩, Or.inr (Or.inr (Or.inr hzy))⟩
      · exact ⟨⟨by rw [hzx]; exact ⟨le_rfl, hx⟩, hzy⟩, Or.inl hzx⟩
      · exact ⟨⟨by rw [hzx]; exact ⟨hx, le_rfl⟩, hzy⟩, Or.inr (Or.inl hzx)⟩
    · rintro ⟨⟨hzx, hzy⟩, h | h | h | h⟩
      · exact Or.inr ⟨Or.inl h, hzy⟩
      · exact Or.inr ⟨Or.inr h, hzy⟩
      · exact Or.inl ⟨hzx, Or.inl h⟩
      · exact Or.inl ⟨hzx, Or.inr h⟩
  have hcellOccupied (i : ℤ × ℤ) (hi : i ∈ gridCells)
      (havoid : Disjoint (gridSquare i) (frontier V)) : gridSquare i ⊆ V := by
    have hcover : gridSquare i ⊆ V ∪ (closure V)ᶜ := by
      intro z hz
      by_cases hzV : z ∈ V
      · exact Or.inl hzV
      · exact Or.inr (fun hzcl => Set.disjoint_left.mp havoid hz
          ⟨hzcl, fun hzint => hzV (interior_subset hzint)⟩)
    have hdisjoint : Disjoint V (closure V)ᶜ :=
      Set.disjoint_left.mpr (fun _ hz hn => hn (subset_closure hz))
    rcases (hcellConvex i).isPreconnected.subset_or_subset hVopen
      isClosed_closure.isOpen_compl hdisjoint hcover with hinside | houtside
    · exact hinside
    · obtain ⟨z, hzcl, hzcell⟩ := hi
      exact False.elim (houtside hzcell hzcl)
  have hoccupiedCellBoundary (i : ℤ × ℤ) (hi : i ∈ gridCells)
      (havoid : Disjoint (gridSquare i) (frontier V)) :
      frontier (V ∩ gridSquare i) = ⋃ j : Fin 4, cellEdge i j '' Set.Icc 0 1 := by
    rw [Set.inter_eq_right.mpr (hcellOccupied i hi havoid)]
    exact hcellFrontier i
  have hoccupiedCellIntegral (i : ℤ × ℤ) (hi : i ∈ gridCells)
      (havoid : Disjoint (gridSquare i) (frontier V)) :
      (∀ j : Fin 4, ∀ t ∈ Set.Icc (0 : ℝ) 1, cellEdge i j t ∈ V) ∧
        (∑ j : Fin 4, intervalIntegral
          (fun t => L (cellEdge i j t) * cellVelocity i j) 0 1 MeasureTheory.volume) = 0 := by
    have hinside := hcellOccupied i hi havoid
    have hLc : ContinuousOn L (gridSquare i) := by
      intro z hz
      exact (hLan z (hKH (hcutClosureK ε (subset_closure (hinside hz).1)))
        (hVzeroFree z (subset_closure (hinside hz)))).continuousAt.continuousWithinAt
    have hint (j : Fin 4) : IntervalIntegrable
        (fun t => L (cellEdge i j t) * cellVelocity i j) MeasureTheory.volume 0 1 := by
      have hη : Continuous (cellEdge i j) :=
        continuous_iff_continuousAt.mpr (fun t => (hcellEdgeDeriv i j t).continuousAt)
      exact ((hLc.comp hη.continuousOn (fun t ht => hcellEdgeMem i j t ht)).mul
        continuousOn_const).intervalIntegrable_of_Icc (by norm_num)
    obtain ⟨g, hg⟩ := hgridPrimitives i hi
    refine ⟨fun j t ht => hinside (hcellEdgeMem i j t ht), ?_⟩
    exact hprimitiveCycles (gridSquare i) g hg 4 cellNext (cellEdge i)
      (fun j _ => cellVelocity i j) (fun _ => 0) (fun _ => 1)
      (fun j t ht => hcellEdgeMem i j t (by simpa using ht))
      (fun j t _ => hcellEdgeDeriv i j t) hint (hcellEdgeBalance i)
  -- Every occupied artificial grid edge has the opposite orientation in its
  -- adjacent square, including squares crossed by the genuine boundary.
  let cellAcross : (ℤ × ℤ) → Fin 4 → ℤ × ℤ := fun i =>
    ![(i.1, i.2 - 1), (i.1 + 1, i.2), (i.1, i.2 + 1), (i.1 - 1, i.2)]
  let cellOpp : Fin 4 → Fin 4 := fun j => j + 2
  have hcellAcrossInvol (i : ℤ × ℤ) (j : Fin 4) :
      cellAcross (cellAcross i j) (cellOpp j) = i ∧ cellOpp (cellOpp j) = j := by
    fin_cases j <;> simp [cellAcross, cellOpp, Fin.add_def]
  have hcellOppNe (j : Fin 4) : cellOpp j ≠ j := by
    fin_cases j <;> decide
  have hcellAcrossPath (i : ℤ × ℤ) (j : Fin 4) (t : ℝ) :
      cellEdge (cellAcross i j) (cellOpp j) (1 - t) = cellEdge i j t := by
    fin_cases j <;> norm_num [cellEdge, cellVertex, cellNext, cellAcross, cellOpp,
      Equiv.addRight, gridVertex, Fin.add_def] <;> ring
  have hcellAcrossVelocity (i : ℤ × ℤ) (j : Fin 4) :
      cellVelocity (cellAcross i j) (cellOpp j) = -cellVelocity i j := by
    fin_cases j <;> norm_num [cellVelocity, cellVertex, cellNext, cellAcross, cellOpp,
      Equiv.addRight, gridVertex, Fin.add_def]
  let occupiedEdge : (ℤ × ℤ) → Fin 4 → ℝ → ℂ := fun i j t =>
    if cellEdge i j t ∈ V then L (cellEdge i j t) * cellVelocity i j else 0
  let occupiedEdgeIntegral : (ℤ × ℤ) → Fin 4 → ℂ := fun i j =>
    intervalIntegral (occupiedEdge i j) 0 1 MeasureTheory.volume
  have hoccupiedEdgeIntegrable (i : ℤ × ℤ) (j : Fin 4) :
      IntervalIntegrable (occupiedEdge i j) MeasureTheory.volume 0 1 := by
    have hη : Continuous (cellEdge i j) :=
      continuous_iff_continuousAt.mpr (fun t => (hcellEdgeDeriv i j t).continuousAt)
    let R : Set ℝ := Set.Icc 0 1 ∩ cellEdge i j ⁻¹' closure V
    have hR : IsCompact R := isCompact_Icc.inter_right (isClosed_closure.preimage hη)
    have hcont : ContinuousOn (fun t => L (cellEdge i j t) * cellVelocity i j) R := by
      intro t ht
      have hK : cellEdge i j t ∈ K :=
        hcutClosureK ε ((closure_mono (show V ⊆ Ω ε from fun _ hz => hz.1)) ht.2)
      exact (((hLan _ (hKH hK) (hVzeroFree _ ht.2)).continuousAt.comp
        hη.continuousAt).mul continuousAt_const).continuousWithinAt
    let T : Set ℝ := cellEdge i j ⁻¹' V
    have hT : MeasurableSet T := (hVopen.preimage hη).measurableSet
    have hsub : T ∩ Set.uIcc (0 : ℝ) 1 ⊆ R := by
      intro t ht
      exact ⟨by simpa using ht.2, subset_closure ht.1⟩
    have hint := (MeasureTheory.integrableOn_indicator_iff hT).mpr
      ((hcont.integrableOn_compact (μ := MeasureTheory.volume) hR).mono_set hsub)
    rw [intervalIntegrable_iff']
    convert hint using 1
    ext t
    simp only [occupiedEdge, T, Set.indicator, Set.mem_preimage]
  have hoccupiedEdgePair (i : ℤ × ℤ) (j : Fin 4) :
      occupiedEdgeIntegral i j + occupiedEdgeIntegral (cellAcross i j) (cellOpp j) = 0 := by
    have heq : (fun t => occupiedEdge (cellAcross i j) (cellOpp j) (1 - t)) =
        fun t => -occupiedEdge i j t := by
      funext t
      simp only [occupiedEdge, hcellAcrossPath, hcellAcrossVelocity]
      split_ifs <;> simp
    have hreflect := intervalIntegral.integral_comp_sub_left
      (occupiedEdge (cellAcross i j) (cellOpp j)) (a := (0 : ℝ)) (b := 1) 1
    rw [heq, intervalIntegral.integral_neg] at hreflect
    have hneg : occupiedEdgeIntegral (cellAcross i j) (cellOpp j) =
        -occupiedEdgeIntegral i j := by
      simpa only [occupiedEdgeIntegral, sub_self, sub_zero] using hreflect.symm
    rw [hneg, add_neg_cancel]
  have hoccupiedEdgeNeighbor (i : ℤ × ℤ) (j : Fin 4)
      (hne : occupiedEdgeIntegral i j ≠ 0) : cellAcross i j ∈ gridCells := by
    by_contra hout
    apply hne
    calc
      _ = intervalIntegral (fun _ : ℝ => (0 : ℂ)) 0 1 MeasureTheory.volume := by
        apply intervalIntegral.integral_congr
        intro t ht
        have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by simpa using ht
        have hnot : cellEdge i j t ∉ V := by
          intro hv
          apply hout
          refine ⟨cellEdge i j t, subset_closure hv, ?_⟩
          rw [← hcellAcrossPath i j t]
          exact hcellEdgeMem _ _ _ ⟨by linarith [ht'.2], by linarith [ht'.1]⟩
        simp only [if_neg hnot]
      _ = 0 := intervalIntegral.integral_zero
  have hartificialEdgesCancel :
      ∑ i ∈ hgridFinite.toFinset, ∑ j : Fin 4, occupiedEdgeIntegral i j = 0 := by
    let edges : Finset ((ℤ × ℤ) × Fin 4) := hgridFinite.toFinset ×ˢ Finset.univ
    let value : ((ℤ × ℤ) × Fin 4) → ℂ := fun p => occupiedEdgeIntegral p.1 p.2
    let active := edges.filter (fun p => value p ≠ 0)
    let swapEdge : ((ℤ × ℤ) × Fin 4) → ((ℤ × ℤ) × Fin 4) :=
      fun p => (cellAcross p.1 p.2, cellOpp p.2)
    have hmem (p : (ℤ × ℤ) × Fin 4) (hp : p ∈ active) : swapEdge p ∈ active := by
      obtain ⟨_, hpne⟩ := Finset.mem_filter.mp hp
      refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · exact Finset.mem_product.mpr
          ⟨hgridFinite.mem_toFinset.mpr (hoccupiedEdgeNeighbor p.1 p.2 hpne), Finset.mem_univ _⟩
      · intro hz
        have hpair := hoccupiedEdgePair p.1 p.2
        change value p + value (swapEdge p) = 0 at hpair
        rw [hz, add_zero] at hpair
        exact hpne hpair
    have hsum : ∑ p ∈ active, value p = 0 := by
      apply Finset.sum_involution (fun p _ => swapEdge p)
      · intro p _
        exact hoccupiedEdgePair p.1 p.2
      · intro p _ _ heq
        exact hcellOppNe p.2 (congrArg Prod.snd heq)
      · exact hmem
      · intro p _
        exact Prod.ext (hcellAcrossInvol p.1 p.2).1 (hcellAcrossInvol p.1 p.2).2
    simpa only [active, Finset.sum_filter_ne_zero, edges, Finset.sum_product, value] using hsum
  have hoccupiedCellRetainedIntegral (i : ℤ × ℤ) (hi : i ∈ gridCells)
      (havoid : Disjoint (gridSquare i) (frontier V)) :
      ∑ j : Fin 4, occupiedEdgeIntegral i j = 0 := by
    obtain ⟨hmem, hsum⟩ := hoccupiedCellIntegral i hi havoid
    convert hsum using 1
    apply Finset.sum_congr rfl
    intro j _
    apply intervalIntegral.integral_congr
    intro t ht
    exact if_pos (hmem j t (by simpa using ht))
  let boundaryCells : Finset (ℤ × ℤ) :=
    hgridFinite.toFinset.filter (fun i => ¬Disjoint (gridSquare i) (frontier V))
  have hboundaryCellIntegralsCancel :
      ∑ i ∈ boundaryCells, ∑ j : Fin 4, occupiedEdgeIntegral i j = 0 := by
    calc
      _ = ∑ i ∈ hgridFinite.toFinset, ∑ j : Fin 4, occupiedEdgeIntegral i j := by
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro i hi hnot
        have havoid : Disjoint (gridSquare i) (frontier V) := by
          by_contra hn
          exact hnot (Finset.mem_filter.mpr ⟨hi, hn⟩)
        exact hoccupiedCellRetainedIntegral i (hgridFinite.mem_toFinset.mp hi) havoid
      _ = 0 := hartificialEdgesCancel
  -- Subdivide each raw grid edge at its actual genuine-boundary crossings.
  -- Keeping the raw cell, side and parameter interval preserves the two
  -- adjacent primitive domains and the reversal map needed at each crossing.
  have hcellVelocityNe (i : ℤ × ℤ) (j : Fin 4) : cellVelocity i j ≠ 0 := by
    have heq : cellVelocity i j =
        ![(d : ℂ), (d : ℂ) * Complex.I, -(d : ℂ), -(d : ℂ) * Complex.I] j := by
      fin_cases j <;> norm_num [cellVelocity, cellVertex, cellNext, Equiv.addRight,
        gridVertex, Fin.add_def] <;> ring
    rw [heq]
    have hdC : (d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hd.ne'
    fin_cases j <;> simp [hdC, Complex.I_ne_zero]
  have hcellEdgeInjective (i : ℤ × ℤ) (j : Fin 4) : Function.Injective (cellEdge i j) := by
    intro s t hst
    apply Complex.ofReal_injective
    exact mul_right_cancel₀ (hcellVelocityNe i j) (add_left_cancel hst)
  have hcellEdgeContinuous (i : ℤ × ℤ) (j : Fin 4) : Continuous (cellEdge i j) :=
    continuous_iff_continuousAt.mpr (fun t => (hcellEdgeDeriv i j t).continuousAt)
  have hcellCircleNormalNe (i : ℤ × ℤ) (j : Fin 4) (t : ℝ)
      (c : ℂ × ℝ) (hc : c ∈ gridCircles)
      (hz : cellEdge i j t ∈ Metric.sphere c.1 c.2) :
      (cellEdge i j t - c.1).re * (cellVelocity i j).re +
        (cellEdge i j t - c.1).im * (cellVelocity i j).im ≠ 0 := by
    have hvelocity : cellVelocity i j =
        ![(d : ℂ), (d : ℂ) * Complex.I, -(d : ℂ), -(d : ℂ) * Complex.I] j := by
      fin_cases j <;> norm_num [cellVelocity, cellVertex, cellNext, Equiv.addRight,
        gridVertex, Fin.add_def] <;> ring
    rw [hvelocity]
    fin_cases j
    · have hline : (cellEdge i 0 t).im = a.im + (i.2 : ℝ) * d := by
        norm_num [cellEdge, cellVertex, cellNext, Equiv.addRight, gridVertex, Fin.add_def]
      have hne := (hgridTransverse c hc i.2 (cellEdge i 0 t) hz).2 hline
      simpa using mul_ne_zero (sub_ne_zero.mpr hne) hd.ne'
    · have hline : (cellEdge i 1 t).re = a.re + ((i.1 + 1 : ℤ) : ℝ) * d := by
        norm_num [cellEdge, cellVertex, cellNext, Equiv.addRight, gridVertex, Fin.add_def]
      have hne := (hgridTransverse c hc (i.1 + 1) (cellEdge i 1 t) hz).1 hline
      simpa using mul_ne_zero (sub_ne_zero.mpr hne) hd.ne'
    · have hline : (cellEdge i 2 t).im = a.im + ((i.2 + 1 : ℤ) : ℝ) * d := by
        norm_num [cellEdge, cellVertex, cellNext, Equiv.addRight, gridVertex, Fin.add_def,
          Matrix.cons_val_two]
      have hne := (hgridTransverse c hc (i.2 + 1) (cellEdge i 2 t) hz).2 hline
      simpa [Matrix.cons_val_two] using mul_ne_zero (sub_ne_zero.mpr hne) (neg_ne_zero.mpr hd.ne')
    · have hline : (cellEdge i 3 t).re = a.re + (i.1 : ℝ) * d := by
        norm_num [cellEdge, cellVertex, cellNext, Equiv.addRight, gridVertex, Fin.add_def,
          Matrix.cons_val_three]
      have hne := (hgridTransverse c hc i.1 (cellEdge i 3 t) hz).1 hline
      simpa [Matrix.cons_val_three] using mul_ne_zero (sub_ne_zero.mpr hne) (neg_ne_zero.mpr hd.ne')
  have hcircleEdgeCrossing (i : ℤ × ℤ) (j : Fin 4) (t : ℝ)
      (c : ℂ × ℝ) (hc : c ∈ gridCircles) (hcpos : 0 ≤ c.2)
      (hz : cellEdge i j t ∈ Metric.sphere c.1 c.2)
      (hexterior : ∀ᶠ w in nhds (cellEdge i j t), (w ∈ V ↔ c.2 < ‖w - c.1‖)) :
      ∀ᶠ x in nhds t, (cellEdge i j x ∈ V ↔ 0 < (x - t) *
        ((cellEdge i j t - c.1).re * (cellVelocity i j).re +
          (cellEdge i j t - c.1).im * (cellVelocity i j).im)) := by
    have hnormal := hcellCircleNormalNe i j t c hc hz
    have hcircle := hlineCircleCrossing (cellEdge i j t) c.1 (cellVelocity i j) c.2 hcpos
      (by simpa only [Metric.mem_sphere, dist_eq_norm] using hz) hnormal
    have hshift : Filter.Tendsto (fun x : ℝ => x - t) (nhds t) (nhds 0) := by
      simpa only [sub_self, id_eq] using (Filter.tendsto_id.sub_const t :
        Filter.Tendsto (fun x : ℝ => x - t) (nhds t) (nhds (t - t)))
    have hlocal := ((hcellEdgeContinuous i j).continuousAt (x := t)).tendsto.eventually
      hexterior
    filter_upwards [hlocal, hshift.eventually hcircle] with x hx hsign
    rw [hx]
    have heq : cellEdge i j t + ((x - t : ℝ) : ℂ) * cellVelocity i j = cellEdge i j x := by
      simp only [cellEdge, cellVelocity, Complex.ofReal_sub]
      ring
    simpa only [heq] using hsign
  have hexcisionEdgeCrossing (i : ℤ × ℤ) (j : Fin 4) (t : ℝ)
      (v : ℂ) (hv : v ∈ S) (hz : cellEdge i j t ∈ Metric.sphere v r) :
      ∀ᶠ x in nhds t, (cellEdge i j x ∈ V ↔ 0 < (x - t) *
        ((cellEdge i j t - v).re * (cellVelocity i j).re +
          (cellEdge i j t - v).im * (cellVelocity i j).im)) :=
    hcircleEdgeCrossing i j t (v, r) (Or.inr ⟨v, hv, rfl⟩) hr.le hz
      (hexcisionLocalExterior v hv (cellEdge i j t) hz)
  have hindentationEdgeCrossing (i : ℤ × ℤ) (j : Fin 4) (t : ℝ)
      (v : ℂ) (hv : v ∈ B) (s : ℝ) (hs : s ∈ Set.Ioo (cutEnd v) (cutStart v))
      (heq : cellEdge i j t = γ v ε s) :
      ∀ᶠ x in nhds t, (cellEdge i j x ∈ V ↔ 0 < (x - t) *
        ((cellEdge i j t - cutCenter v ε).re * (cellVelocity i j).re +
          (cellEdge i j t - cutCenter v ε).im * (cellVelocity i j).im)) := by
    have hrad : 0 ≤ cutRadius v ε := by
      dsimp only [cutRadius]
      exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (hKH hv.1.1).le) hε.1.le)
        (by nlinarith only [hε.1, hε.2])
    have hz : cellEdge i j t ∈ Metric.sphere (cutCenter v ε) (cutRadius v ε) := by
      rw [heq]
      exact hgammaSphere v (hKH hv.1.1) ε hε.1 hε.2 s
    exact hcircleEdgeCrossing i j t (cutCenter v ε, cutRadius v ε)
      (Or.inl (Or.inr ⟨v, hv, rfl⟩)) hrad hz
      (hboundaryCutLocalExterior v hv _ (by rw [heq]; exact hboundaryArcInterior v hv s hs) hz)
  have hedgeCrossingsFinite (i : ℤ × ℤ) (j : Fin 4) :
      {t ∈ Set.Icc (0 : ℝ) 1 | cellEdge i j t ∈ frontier V}.Finite := by
    have hf := ((hgridVerticalIntersections i.1).union
      (hgridVerticalIntersections (i.1 + 1))).union
        ((hgridHorizontalIntersections i.2).union (hgridHorizontalIntersections (i.2 + 1)))
    apply (hf.preimage (hcellEdgeInjective i j).injOn).subset
    rintro t ⟨_, ht⟩
    change (_ ∨ _) ∨ (_ ∨ _)
    fin_cases j
    · right; left
      refine ⟨ht, ?_⟩
      simp [cellEdge, cellVertex, cellNext, gridVertex, Equiv.addRight, Fin.add_def]
    · left; right
      refine ⟨ht, ?_⟩
      simp [cellEdge, cellVertex, cellNext, gridVertex, Equiv.addRight, Fin.add_def]
    · right; right
      refine ⟨ht, ?_⟩
      simp [cellEdge, cellVertex, cellNext, gridVertex, Equiv.addRight, Fin.add_def]
    · left; left
      refine ⟨ht, ?_⟩
      simp [cellEdge, cellVertex, cellNext, gridVertex, Equiv.addRight, Fin.add_def]
  let edgeCuts : (ℤ × ℤ) → Fin 4 → Finset ℝ := fun i j =>
    insert 0 (insert 1 (hedgeCrossingsFinite i j).toFinset)
  have hedgeCutsMem (i : ℤ × ℤ) (j : Fin 4) (t : ℝ) :
      t ∈ edgeCuts i j ↔ t = 0 ∨ t = 1 ∨
        t ∈ Set.Icc (0 : ℝ) 1 ∧ cellEdge i j t ∈ frontier V := by
    simp only [edgeCuts, Finset.mem_insert, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  have hedgeCutsBounds (i : ℤ × ℤ) (j : Fin 4) {t : ℝ}
      (ht : t ∈ edgeCuts i j) : t ∈ Set.Icc (0 : ℝ) 1 := by
    rcases (hedgeCutsMem i j t).mp ht with rfl | rfl | ht
    · norm_num
    · norm_num
    · exact ht.1
  let edgePieces : (ℤ × ℤ) → Fin 4 → Finset (ℝ × ℝ) := fun i j =>
    ((edgeCuts i j) ×ˢ (edgeCuts i j)).filter (fun p =>
      p.1 < p.2 ∧ ∀ t ∈ edgeCuts i j, t ≤ p.1 ∨ p.2 ≤ t)
  have hedgePieceMem (i : ℤ × ℤ) (j : Fin 4) (p : ℝ × ℝ) :
      p ∈ edgePieces i j ↔ p.1 ∈ edgeCuts i j ∧ p.2 ∈ edgeCuts i j ∧
        p.1 < p.2 ∧ ∀ t ∈ edgeCuts i j, t ≤ p.1 ∨ p.2 ≤ t := by
    simp only [edgePieces, Finset.mem_filter, Finset.mem_product]
    tauto
  have hedgePieceAvoidsFrontier (i : ℤ × ℤ) (j : Fin 4) (p : ℝ × ℝ)
      (hp : p ∈ edgePieces i j) :
      ∀ t ∈ Set.Ioo p.1 p.2, cellEdge i j t ∉ frontier V := by
    obtain ⟨hp₁, hp₂, _, hgap⟩ := (hedgePieceMem i j p).mp hp
    intro t ht hfront
    have ht01 : t ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨(hedgeCutsBounds i j hp₁).1.trans ht.1.le,
        ht.2.le.trans (hedgeCutsBounds i j hp₂).2⟩
    have hcut := (hedgeCutsMem i j t).mpr (Or.inr (Or.inr ⟨ht01, hfront⟩))
    rcases hgap t hcut with h | h <;> linarith [ht.1, ht.2]
  have hedgePieceDichotomy (i : ℤ × ℤ) (j : Fin 4) (p : ℝ × ℝ)
      (hp : p ∈ edgePieces i j) :
      (∀ t ∈ Set.Ioo p.1 p.2, cellEdge i j t ∈ V) ∨
      (∀ t ∈ Set.Ioo p.1 p.2, cellEdge i j t ∉ closure V) := by
    have hcover : cellEdge i j '' Set.Ioo p.1 p.2 ⊆ V ∪ (closure V)ᶜ := by
      rintro z ⟨t, ht, rfl⟩
      by_cases hz : cellEdge i j t ∈ V
      · exact Or.inl hz
      · exact Or.inr (fun hcl => hedgePieceAvoidsFrontier i j p hp t ht
          ⟨hcl, fun hint => hz (interior_subset hint)⟩)
    have hdisjoint : Disjoint V (closure V)ᶜ :=
      Set.disjoint_left.mpr (fun _ hz hn => hn (subset_closure hz))
    rcases (isPreconnected_Ioo.image _ (hcellEdgeContinuous i j).continuousOn).subset_or_subset
      hVopen isClosed_closure.isOpen_compl hdisjoint hcover with hin | hout
    · exact Or.inl (fun t ht => hin ⟨t, ht, rfl⟩)
    · exact Or.inr (fun t ht => hout ⟨t, ht, rfl⟩)
  let retainedPieces : (ℤ × ℤ) → Fin 4 → Finset (ℝ × ℝ) := fun i j =>
    (edgePieces i j).filter (fun p => cellEdge i j ((p.1 + p.2) / 2) ∈ V)
  have hretainedPieceInterior (i : ℤ × ℤ) (j : Fin 4) (p : ℝ × ℝ)
      (hp : p ∈ retainedPieces i j) :
      ∀ t ∈ Set.Ioo p.1 p.2, cellEdge i j t ∈ V := by
    obtain ⟨hpiece, hmid⟩ := Finset.mem_filter.mp hp
    rcases hedgePieceDichotomy i j p hpiece with hin | hout
    · exact hin
    · have hlt := ((hedgePieceMem i j p).mp hpiece).2.2.1
      exact False.elim (hout _ ⟨by linarith, by linarith⟩ (subset_closure hmid))
  have hexcisionRetainedEndpointSigns (i : ℤ × ℤ) (j : Fin 4) (p : ℝ × ℝ)
      (hp : p ∈ retainedPieces i j) (t : ℝ) (v : ℂ) (hv : v ∈ S)
      (hz : cellEdge i j t ∈ Metric.sphere v r) :
      (p.1 = t → 0 < (cellEdge i j t - v).re * (cellVelocity i j).re +
        (cellEdge i j t - v).im * (cellVelocity i j).im) ∧
      (p.2 = t → (cellEdge i j t - v).re * (cellVelocity i j).re +
        (cellEdge i j t - v).im * (cellVelocity i j).im < 0) := by
    have hlt := ((hedgePieceMem i j p).mp (Finset.mem_filter.mp hp).1).2.2.1
    exact hoccupiedEndpointSigns (cellEdge i j) V t _ p.1 p.2 hlt
      (hretainedPieceInterior i j p hp) (hexcisionEdgeCrossing i j t v hv hz)
  have hexcisionEndpointOrientation (i : ℤ × ℤ) (j : Fin 4) (p : ℝ × ℝ)
      (hp : p ∈ retainedPieces i j) (t : ℝ) (v : ℂ) (hv : v ∈ S) (s : ℝ)
      (heq : cellEdge i j t = circleMap v r s) :
      (p.1 = t → 0 < (deriv (circleMap v r) s * star (cellVelocity i j)).im) ∧
      (p.2 = t → (deriv (circleMap v r) s * star (cellVelocity i j)).im < 0) := by
    have hz : cellEdge i j t ∈ Metric.sphere v r := by
      rw [heq]
      exact circleMap_mem_sphere v hr.le s
    have hsign := hexcisionRetainedEndpointSigns i j p hp t v hv hz
    simpa only [hcircleTangent, heq] using hsign
  have hindentationEndpointOrientation (i : ℤ × ℤ) (j : Fin 4) (p : ℝ × ℝ)
      (hp : p ∈ retainedPieces i j) (t : ℝ) (v : ℂ) (hv : v ∈ B) (s : ℝ)
      (hs : s ∈ Set.Ioo (cutEnd v) (cutStart v)) (heq : cellEdge i j t = γ v ε s) :
      (p.1 = t → 0 < (deriv (γ v ε) s * star (cellVelocity i j)).im) ∧
      (p.2 = t → (deriv (γ v ε) s * star (cellVelocity i j)).im < 0) := by
    have hlt := ((hedgePieceMem i j p).mp (Finset.mem_filter.mp hp).1).2.2.1
    have hsign := hoccupiedEndpointSigns (cellEdge i j) V t _ p.1 p.2 hlt
      (hretainedPieceInterior i j p hp) (hindentationEdgeCrossing i j t v hv s hs heq)
    obtain ⟨speed, hspeed, hderiv⟩ := hgammaTangent v ε hε.1 hε.2 s
    have hdet : (deriv (γ v ε) s * star (cellVelocity i j)).im =
        speed * ((cellEdge i j t - cutCenter v ε).re * (cellVelocity i j).re +
          (cellEdge i j t - cutCenter v ε).im * (cellVelocity i j).im) := by
      rw [hderiv, heq]
      simp [Complex.mul_im, Complex.mul_re]
      ring
    rw [hdet]
    exact ⟨fun h => mul_pos hspeed (hsign.1 h), fun h => mul_neg_of_pos_of_neg hspeed (hsign.2 h)⟩
  have hretainedPieceClosure (i : ℤ × ℤ) (j : Fin 4) (p : ℝ × ℝ)
      (hp : p ∈ retainedPieces i j) :
      ∀ t ∈ Set.Icc p.1 p.2, cellEdge i j t ∈ closure V := by
    have hpiece := (Finset.mem_filter.mp hp).1
    have hlt := ((hedgePieceMem i j p).mp hpiece).2.2.1
    have himage : cellEdge i j '' Set.Ioo p.1 p.2 ⊆ V := by
      rintro _ ⟨t, ht, rfl⟩
      exact hretainedPieceInterior i j p hp t ht
    intro t ht
    apply closure_mono himage
    exact image_closure_subset_closure_image (hcellEdgeContinuous i j)
      ⟨t, by rwa [closure_Ioo hlt.ne], rfl⟩
  have hunretainedPieceExterior (i : ℤ × ℤ) (j : Fin 4) (p : ℝ × ℝ)
      (hp : p ∈ edgePieces i j) (hn : p ∉ retainedPieces i j) :
      ∀ t ∈ Set.Ioo p.1 p.2, cellEdge i j t ∉ closure V := by
    rcases hedgePieceDichotomy i j p hp with hin | hout
    · exfalso
      apply hn
      have hlt := ((hedgePieceMem i j p).mp hp).2.2.1
      exact Finset.mem_filter.mpr ⟨hp, hin _ ⟨by linarith, by linarith⟩⟩
    · exact hout
  have hretainedPiecePrimitives (i : ℤ × ℤ) (j : Fin 4) (p : ℝ × ℝ)
      (hp : p ∈ retainedPieces i j) :
      i ∈ gridCells ∧ cellAcross i j ∈ gridCells ∧
      ∃ g h : ℂ → ℂ,
        (∀ z ∈ gridSquare i, HasDerivAt g (L z) z) ∧
        (∀ z ∈ gridSquare (cellAcross i j), HasDerivAt h (L z) z) ∧
        intervalIntegral (fun t => L (cellEdge i j t) * cellVelocity i j)
          p.1 p.2 MeasureTheory.volume = g (cellEdge i j p.2) - g (cellEdge i j p.1) ∧
        intervalIntegral (fun t => L (cellEdge i j t) * cellVelocity i j)
          p.1 p.2 MeasureTheory.volume = h (cellEdge i j p.2) - h (cellEdge i j p.1) := by
    obtain ⟨hpiece, hmid⟩ := Finset.mem_filter.mp hp
    obtain ⟨hp₁, hp₂, hlt, _⟩ := (hedgePieceMem i j p).mp hpiece
    have hbound : Set.Icc p.1 p.2 ⊆ Set.Icc (0 : ℝ) 1 :=
      Set.Icc_subset_Icc (hedgeCutsBounds i j hp₁).1 (hedgeCutsBounds i j hp₂).2
    have hmid01 := hbound (show (p.1 + p.2) / 2 ∈ Set.Icc p.1 p.2 from
      ⟨by linarith, by linarith⟩)
    have hi : i ∈ gridCells :=
      ⟨_, subset_closure hmid, hcellEdgeMem i j _ hmid01⟩
    have hacross (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
        cellEdge i j t ∈ gridSquare (cellAcross i j) := by
      rw [← hcellAcrossPath i j t]
      exact hcellEdgeMem _ _ _ ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have hi' : cellAcross i j ∈ gridCells := ⟨_, subset_closure hmid, hacross _ hmid01⟩
    obtain ⟨g, hg⟩ := hgridPrimitives i hi
    obtain ⟨h, hh⟩ := hgridPrimitives _ hi'
    have hint : IntervalIntegrable (fun t => L (cellEdge i j t) * cellVelocity i j)
        MeasureTheory.volume p.1 p.2 := by
      apply ContinuousOn.intervalIntegrable_of_Icc hlt.le
      intro t ht
      have hcl := hretainedPieceClosure i j p hp t ht
      have hK := hcutClosureK ε ((closure_mono (show V ⊆ Ω ε from fun _ hz => hz.1)) hcl)
      exact (((hLan _ (hKH hK) (hVzeroFree _ hcl)).continuousAt.comp
        (hcellEdgeContinuous i j).continuousAt).mul continuousAt_const).continuousWithinAt
    refine ⟨hi, hi', g, h, hg, hh, ?_, ?_⟩
    · exact hprimitiveIntegral _ g hg (cellEdge i j) (fun _ => cellVelocity i j) p.1 p.2
        (fun t ht => hcellEdgeMem i j t (hbound (by simpa [Set.uIcc_of_le hlt.le] using ht)))
        (fun t _ => hcellEdgeDeriv i j t) hint
    · exact hprimitiveIntegral _ h hh (cellEdge i j) (fun _ => cellVelocity i j) p.1 p.2
        (fun t ht => hacross t (hbound (by simpa [Set.uIcc_of_le hlt.le] using ht)))
        (fun t _ => hcellEdgeDeriv i j t) hint
  have hedgePiecesCover (i : ℤ × ℤ) (j : Fin 4) (t : ℝ)
      (ht : t ∈ Set.Ioo (0 : ℝ) 1) (hn : t ∉ edgeCuts i j) :
      ∃ p ∈ edgePieces i j, t ∈ Set.Ioo p.1 p.2 := by
    let lo := (edgeCuts i j).filter (fun x => x ≤ t)
    let hi := (edgeCuts i j).filter (fun x => t < x)
    have hlo : lo.Nonempty := ⟨0, Finset.mem_filter.mpr
      ⟨(hedgeCutsMem i j 0).mpr (Or.inl rfl), ht.1.le⟩⟩
    have hhi : hi.Nonempty := ⟨1, Finset.mem_filter.mpr
      ⟨(hedgeCutsMem i j 1).mpr (Or.inr (Or.inl rfl)), ht.2⟩⟩
    let u := lo.max' hlo
    let v := hi.min' hhi
    have hu := Finset.mem_filter.mp (lo.max'_mem hlo)
    have hv := Finset.mem_filter.mp (hi.min'_mem hhi)
    have hut : u < t := lt_of_le_of_ne hu.2 (fun heq => hn (heq ▸ hu.1))
    refine ⟨(u, v), (hedgePieceMem i j (u, v)).mpr ⟨hu.1, hv.1, hut.trans hv.2, ?_⟩,
      hut, hv.2⟩
    intro x hx
    by_cases hxt : x ≤ t
    · exact Or.inl (lo.le_max' x (Finset.mem_filter.mpr ⟨hx, hxt⟩))
    · exact Or.inr (hi.min'_le x (Finset.mem_filter.mpr ⟨hx, lt_of_not_ge hxt⟩))
  have hedgePiecesUnique (i : ℤ × ℤ) (j : Fin 4) (p q : ℝ × ℝ)
      (hp : p ∈ edgePieces i j) (hq : q ∈ edgePieces i j)
      (t : ℝ) (hpt : t ∈ Set.Ioo p.1 p.2) (hqt : t ∈ Set.Ioo q.1 q.2) : p = q := by
    obtain ⟨hp₁, hp₂, _, hpgap⟩ := (hedgePieceMem i j p).mp hp
    obtain ⟨hq₁, hq₂, _, hqgap⟩ := (hedgePieceMem i j q).mp hq
    apply Prod.ext
    · apply le_antisymm
      · rcases hqgap p.1 hp₁ with h | h
        · exact h
        · linarith only [h, hpt.1, hqt.2]
      · rcases hpgap q.1 hq₁ with h | h
        · exact h
        · linarith only [h, hqt.1, hpt.2]
    · apply le_antisymm
      · rcases hpgap q.2 hq₂ with h | h
        · linarith only [h, hpt.1, hqt.2]
        · exact h
      · rcases hqgap p.2 hp₂ with h | h
        · linarith only [h, hqt.1, hpt.2]
        · exact h
  have hedgeCutsAcross (i : ℤ × ℤ) (j : Fin 4) (t : ℝ) :
      t ∈ edgeCuts i j ↔ 1 - t ∈ edgeCuts (cellAcross i j) (cellOpp j) := by
    rw [hedgeCutsMem, hedgeCutsMem, hcellAcrossPath]
    constructor
    · rintro (rfl | rfl | ⟨ht, hfront⟩)
      · exact Or.inr (Or.inl (by ring))
      · exact Or.inl (by ring)
      · exact Or.inr (Or.inr ⟨⟨by linarith only [ht.2], by linarith only [ht.1]⟩, hfront⟩)
    · rintro (heq | heq | ⟨ht, hfront⟩)
      · exact Or.inr (Or.inl (by linarith only [heq]))
      · exact Or.inl (by linarith only [heq])
      · exact Or.inr (Or.inr ⟨⟨by linarith only [ht.2], by linarith only [ht.1]⟩, hfront⟩)
  let reversePiece : (ℝ × ℝ) → (ℝ × ℝ) := fun p => (1 - p.2, 1 - p.1)
  have hreversePieceInvol (p : ℝ × ℝ) : reversePiece (reversePiece p) = p := by
    ext <;> simp [reversePiece]
  have hedgePiecesAcross (i : ℤ × ℤ) (j : Fin 4) (p : ℝ × ℝ)
      (hp : p ∈ edgePieces i j) :
      reversePiece p ∈ edgePieces (cellAcross i j) (cellOpp j) := by
    obtain ⟨hp₁, hp₂, hlt, hgap⟩ := (hedgePieceMem i j p).mp hp
    refine (hedgePieceMem _ _ _).mpr ⟨(hedgeCutsAcross i j p.2).mp hp₂,
      (hedgeCutsAcross i j p.1).mp hp₁, by dsimp [reversePiece]; linarith only [hlt], ?_⟩
    intro t ht
    have ht' : 1 - t ∈ edgeCuts i j :=
      (hedgeCutsAcross i j (1 - t)).mpr (by simpa only [sub_sub_cancel] using ht)
    rcases hgap (1 - t) ht' with h | h
    · right; dsimp [reversePiece]; linarith only [h]
    · left; dsimp [reversePiece]; linarith only [h]
  have hretainedPiecesAcross (i : ℤ × ℤ) (j : Fin 4) (p : ℝ × ℝ)
      (hp : p ∈ retainedPieces i j) :
      reversePiece p ∈ retainedPieces (cellAcross i j) (cellOpp j) := by
    obtain ⟨hpiece, hmid⟩ := Finset.mem_filter.mp hp
    refine Finset.mem_filter.mpr ⟨hedgePiecesAcross i j p hpiece, ?_⟩
    have hmidpoint : ((reversePiece p).1 + (reversePiece p).2) / 2 =
        1 - (p.1 + p.2) / 2 := by dsimp [reversePiece]; ring
    simpa only [hmidpoint, hcellAcrossPath] using hmid
  have hretainedPieceIntegralAcross (i : ℤ × ℤ) (j : Fin 4) (p : ℝ × ℝ) :
      intervalIntegral (fun t => L (cellEdge i j t) * cellVelocity i j)
          p.1 p.2 MeasureTheory.volume +
        intervalIntegral
          (fun t => L (cellEdge (cellAcross i j) (cellOpp j) t) *
            cellVelocity (cellAcross i j) (cellOpp j))
          (reversePiece p).1 (reversePiece p).2 MeasureTheory.volume = 0 := by
    have heq : (fun t => L (cellEdge (cellAcross i j) (cellOpp j) (1 - t)) *
        cellVelocity (cellAcross i j) (cellOpp j)) =
        fun t => -(L (cellEdge i j t) * cellVelocity i j) := by
      funext t
      rw [hcellAcrossPath, hcellAcrossVelocity, mul_neg]
    have hreflect := intervalIntegral.integral_comp_sub_left
      (fun t => L (cellEdge (cellAcross i j) (cellOpp j) t) *
        cellVelocity (cellAcross i j) (cellOpp j)) (a := p.1) (b := p.2) 1
    rw [heq, intervalIntegral.integral_neg] at hreflect
    change _ + intervalIntegral _ (1 - p.2) (1 - p.1) MeasureTheory.volume = 0
    rw [← hreflect, add_neg_cancel]
  let retainedGridPieces : Finset ((ℤ × ℤ) × Fin 4 × (ℝ × ℝ)) :=
    hgridFinite.toFinset.biUnion (fun i => Finset.univ.biUnion (fun j : Fin 4 =>
      (retainedPieces i j).image (fun p => (i, j, p))))
  have hretainedGridMem (e : (ℤ × ℤ) × Fin 4 × (ℝ × ℝ)) :
      e ∈ retainedGridPieces ↔ e.1 ∈ gridCells ∧ e.2.2 ∈ retainedPieces e.1 e.2.1 := by
    rcases e with ⟨⟨x, y⟩, j, u, v⟩
    simp [retainedGridPieces]
  let retainedIntegral : ((ℤ × ℤ) × Fin 4 × (ℝ × ℝ)) → ℂ := fun e =>
    intervalIntegral (fun t => L (cellEdge e.1 e.2.1 t) * cellVelocity e.1 e.2.1)
      e.2.2.1 e.2.2.2 MeasureTheory.volume
  have hretainedGridCancellation : ∑ e ∈ retainedGridPieces, retainedIntegral e = 0 := by
    let swap : ((ℤ × ℤ) × Fin 4 × (ℝ × ℝ)) → ((ℤ × ℤ) × Fin 4 × (ℝ × ℝ)) :=
      fun e => (cellAcross e.1 e.2.1, cellOpp e.2.1, reversePiece e.2.2)
    apply Finset.sum_involution (fun e _ => swap e)
    · intro e _
      exact hretainedPieceIntegralAcross e.1 e.2.1 e.2.2
    · intro e _ _ heq
      exact hcellOppNe e.2.1 (congrArg (fun e : (ℤ × ℤ) × Fin 4 × (ℝ × ℝ) => e.2.1) heq)
    · intro e he
      have hp := ((hretainedGridMem e).mp he).2
      exact (hretainedGridMem (swap e)).mpr
        ⟨(hretainedPiecePrimitives e.1 e.2.1 e.2.2 hp).2.1,
          hretainedPiecesAcross e.1 e.2.1 e.2.2 hp⟩
    · intro e _
      exact Prod.ext (hcellAcrossInvol e.1 e.2.1).1
        (Prod.ext (hcellAcrossInvol e.1 e.2.1).2 (hreversePieceInvol e.2.2))
  have hretainedPiecesCover (i : ℤ × ℤ) (j : Fin 4) (t : ℝ)
      (ht : t ∈ Set.Ioo (0 : ℝ) 1) (hV : cellEdge i j t ∈ V) :
      ∃! p : ℝ × ℝ, p ∈ retainedPieces i j ∧ t ∈ Set.Ioo p.1 p.2 := by
    have hn : t ∉ edgeCuts i j := by
      intro hcut
      rcases (hedgeCutsMem i j t).mp hcut with heq | heq | ⟨_, hfront⟩
      · linarith only [heq, ht.1]
      · linarith only [heq, ht.2]
      · have hint : interior V = V := hVopen.interior_eq
        exact hfront.2 (hint.symm ▸ hV)
    obtain ⟨p, hp, hpt⟩ := hedgePiecesCover i j t ht hn
    have hret : p ∈ retainedPieces i j := by
      by_contra hnot
      exact hunretainedPieceExterior i j p hp hnot t hpt (subset_closure hV)
    refine ⟨p, ⟨hret, hpt⟩, ?_⟩
    rintro q ⟨hq, hqt⟩
    exact hedgePiecesUnique i j q p (Finset.mem_filter.mp hq).1 hp t hqt hpt
  have hcellVertexAvoidsFrontier (i : ℤ × ℤ) (j : Fin 4) :
      cellVertex i j ∉ frontier V := by
    fin_cases j
    · exact hgridVerticesAvoidFrontier i
    · exact hgridVerticesAvoidFrontier (i.1 + 1, i.2)
    · exact hgridVerticesAvoidFrontier (i.1 + 1, i.2 + 1)
    · exact hgridVerticesAvoidFrontier (i.1, i.2 + 1)
  have hretainedPieceEndpoints (i : ℤ × ℤ) (j : Fin 4) (p : ℝ × ℝ)
      (hp : p ∈ retainedPieces i j) :
      ((p.1 = 0 ∧ cellEdge i j p.1 = cellVertex i j ∧ cellVertex i j ∈ V) ∨
        cellEdge i j p.1 ∈ frontier V) ∧
      ((p.2 = 1 ∧ cellEdge i j p.2 = cellVertex i (cellNext j) ∧
          cellVertex i (cellNext j) ∈ V) ∨ cellEdge i j p.2 ∈ frontier V) := by
    obtain ⟨hp₁, hp₂, hlt, _⟩ := (hedgePieceMem i j p).mp (Finset.mem_filter.mp hp).1
    have hstartcl := hretainedPieceClosure i j p hp p.1 ⟨le_rfl, hlt.le⟩
    have hendcl := hretainedPieceClosure i j p hp p.2 ⟨hlt.le, le_rfl⟩
    have hvertexMem (q : Fin 4) (hcl : cellVertex i q ∈ closure V) : cellVertex i q ∈ V := by
      by_contra hnot
      exact hcellVertexAvoidsFrontier i q ⟨hcl, fun hint => hnot (interior_subset hint)⟩
    constructor
    · rcases (hedgeCutsMem i j p.1).mp hp₁ with hzero | hone | hfront
      · have heq : cellEdge i j p.1 = cellVertex i j := by
          rw [hzero, (hcellEdgeEndpoints i j).1]
        exact Or.inl ⟨hzero, heq, hvertexMem j (heq ▸ hstartcl)⟩
      · have hbound := (hedgeCutsBounds i j hp₂).2
        linarith only [hlt, hone, hbound]
      · exact Or.inr hfront.2
    · rcases (hedgeCutsMem i j p.2).mp hp₂ with hzero | hone | hfront
      · have hbound := (hedgeCutsBounds i j hp₁).1
        linarith only [hlt, hzero, hbound]
      · have heq : cellEdge i j p.2 = cellVertex i (cellNext j) := by
          rw [hone, (hcellEdgeEndpoints i j).2]
        exact Or.inl ⟨hone, heq, hvertexMem (cellNext j) (heq ▸ hendcl)⟩
      · exact Or.inr hfront.2
  have hfiniteEdgeVertexSums (η : ℝ → ℂ) (hη : Continuous η)
      (cuts : Finset ℝ) (h0 : 0 ∈ cuts) (h1 : 1 ∈ cuts)
      (pieces retained : Finset (ℝ × ℝ))
      (hpiece : ∀ p, p ∈ pieces ↔ p.1 ∈ cuts ∧ p.2 ∈ cuts ∧
        p.1 < p.2 ∧ ∀ t ∈ cuts, t ≤ p.1 ∨ p.2 ≤ t)
      (hretained : retained ⊆ pieces)
      (hclosure : ∀ p ∈ retained, ∀ t ∈ Set.Icc p.1 p.2, η t ∈ closure V)
      (hexterior : ∀ p ∈ pieces, p ∉ retained → ∀ t ∈ Set.Ioo p.1 p.2,
        η t ∉ closure V)
      (havoid0 : η 0 ∉ frontier V) (havoid1 : η 1 ∉ frontier V) :
      ∀ G : ℂ → ℂ,
        (∑ p ∈ retained, if p.1 = 0 then G (η p.1) else 0) =
          (if η 0 ∈ V then G (η 0) else 0) ∧
        (∑ p ∈ retained, if p.2 = 1 then G (η p.2) else 0) =
          (if η 1 ∈ V then G (η 1) else 0) := by
    classical
    have hendpointRetained (p : ℝ × ℝ) (hp : p ∈ pieces) (t : ℝ)
        (ht : t ∈ Set.Icc p.1 p.2) (havoid : η t ∉ frontier V) :
        p ∈ retained ↔ η t ∈ V := by
      constructor
      · intro hret
        by_contra hnot
        exact havoid ⟨hclosure p hret t ht, fun hint => hnot (interior_subset hint)⟩
      · intro hmem
        by_contra hnot
        have hsub : Set.Ioo p.1 p.2 ⊆ η ⁻¹' Vᶜ := by
          intro u hu hVu
          exact hexterior p hp hnot u hu (subset_closure hVu)
        have hc := closure_minimal hsub (hVopen.isClosed_compl.preimage hη)
        rw [closure_Ioo ((hpiece p).mp hp).2.2.1.ne] at hc
        exact hc ht hmem
    have hfirst : ∃! p : ℝ × ℝ, p ∈ pieces ∧ p.1 = 0 := by
      let positive := cuts.filter (fun t => 0 < t)
      have hpos : positive.Nonempty := ⟨1, Finset.mem_filter.mpr ⟨h1, zero_lt_one⟩⟩
      let v := positive.min' hpos
      have hv := Finset.mem_filter.mp (positive.min'_mem hpos)
      refine ⟨(0, v), ⟨(hpiece (0, v)).mpr ⟨h0, hv.1, hv.2, ?_⟩, rfl⟩, ?_⟩
      · intro t ht
        by_cases ht0 : t ≤ 0
        · exact Or.inl ht0
        · exact Or.inr (positive.min'_le t (Finset.mem_filter.mpr ⟨ht, lt_of_not_ge ht0⟩))
      · rintro q ⟨hq, hq0⟩
        obtain ⟨_, hq2, hqLt, hqGap⟩ := (hpiece q).mp hq
        apply Prod.ext hq0
        apply le_antisymm
        · rcases hqGap v hv.1 with h | h
          · rw [hq0] at h
            exact (not_le_of_gt hv.2 h).elim
          · exact h
        · exact positive.min'_le q.2 (Finset.mem_filter.mpr ⟨hq2, hq0 ▸ hqLt⟩)
    have hlast : ∃! p : ℝ × ℝ, p ∈ pieces ∧ p.2 = 1 := by
      let below := cuts.filter (fun t => t < 1)
      have hbelow : below.Nonempty := ⟨0, Finset.mem_filter.mpr ⟨h0, zero_lt_one⟩⟩
      let u := below.max' hbelow
      have hu := Finset.mem_filter.mp (below.max'_mem hbelow)
      refine ⟨(u, 1), ⟨(hpiece (u, 1)).mpr ⟨hu.1, h1, hu.2, ?_⟩, rfl⟩, ?_⟩
      · intro t ht
        by_cases ht1 : 1 ≤ t
        · exact Or.inr ht1
        · exact Or.inl (below.le_max' t (Finset.mem_filter.mpr ⟨ht, lt_of_not_ge ht1⟩))
      · rintro q ⟨hq, hq1⟩
        obtain ⟨hq0, _, hqLt, hqGap⟩ := (hpiece q).mp hq
        refine Prod.ext (le_antisymm ?_ ?_) hq1
        · exact below.le_max' q.1 (Finset.mem_filter.mpr ⟨hq0, hq1 ▸ hqLt⟩)
        · rcases hqGap u hu.1 with h | h
          · exact h
          · rw [hq1] at h
            exact (not_le_of_gt hu.2 h).elim
    intro G
    obtain ⟨p, ⟨hp, hp0⟩, hpu⟩ := hfirst
    obtain ⟨q, ⟨hq, hq1⟩, hqu⟩ := hlast
    have hpRet : p ∈ retained ↔ η 0 ∈ V :=
      hendpointRetained p hp 0 ⟨hp0.le, hp0 ▸ ((hpiece p).mp hp).2.2.1.le⟩ havoid0
    have hqRet : q ∈ retained ↔ η 1 ∈ V :=
      hendpointRetained q hq 1 ⟨hq1 ▸ ((hpiece q).mp hq).2.2.1.le, hq1.ge⟩ havoid1
    constructor
    · by_cases hmem : η 0 ∈ V
      · rw [if_pos hmem, Finset.sum_eq_single p]
        · rw [if_pos hp0, hp0]
        · intro x hx hxp
          exact if_neg (fun hx0 => hxp (hpu x ⟨hretained hx, hx0⟩))
        · intro hn
          exact (hn (hpRet.mpr hmem)).elim
      · rw [if_neg hmem]
        apply Finset.sum_eq_zero
        intro x hx
        apply if_neg
        intro hx0
        have hxp := hpu x ⟨hretained hx, hx0⟩
        exact hmem (hpRet.mp (hxp ▸ hx))
    · by_cases hmem : η 1 ∈ V
      · rw [if_pos hmem, Finset.sum_eq_single q]
        · rw [if_pos hq1, hq1]
        · intro x hx hxq
          exact if_neg (fun hx1 => hxq (hqu x ⟨hretained hx, hx1⟩))
        · intro hn
          exact (hn (hqRet.mpr hmem)).elim
      · rw [if_neg hmem]
        apply Finset.sum_eq_zero
        intro x hx
        apply if_neg
        intro hx1
        have hxq := hqu x ⟨hretained hx, hx1⟩
        exact hmem (hqRet.mp (hxq ▸ hx))
  have hgridCellVertexSums (i : ℤ × ℤ) (j : Fin 4) (G : ℂ → ℂ) :
      (∑ p ∈ retainedPieces i j, if p.1 = 0 then G (cellEdge i j p.1) else 0) =
        (if cellVertex i j ∈ V then G (cellVertex i j) else 0) ∧
      (∑ p ∈ retainedPieces i j, if p.2 = 1 then G (cellEdge i j p.2) else 0) =
        (if cellVertex i (cellNext j) ∈ V then G (cellVertex i (cellNext j)) else 0) := by
    have h := hfiniteEdgeVertexSums (cellEdge i j) (hcellEdgeContinuous i j)
      (edgeCuts i j) ((hedgeCutsMem i j 0).mpr (Or.inl rfl))
      ((hedgeCutsMem i j 1).mpr (Or.inr (Or.inl rfl)))
      (edgePieces i j) (retainedPieces i j) (hedgePieceMem i j)
      (fun _ hp => (Finset.mem_filter.mp hp).1)
      (hretainedPieceClosure i j) (hunretainedPieceExterior i j)
      (by simpa only [(hcellEdgeEndpoints i j).1] using hcellVertexAvoidsFrontier i j)
      (by simpa only [(hcellEdgeEndpoints i j).2] using
        hcellVertexAvoidsFrontier i (cellNext j)) G
    simpa only [(hcellEdgeEndpoints i j).1, (hcellEdgeEndpoints i j).2] using h
  have hfinitePieceIncidence (cuts : Finset ℝ) (pieces : Finset (ℝ × ℝ))
      (hpiece : ∀ p, p ∈ pieces ↔ p.1 ∈ cuts ∧ p.2 ∈ cuts ∧
        p.1 < p.2 ∧ ∀ t ∈ cuts, t ≤ p.1 ∨ p.2 ≤ t)
      (t : ℝ) (ht : t ∈ cuts) :
      ((∃ x ∈ cuts, t < x) → ∃! p : ℝ × ℝ, p ∈ pieces ∧ p.1 = t) ∧
      ((∃ x ∈ cuts, x < t) → ∃! p : ℝ × ℝ, p ∈ pieces ∧ p.2 = t) := by
    constructor
    · rintro ⟨x, hx, htx⟩
      let above := cuts.filter (fun x => t < x)
      have habove : above.Nonempty := ⟨x, Finset.mem_filter.mpr ⟨hx, htx⟩⟩
      let b := above.min' habove
      have hb := Finset.mem_filter.mp (above.min'_mem habove)
      refine ⟨(t, b), ⟨(hpiece (t, b)).mpr ⟨ht, hb.1, hb.2, ?_⟩, rfl⟩, ?_⟩
      · intro y hy
        by_cases hyt : y ≤ t
        · exact Or.inl hyt
        · exact Or.inr (above.min'_le y (Finset.mem_filter.mpr ⟨hy, lt_of_not_ge hyt⟩))
      · rintro q ⟨hq, hqt⟩
        obtain ⟨_, hq2, hqLt, hqGap⟩ := (hpiece q).mp hq
        refine Prod.ext hqt (le_antisymm ?_ ?_)
        · rcases hqGap b hb.1 with h | h
          · rw [hqt] at h
            exact (not_le_of_gt hb.2 h).elim
          · exact h
        · exact above.min'_le q.2 (Finset.mem_filter.mpr ⟨hq2, hqt ▸ hqLt⟩)
    · rintro ⟨x, hx, hxt⟩
      let below := cuts.filter (fun x => x < t)
      have hbelow : below.Nonempty := ⟨x, Finset.mem_filter.mpr ⟨hx, hxt⟩⟩
      let a := below.max' hbelow
      have ha := Finset.mem_filter.mp (below.max'_mem hbelow)
      refine ⟨(a, t), ⟨(hpiece (a, t)).mpr ⟨ha.1, ht, ha.2, ?_⟩, rfl⟩, ?_⟩
      · intro y hy
        by_cases hty : t ≤ y
        · exact Or.inr hty
        · exact Or.inl (below.le_max' y (Finset.mem_filter.mpr ⟨hy, lt_of_not_ge hty⟩))
      · rintro q ⟨hq, hqt⟩
        obtain ⟨hq1, _, hqLt, hqGap⟩ := (hpiece q).mp hq
        refine Prod.ext (le_antisymm ?_ ?_) hqt
        · exact below.le_max' q.1 (Finset.mem_filter.mpr ⟨hq1, hqt ▸ hqLt⟩)
        · rcases hqGap a ha.1 with h | h
          · exact h
          · rw [hqt] at h
            exact (not_le_of_gt ha.2 h).elim
  have hclosedSubdivisionEndpointReduction
      (cuts : Finset ℝ) (pieces : Finset (ℝ × ℝ)) (u v : ℝ)
      (hu : u ∈ cuts) (hv : v ∈ cuts) (huv : u < v)
      (hpiece : ∀ p, p ∈ pieces ↔ p.1 ∈ cuts ∧ p.2 ∈ cuts ∧
        p.1 < p.2 ∧ ∀ t ∈ cuts, t ≤ p.1 ∨ p.2 ≤ t)
      (η : ℝ → ℂ) (cell : (ℝ × ℝ) → ℤ × ℤ)
      (square : (ℤ × ℤ) → Set ℂ)
      (hpath : ∀ p ∈ pieces, ∀ t ∈ Set.Icc p.1 p.2, η t ∈ square (cell p))
      (hclosed : η v = η u)
      (hunique : ∀ i j, η u ∈ square i → η u ∈ square j → i = j)
      (G : (ℤ × ℤ) → ℂ → ℂ) :
      (∑ p ∈ pieces, (G (cell p) (η p.2) - G (cell p) (η p.1))) =
        ∑ p ∈ pieces, ((if p.2 = v then 0 else G (cell p) (η p.2)) -
          (if p.1 = u then 0 else G (cell p) (η p.1))) := by
    obtain ⟨first, ⟨hfirst, hfirstStart⟩, hfirstUnique⟩ :=
      (hfinitePieceIncidence cuts pieces hpiece u hu).1 ⟨v, hv, huv⟩
    obtain ⟨last, ⟨hlast, hlastEnd⟩, hlastUnique⟩ :=
      (hfinitePieceIncidence cuts pieces hpiece v hv).2 ⟨u, hu, huv⟩
    have hfirstMem : η u ∈ square (cell first) := by
      rw [← hfirstStart]
      exact hpath first hfirst first.1 ⟨le_rfl, ((hpiece first).mp hfirst).2.2.1.le⟩
    have hlastMem : η u ∈ square (cell last) := by
      rw [← hclosed, ← hlastEnd]
      exact hpath last hlast last.2 ⟨((hpiece last).mp hlast).2.2.1.le, le_rfl⟩
    have hcell := hunique (cell last) (cell first) hlastMem hfirstMem
    have hfirstSum :
        (∑ p ∈ pieces, if p.1 = u then G (cell p) (η p.1) else 0) =
          G (cell first) (η u) := by
      rw [Finset.sum_eq_single first]
      · rw [if_pos hfirstStart, hfirstStart]
      · intro p hp hne
        exact if_neg (fun h => hne (hfirstUnique p ⟨hp, h⟩))
      · exact fun h => (h hfirst).elim
    have hlastSum :
        (∑ p ∈ pieces, if p.2 = v then G (cell p) (η p.2) else 0) =
          G (cell last) (η v) := by
      rw [Finset.sum_eq_single last]
      · rw [if_pos hlastEnd, hlastEnd]
      · intro p hp hne
        exact if_neg (fun h => hne (hlastUnique p ⟨hp, h⟩))
      · exact fun h => (h hlast).elim
    have hbalance :
        (∑ p ∈ pieces, if p.2 = v then G (cell p) (η p.2) else 0) =
          ∑ p ∈ pieces, if p.1 = u then G (cell p) (η p.1) else 0 := by
      rw [hlastSum, hfirstSum, hclosed, hcell]
    have hsplit (p : ℝ × ℝ) :
        G (cell p) (η p.2) - G (cell p) (η p.1) =
          ((if p.2 = v then 0 else G (cell p) (η p.2)) -
            (if p.1 = u then 0 else G (cell p) (η p.1))) +
          ((if p.2 = v then G (cell p) (η p.2) else 0) -
            (if p.1 = u then G (cell p) (η p.1) else 0)) := by
      split_ifs <;> ring
    calc
      _ = (∑ p ∈ pieces, ((if p.2 = v then 0 else G (cell p) (η p.2)) -
            (if p.1 = u then 0 else G (cell p) (η p.1)))) +
          ((∑ p ∈ pieces, if p.2 = v then G (cell p) (η p.2) else 0) -
            ∑ p ∈ pieces, if p.1 = u then G (cell p) (η p.1) else 0) := by
        simp_rw [hsplit, Finset.sum_add_distrib, Finset.sum_sub_distrib]
      _ = _ := by rw [hbalance, sub_self, add_zero]
  have hcellEdgeCoordinates (i : ℤ × ℤ) (j : Fin 4) (t : ℝ) :
      (cellEdge i j t).re =
        ![a.re + (i.1 : ℝ) * d + t * d, a.re + ((i.1 : ℝ) + 1) * d,
          a.re + ((i.1 : ℝ) + 1) * d - t * d, a.re + (i.1 : ℝ) * d] j ∧
      (cellEdge i j t).im =
        ![a.im + (i.2 : ℝ) * d, a.im + (i.2 : ℝ) * d + t * d,
          a.im + ((i.2 : ℝ) + 1) * d, a.im + ((i.2 : ℝ) + 1) * d - t * d] j := by
    fin_cases j <;> constructor <;>
      norm_num [cellEdge, cellVertex, cellNext, Equiv.addRight, gridVertex, Fin.add_def,
        Matrix.cons_val_two, Matrix.cons_val_three] <;> ring_nf <;> simp
  have hgridCellsAtEdge (i : ℤ × ℤ) (j : Fin 4) (t : ℝ)
      (ht : t ∈ Set.Ioo (0 : ℝ) 1) (q : ℤ × ℤ)
      (hq : cellEdge i j t ∈ gridSquare q) : q = i ∨ q = cellAcross i j := by
    have hinteriorIndex (x o : ℝ) (m n : ℤ)
        (hm : o + (m : ℝ) * d < x ∧ x < o + ((m : ℝ) + 1) * d)
        (hn : o + (n : ℝ) * d ≤ x ∧ x ≤ o + ((n : ℝ) + 1) * d) : n = m := by
      apply le_antisymm
      · by_contra hnm
        have hle : m + 1 ≤ n := by omega
        have hmul : ((m : ℝ) + 1) * d ≤ (n : ℝ) * d :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hle) hd.le
        linarith only [hm.2, hn.1, hmul]
      · by_contra hmn
        have hle : n + 1 ≤ m := by omega
        have hmul : ((n : ℝ) + 1) * d ≤ (m : ℝ) * d :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hle) hd.le
        linarith only [hm.1, hn.2, hmul]
    have hboundaryIndex (o : ℝ) (m n : ℤ)
        (hn : o + (n : ℝ) * d ≤ o + (m : ℝ) * d ∧
          o + (m : ℝ) * d ≤ o + ((n : ℝ) + 1) * d) : n = m ∨ n = m - 1 := by
      have hlo : n ≤ m := by
        exact_mod_cast (le_of_mul_le_mul_right (by linarith only [hn.1]) hd : (n : ℝ) ≤ m)
      have hhi : m ≤ n + 1 := by
        exact_mod_cast (le_of_mul_le_mul_right (by linarith only [hn.2]) hd : (m : ℝ) ≤ (n : ℝ) + 1)
      omega
    have htd : 0 < t * d ∧ t * d < d :=
      ⟨mul_pos ht.1 hd, by simpa only [one_mul] using mul_lt_mul_of_pos_right ht.2 hd⟩
    change a.re + (q.1 : ℝ) * d ≤ (cellEdge i j t).re ∧
      (cellEdge i j t).re ≤ a.re + ((q.1 : ℝ) + 1) * d ∧
      a.im + (q.2 : ℝ) * d ≤ (cellEdge i j t).im ∧
      (cellEdge i j t).im ≤ a.im + ((q.2 : ℝ) + 1) * d at hq
    rw [(hcellEdgeCoordinates i j t).1, (hcellEdgeCoordinates i j t).2] at hq
    fin_cases j
    · change a.re + (q.1 : ℝ) * d ≤ a.re + (i.1 : ℝ) * d + t * d ∧
        a.re + (i.1 : ℝ) * d + t * d ≤ a.re + ((q.1 : ℝ) + 1) * d ∧
        a.im + (q.2 : ℝ) * d ≤ a.im + (i.2 : ℝ) * d ∧
        a.im + (i.2 : ℝ) * d ≤ a.im + ((q.2 : ℝ) + 1) * d at hq
      have hx := hinteriorIndex _ a.re i.1 q.1
        ⟨by linarith only [htd.1], by linarith only [htd.2]⟩ ⟨hq.1, hq.2.1⟩
      rcases hboundaryIndex a.im i.2 q.2 hq.2.2 with hy | hy
      · exact Or.inl (Prod.ext hx hy)
      · exact Or.inr (Prod.ext hx hy)
    · change a.re + (q.1 : ℝ) * d ≤ a.re + ((i.1 : ℝ) + 1) * d ∧
        a.re + ((i.1 : ℝ) + 1) * d ≤ a.re + ((q.1 : ℝ) + 1) * d ∧
        a.im + (q.2 : ℝ) * d ≤ a.im + (i.2 : ℝ) * d + t * d ∧
        a.im + (i.2 : ℝ) * d + t * d ≤ a.im + ((q.2 : ℝ) + 1) * d at hq
      have hy := hinteriorIndex _ a.im i.2 q.2
        ⟨by linarith only [htd.1], by linarith only [htd.2]⟩ hq.2.2
      have hx := hboundaryIndex a.re (i.1 + 1) q.1
        (by simpa only [Int.cast_add, Int.cast_one] using And.intro hq.1 hq.2.1)
      rcases hx with hx | hx
      · exact Or.inr (Prod.ext hx hy)
      · exact Or.inl (Prod.ext (by omega) hy)
    · change a.re + (q.1 : ℝ) * d ≤ a.re + ((i.1 : ℝ) + 1) * d - t * d ∧
        a.re + ((i.1 : ℝ) + 1) * d - t * d ≤ a.re + ((q.1 : ℝ) + 1) * d ∧
        a.im + (q.2 : ℝ) * d ≤ a.im + ((i.2 : ℝ) + 1) * d ∧
        a.im + ((i.2 : ℝ) + 1) * d ≤ a.im + ((q.2 : ℝ) + 1) * d at hq
      have hx := hinteriorIndex _ a.re i.1 q.1
        ⟨by linarith only [htd.2], by linarith only [htd.1]⟩ ⟨hq.1, hq.2.1⟩
      have hy := hboundaryIndex a.im (i.2 + 1) q.2
        (by simpa only [Int.cast_add, Int.cast_one] using hq.2.2)
      rcases hy with hy | hy
      · exact Or.inr (Prod.ext hx hy)
      · exact Or.inl (Prod.ext hx (by omega))
    · change a.re + (q.1 : ℝ) * d ≤ a.re + (i.1 : ℝ) * d ∧
        a.re + (i.1 : ℝ) * d ≤ a.re + ((q.1 : ℝ) + 1) * d ∧
        a.im + (q.2 : ℝ) * d ≤ a.im + ((i.2 : ℝ) + 1) * d - t * d ∧
        a.im + ((i.2 : ℝ) + 1) * d - t * d ≤ a.im + ((q.2 : ℝ) + 1) * d at hq
      have hy := hinteriorIndex _ a.im i.2 q.2
        ⟨by linarith only [htd.2], by linarith only [htd.1]⟩ hq.2.2
      rcases hboundaryIndex a.re i.1 q.1 ⟨hq.1, hq.2.1⟩ with hx | hx
      · exact Or.inl (Prod.ext hx hy)
      · exact Or.inr (Prod.ext hx hy)
  have hnonnegativeEndpointDerivative (f : ℝ → ℝ) (D t u v : ℝ)
      (hderiv : HasDerivAt f D t) (hzero : f t = 0) (hD : D ≠ 0) (huv : u < v)
      (hside : ∀ x ∈ Set.Ioo u v, 0 ≤ f x) :
      (u = t → 0 < D) ∧ (v = t → D < 0) := by
    constructor
    · rintro rfl
      have hnonneg : 0 ≤ D := by
        apply ge_of_tendsto (hasDerivAt_iff_tendsto_slope_left_right.mp hderiv).2
        filter_upwards [self_mem_nhdsWithin,
          (eventually_lt_nhds huv).filter_mono nhdsWithin_le_nhds] with x hx hxv
        change u < x at hx
        simp only [slope, vsub_eq_sub, smul_eq_mul, hzero, sub_zero]
        exact mul_nonneg (inv_nonneg.mpr (sub_nonneg.mpr hx.le)) (hside x ⟨hx, hxv⟩)
      exact lt_of_le_of_ne hnonneg hD.symm
    · rintro rfl
      have hnonpos : D ≤ 0 := by
        apply le_of_tendsto (hasDerivAt_iff_tendsto_slope_left_right.mp hderiv).1
        filter_upwards [self_mem_nhdsWithin,
          (eventually_gt_nhds huv).filter_mono nhdsWithin_le_nhds] with x hx hux
        change x < v at hx
        simp only [slope, vsub_eq_sub, smul_eq_mul, hzero, sub_zero]
        exact mul_nonpos_of_nonpos_of_nonneg (inv_nonpos.mpr (sub_nonpos.mpr hx.le))
          (hside x ⟨hux, hx⟩)
      exact lt_of_le_of_ne hnonpos hD
  have hcellSideNonneg (i : ℤ × ℤ) (j : Fin 4) (z : ℂ) (hz : z ∈ gridSquare i) :
      0 ≤ ((z - cellVertex i j) * star (cellVelocity i j)).im := by
    have hformula : ((z - cellVertex i j) * star (cellVelocity i j)).im =
        ![d * (z.im - (a.im + (i.2 : ℝ) * d)),
          d * (a.re + ((i.1 : ℝ) + 1) * d - z.re),
          d * (a.im + ((i.2 : ℝ) + 1) * d - z.im),
          d * (z.re - (a.re + (i.1 : ℝ) * d))] j := by
      fin_cases j <;> norm_num [cellVelocity, cellVertex, cellNext, Equiv.addRight,
        gridVertex, Fin.add_def, Complex.mul_im, Complex.mul_re,
        Matrix.cons_val_two, Matrix.cons_val_three] <;> ring
    rw [hformula]
    fin_cases j
    · exact mul_nonneg hd.le (sub_nonneg.mpr hz.2.2.1)
    · exact mul_nonneg hd.le (sub_nonneg.mpr hz.2.1)
    · exact mul_nonneg hd.le (sub_nonneg.mpr hz.2.2.2)
    · exact mul_nonneg hd.le (sub_nonneg.mpr hz.1)
  have hcellSideOnEdge (i : ℤ × ℤ) (j : Fin 4) (t : ℝ) :
      ((cellEdge i j t - cellVertex i j) * star (cellVelocity i j)).im = 0 := by
    have hsub : cellEdge i j t - cellVertex i j = (t : ℂ) * cellVelocity i j := by
      simp only [cellEdge, cellVelocity, add_sub_cancel_left]
    rw [hsub, mul_assoc,
      show cellVelocity i j * star (cellVelocity i j) = (Complex.normSq (cellVelocity i j) : ℂ)
        from Complex.mul_conj (cellVelocity i j)]
    simp
  have hcellPathEndpointSigns (η : ℝ → ℂ) (s : ℝ) (w : ℂ)
      (hη : HasDerivAt η w s) (i : ℤ × ℤ) (j : Fin 4) (t : ℝ)
      (heq : η s = cellEdge i j t) (u v : ℝ) (huv : u < v)
      (hpath : ∀ x ∈ Set.Ioo u v, η x ∈ gridSquare i)
      (htrans : (w * star (cellVelocity i j)).im ≠ 0) :
      (u = s → 0 < (w * star (cellVelocity i j)).im) ∧
      (v = s → (w * star (cellVelocity i j)).im < 0) := by
    apply hnonnegativeEndpointDerivative
      (fun x => ((η x - cellVertex i j) * star (cellVelocity i j)).im)
      _ s u v _ _ htrans huv (fun x hx => hcellSideNonneg i j _ (hpath x hx))
    · simpa only [Function.comp_def, Complex.imCLM_apply] using
        Complex.imCLM.hasFDerivAt.comp_hasDerivAt s
          ((hη.sub_const (cellVertex i j)).mul_const (star (cellVelocity i j)))
    · rw [heq]
      exact hcellSideOnEdge i j t
  have hcellPathEndpointCell (η : ℝ → ℂ) (s : ℝ) (D : ℂ)
      (hD : HasDerivAt η D s) (i : ℤ × ℤ) (j : Fin 4) (t : ℝ)
      (ht : t ∈ Set.Ioo (0 : ℝ) 1) (heq : η s = cellEdge i j t)
      (q : ℤ × ℤ) (u v : ℝ) (huv : u < v)
      (hpath : ∀ x ∈ Set.Icc u v, η x ∈ gridSquare q)
      (hsign : (u = s ∧ 0 < (D * star (cellVelocity i j)).im) ∨
        (v = s ∧ (D * star (cellVelocity i j)).im < 0)) : q = i := by
    have hs : s ∈ Set.Icc u v := by
      rcases hsign with ⟨h, _⟩ | ⟨h, _⟩ <;> constructor <;> linarith only [huv, h]
    rcases hgridCellsAtEdge i j t ht q (by rw [← heq]; exact hpath s hs) with hq | hq
    · exact hq
    subst q
    have hcontact : η s = cellEdge (cellAcross i j) (cellOpp j) (1 - t) :=
      heq.trans (hcellAcrossPath i j t).symm
    have hdet : (D * star (cellVelocity (cellAcross i j) (cellOpp j))).im =
        -(D * star (cellVelocity i j)).im := by
      rw [hcellAcrossVelocity, star_neg, mul_neg, Complex.neg_im]
    have hn : (D * star (cellVelocity (cellAcross i j) (cellOpp j))).im ≠ 0 := by
      rw [hdet]
      rcases hsign with ⟨_, h⟩ | ⟨_, h⟩
      · exact neg_ne_zero.mpr h.ne'
      · exact neg_ne_zero.mpr h.ne
    have hother := hcellPathEndpointSigns η s D hD (cellAcross i j) (cellOpp j)
      (1 - t) hcontact u v huv (fun x hx => hpath x ⟨hx.1.le, hx.2.le⟩) hn
    rw [hdet] at hother
    rcases hsign with ⟨h, hpos⟩ | ⟨h, hneg⟩
    · have := hother.1 h
      linarith only [hpos, this]
    · have := hother.2 h
      linarith only [hneg, this]
  have hfiniteRetainedEndpointIncidence
      (cuts : Finset ℝ) (pieces retained : Finset (ℝ × ℝ))
      (hpiece : ∀ p, p ∈ pieces ↔ p.1 ∈ cuts ∧ p.2 ∈ cuts ∧
        p.1 < p.2 ∧ ∀ t ∈ cuts, t ≤ p.1 ∨ p.2 ≤ t)
      (hretained : retained ⊆ pieces) (η : ℝ → ℂ) (U : Set ℂ)
      (hinside : ∀ p ∈ retained, ∀ x ∈ Set.Ioo p.1 p.2, η x ∈ U)
      (houtside : ∀ p ∈ pieces, p ∉ retained → ∀ x ∈ Set.Ioo p.1 p.2, η x ∉ U)
      (a b t D : ℝ) (ha : a ∈ cuts) (hb : b ∈ cuts) (ht : t ∈ cuts)
      (hat : a < t) (htb : t < b)
      (hcross : ∀ᶠ x in nhds t, (η x ∈ U ↔ 0 < (x - t) * D)) :
      ((∃! p : ℝ × ℝ, p ∈ retained ∧ p.1 = t) ↔ 0 < D) ∧
      ((∃! p : ℝ × ℝ, p ∈ retained ∧ p.2 = t) ↔ D < 0) := by
    constructor
    · constructor
      · rintro ⟨p, ⟨hp, hpt⟩, _⟩
        exact (hoccupiedEndpointSigns η U t D p.1 p.2
          ((hpiece p).mp (hretained hp)).2.2.1 (hinside p hp) hcross).1 hpt
      · intro hD
        obtain ⟨p, ⟨hp, hpt⟩, huniq⟩ :=
          (hfinitePieceIncidence cuts pieces hpiece t ht).1 ⟨b, hb, htb⟩
        have hpRet : p ∈ retained := by
          by_contra hn
          have hlt : t < p.2 := hpt ▸ ((hpiece p).mp hp).2.2.1
          have hnear := (hcross.and (eventually_lt_nhds hlt)).filter_mono
            (show nhdsWithin t (Set.Ioi t) ≤ nhds t from nhdsWithin_le_nhds)
          have hside : ∀ᶠ x in nhdsWithin t (Set.Ioi t), t < x := self_mem_nhdsWithin
          obtain ⟨x, htx, hlocal, hxp⟩ := (hside.and hnear).exists
          exact houtside p hp hn x ⟨by simpa only [hpt] using htx, hxp⟩
            (hlocal.mpr (mul_pos (sub_pos.mpr htx) hD))
        exact ⟨p, ⟨hpRet, hpt⟩, fun q hq => huniq q ⟨hretained hq.1, hq.2⟩⟩
    · constructor
      · rintro ⟨p, ⟨hp, hpt⟩, _⟩
        exact (hoccupiedEndpointSigns η U t D p.1 p.2
          ((hpiece p).mp (hretained hp)).2.2.1 (hinside p hp) hcross).2 hpt
      · intro hD
        obtain ⟨p, ⟨hp, hpt⟩, huniq⟩ :=
          (hfinitePieceIncidence cuts pieces hpiece t ht).2 ⟨a, ha, hat⟩
        have hpRet : p ∈ retained := by
          by_contra hn
          have hlt : p.1 < t := hpt ▸ ((hpiece p).mp hp).2.2.1
          have hnear := (hcross.and (eventually_gt_nhds hlt)).filter_mono
            (show nhdsWithin t (Set.Iio t) ≤ nhds t from nhdsWithin_le_nhds)
          have hside : ∀ᶠ x in nhdsWithin t (Set.Iio t), x < t := self_mem_nhdsWithin
          obtain ⟨x, hxt, hlocal, hpx⟩ := (hside.and hnear).exists
          exact houtside p hp hn x ⟨hpx, by simpa only [hpt] using hxt⟩
            (hlocal.mpr (mul_pos_of_neg_of_neg (sub_neg.mpr hxt) hD))
        exact ⟨p, ⟨hpRet, hpt⟩, fun q hq => huniq q ⟨hretained hq.1, hq.2⟩⟩
  have hfiniteSubdivision (s : Finset ℝ) (a b : ℝ) (ha : a ∈ s) (hb : b ∈ s)
      (hs : ∀ x ∈ s, a ≤ x ∧ x ≤ b) (f : ℝ → ℂ)
      (hf : IntervalIntegrable f MeasureTheory.volume a b) :
      ∑ p ∈ (s ×ˢ s).filter (fun p => p.1 < p.2 ∧ ∀ x ∈ s, x ≤ p.1 ∨ p.2 ≤ x),
        intervalIntegral f p.1 p.2 MeasureTheory.volume =
          intervalIntegral f a b MeasureTheory.volume := by
    classical
    have hchain : ∀ (n : ℕ) (t : Fin (n + 1) → ℝ),
        (∀ i j, IntervalIntegrable f MeasureTheory.volume (t i) (t j)) →
        (∑ j : Fin n, intervalIntegral f (t j.castSucc) (t j.succ) MeasureTheory.volume) =
          intervalIntegral f (t 0) (t (Fin.last n)) MeasureTheory.volume := by
      intro n
      induction n with
      | zero => intro t _; simp
      | succ n ih =>
        intro t hint
        rw [Fin.sum_univ_castSucc]
        have h := ih (fun j => t j.castSucc) (fun i j => hint _ _)
        simp only [Fin.succ_castSucc]
        rw [h]
        exact intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _)
    let n := s.card - 1
    have hcard : s.card = n + 1 := by
      have hpos := Finset.card_pos.mpr (show s.Nonempty from ⟨a, ha⟩)
      dsimp [n]
      omega
    let t : Fin (n + 1) ↪o ℝ := s.orderEmbOfFin hcard
    have htmem (j : Fin (n + 1)) : t j ∈ s := s.orderEmbOfFin_mem hcard j
    have htsurj {x : ℝ} (hx : x ∈ s) : ∃ j, t j = x := by
      have : x ∈ Set.range t := by simpa only [t, Finset.range_orderEmbOfFin, Finset.mem_coe] using hx
      exact this
    have ht0 : t 0 = a := by
      obtain ⟨j, hj⟩ := htsurj ha
      apply le_antisymm
      · rw [← hj]
        exact t.monotone (Fin.zero_le j)
      · exact (hs _ (htmem 0)).1
    have htn : t (Fin.last n) = b := by
      obtain ⟨j, hj⟩ := htsurj hb
      apply le_antisymm
      · exact (hs _ (htmem _)).2
      · rw [← hj]
        exact t.monotone (Fin.le_last j)
    let pair : Fin n → ℝ × ℝ := fun j => (t j.castSucc, t j.succ)
    have hpairinj : Function.Injective pair := by
      intro i j hij
      apply Fin.ext
      have heq := t.injective (congrArg Prod.fst hij)
      exact congrArg (fun x : Fin (n + 1) => x.val) heq
    have hpairs : (s ×ˢ s).filter
        (fun p => p.1 < p.2 ∧ ∀ x ∈ s, x ≤ p.1 ∨ p.2 ≤ x) = Finset.univ.image pair := by
      ext p
      constructor
      · intro hp
        obtain ⟨hpp, hpLt, hpGap⟩ := Finset.mem_filter.mp hp
        obtain ⟨hp₁, hp₂⟩ := Finset.mem_product.mp hpp
        obtain ⟨u, hu⟩ := htsurj hp₁
        obtain ⟨v, hv⟩ := htsurj hp₂
        have huv : u < v := t.strictMono.lt_iff_lt.mp (by simpa [hu, hv] using hpLt)
        have huvn : v.val = u.val + 1 := by
          by_contra hn
          have huc : u.val + 1 < n + 1 := by omega
          let w : Fin (n + 1) := ⟨u.val + 1, huc⟩
          have huw : t u < t w := t.strictMono (by change u.val < u.val + 1; omega)
          have hwv : t w < t v := t.strictMono (by change u.val + 1 < v.val; change u.val < v.val at huv; omega)
          rcases hpGap (t w) (htmem w) with h | h
          · rw [hu] at huw
            exact (not_lt_of_ge h) huw
          · rw [hv] at hwv
            exact (not_lt_of_ge h) hwv
        let j : Fin n := ⟨u.val, by omega⟩
        refine Finset.mem_image.mpr ⟨j, Finset.mem_univ _, ?_⟩
        have hju : j.castSucc = u := Fin.ext rfl
        have hjv : j.succ = v := Fin.ext huvn.symm
        exact Prod.ext (by simpa only [pair, hju] using hu) (by simpa only [pair, hjv] using hv)
      · rintro hp
        obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hp
        refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨htmem _, htmem _⟩,
          t.strictMono (by simp), ?_⟩
        intro x hx
        obtain ⟨u, rfl⟩ := htsurj hx
        by_cases huj : u ≤ j.castSucc
        · exact Or.inl (t.monotone huj)
        · exact Or.inr (t.monotone (by change j.val + 1 ≤ u.val; change ¬u.val ≤ j.val at huj; omega))
    rw [hpairs, Finset.sum_image (fun _ _ _ _ h => hpairinj h)]
    have hinterval (i j : Fin (n + 1)) :
        IntervalIntegrable f MeasureTheory.volume (t i) (t j) := by
      apply hf.mono_set
      exact Set.uIcc_subset_uIcc
        (by simpa only [Set.uIcc_of_le (hs a ha).2, Set.mem_Icc] using hs _ (htmem i))
        (by simpa only [Set.uIcc_of_le (hs a ha).2, Set.mem_Icc] using hs _ (htmem j))
    simpa only [pair, ht0, htn] using hchain n t hinterval
  have hedgePieceIntegral (i : ℤ × ℤ) (j : Fin 4) (p : ℝ × ℝ)
      (hp : p ∈ edgePieces i j) :
      intervalIntegral (occupiedEdge i j) p.1 p.2 MeasureTheory.volume =
        if p ∈ retainedPieces i j then
          intervalIntegral (fun t => L (cellEdge i j t) * cellVelocity i j)
            p.1 p.2 MeasureTheory.volume else 0 := by
    have hlt := ((hedgePieceMem i j p).mp hp).2.2.1
    by_cases hret : p ∈ retainedPieces i j
    · rw [if_pos hret]
      apply intervalIntegral.integral_congr_Ioo_of_le hlt.le
      intro t ht
      exact if_pos (hretainedPieceInterior i j p hret t ht)
    · rw [if_neg hret]
      calc
        _ = intervalIntegral (fun _ : ℝ => (0 : ℂ)) p.1 p.2 MeasureTheory.volume := by
          apply intervalIntegral.integral_congr_Ioo_of_le hlt.le
          intro t ht
          exact if_neg (fun hmem => hunretainedPieceExterior i j p hp hret t ht (subset_closure hmem))
        _ = 0 := intervalIntegral.integral_zero
  have hoccupiedEdgeSubdivision (i : ℤ × ℤ) (j : Fin 4) :
      occupiedEdgeIntegral i j =
        ∑ p ∈ retainedPieces i j,
          intervalIntegral (fun t => L (cellEdge i j t) * cellVelocity i j)
            p.1 p.2 MeasureTheory.volume := by
    have hsplit := hfiniteSubdivision (edgeCuts i j) 0 1
      ((hedgeCutsMem i j 0).mpr (Or.inl rfl))
      ((hedgeCutsMem i j 1).mpr (Or.inr (Or.inl rfl)))
      (fun t ht => hedgeCutsBounds i j ht) (occupiedEdge i j) (hoccupiedEdgeIntegrable i j)
    change (∑ p ∈ edgePieces i j, intervalIntegral (occupiedEdge i j)
      p.1 p.2 MeasureTheory.volume) = occupiedEdgeIntegral i j at hsplit
    rw [← hsplit]
    simp_rw [retainedPieces, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p hp
    rw [hedgePieceIntegral i j p hp]
    simp only [retainedPieces, Finset.mem_filter, hp, true_and]
  have hretainedBoundaryCancellation :
      ∑ i ∈ boundaryCells, ∑ j : Fin 4, ∑ p ∈ retainedPieces i j,
        intervalIntegral (fun t => L (cellEdge i j t) * cellVelocity i j)
          p.1 p.2 MeasureTheory.volume = 0 := by
    simpa only [hoccupiedEdgeSubdivision] using hboundaryCellIntegralsCancel
  let gridCrossings : Set ℂ := ⋃ i ∈ gridCells,
    ({z ∈ frontier V | z.re = a.re + (i.1 : ℝ) * d} ∪
      {z ∈ frontier V | z.re = a.re + ((i.1 + 1 : ℤ) : ℝ) * d}) ∪
    ({z ∈ frontier V | z.im = a.im + (i.2 : ℝ) * d} ∪
      {z ∈ frontier V | z.im = a.im + ((i.2 + 1 : ℤ) : ℝ) * d})
  have hgridCrossingsFinite' : gridCrossings.Finite := hgridCrossingsFinite
  have hgridCrossingContains (z : ℂ) (hz : z ∈ frontier V) (n : ℤ)
      (hn : z.re = a.re + (n : ℝ) * d ∨ z.im = a.im + (n : ℝ) * d) :
      z ∈ gridCrossings := by
    obtain ⟨i, hi, hzi⟩ := Set.mem_iUnion₂.mp (hgridCover (frontier_subset_closure hz))
    refine Set.mem_iUnion₂.mpr ⟨i, hi, ?_⟩
    rcases hn with hn | hn
    · have hlo : (i.1 : ℝ) ≤ n :=
        le_of_mul_le_mul_right (by linarith only [hzi.1, hn]) hd
      have hhi : (n : ℝ) ≤ (i.1 : ℝ) + 1 :=
        le_of_mul_le_mul_right (by linarith only [hzi.2.1, hn]) hd
      have hlo' : i.1 ≤ n := by exact_mod_cast hlo
      have hhi' : n ≤ i.1 + 1 := by exact_mod_cast hhi
      have heq : n = i.1 ∨ n = i.1 + 1 := by omega
      rcases heq with rfl | rfl
      · exact Or.inl (Or.inl ⟨hz, hn⟩)
      · exact Or.inl (Or.inr ⟨hz, hn⟩)
    · have hlo : (i.2 : ℝ) ≤ n :=
        le_of_mul_le_mul_right (by linarith only [hzi.2.2.1, hn]) hd
      have hhi : (n : ℝ) ≤ (i.2 : ℝ) + 1 :=
        le_of_mul_le_mul_right (by linarith only [hzi.2.2.2, hn]) hd
      have hlo' : i.2 ≤ n := by exact_mod_cast hlo
      have hhi' : n ≤ i.2 + 1 := by exact_mod_cast hhi
      have heq : n = i.2 ∨ n = i.2 + 1 := by omega
      rcases heq with rfl | rfl
      · exact Or.inr (Or.inl ⟨hz, hn⟩)
      · exact Or.inr (Or.inr ⟨hz, hn⟩)
  have hstayAbove (f : ℝ → ℝ) (hf : Continuous f) (u v c level : ℝ)
      (hc : c ∈ Set.Ioo u v) (hfc : level < f c)
      (havoid : ∀ t ∈ Set.Ioo u v, f t ≠ level) :
      ∀ t ∈ Set.Ioo u v, level < f t := by
    have hcover : f '' Set.Ioo u v ⊆ Set.Iio level ∪ Set.Ioi level := by
      rintro _ ⟨t, ht, rfl⟩
      exact lt_or_gt_of_ne (havoid t ht)
    have hdisjoint : Disjoint (Set.Iio level) (Set.Ioi level) :=
      Set.disjoint_left.mpr (fun x (h₁ : x < level) (h₂ : level < x) => lt_asymm h₁ h₂)
    rcases (isPreconnected_Ioo.image _ hf.continuousOn).subset_or_subset
      isOpen_Iio isOpen_Ioi hdisjoint hcover with hlo | hhi
    · exact False.elim (lt_asymm (hlo ⟨c, hc, rfl⟩) hfc)
    · exact fun t ht => hhi ⟨t, ht, rfl⟩
  have hpathOneCell (η : ℝ → ℂ) (hη : Continuous η) (u v : ℝ) (huv : u < v)
      (hfront : ∀ t ∈ Set.Icc u v, η t ∈ frontier V)
      (havoid : ∀ t ∈ Set.Ioo u v, η t ∉ gridCrossings) :
      ∃ i ∈ gridCells, ∀ t ∈ Set.Icc u v, η t ∈ gridSquare i := by
    let c := (u + v) / 2
    have hc : c ∈ Set.Ioo u v := ⟨by dsimp [c]; linarith only [huv],
      by dsimp [c]; linarith only [huv]⟩
    obtain ⟨i, hi, hci⟩ := Set.mem_iUnion₂.mp
      (hgridCover (frontier_subset_closure (hfront c ⟨hc.1.le, hc.2.le⟩)))
    have hnot (t : ℝ) (ht : t ∈ Set.Ioo u v) (n : ℤ) :
        (η t).re ≠ a.re + (n : ℝ) * d ∧ (η t).im ≠ a.im + (n : ℝ) * d := by
      constructor
      · intro heq
        exact havoid t ht (hgridCrossingContains _ (hfront t ⟨ht.1.le, ht.2.le⟩) n (Or.inl heq))
      · intro heq
        exact havoid t ht (hgridCrossingContains _ (hfront t ⟨ht.1.le, ht.2.le⟩) n (Or.inr heq))
    have hnotReHi (t : ℝ) (ht : t ∈ Set.Ioo u v) :
        (η t).re ≠ a.re + ((i.1 : ℝ) + 1) * d := by
      simpa only [Int.cast_add, Int.cast_one] using (hnot t ht (i.1 + 1)).1
    have hnotImHi (t : ℝ) (ht : t ∈ Set.Ioo u v) :
        (η t).im ≠ a.im + ((i.2 : ℝ) + 1) * d := by
      simpa only [Int.cast_add, Int.cast_one] using (hnot t ht (i.2 + 1)).2
    have hrealLo := hstayAbove (fun t => (η t).re) (Complex.continuous_re.comp hη)
      u v c (a.re + (i.1 : ℝ) * d) hc
      (lt_of_le_of_ne hci.1 (hnot c hc i.1).1.symm) (fun t ht => (hnot t ht i.1).1)
    have hrealHi := hstayAbove (fun t => -(η t).re) (Complex.continuous_re.comp hη).neg
      u v c (-(a.re + ((i.1 : ℝ) + 1) * d)) hc
      (neg_lt_neg (lt_of_le_of_ne hci.2.1 (hnotReHi c hc)))
      (fun t ht h => hnotReHi t ht (neg_injective h))
    have himagLo := hstayAbove (fun t => (η t).im) (Complex.continuous_im.comp hη)
      u v c (a.im + (i.2 : ℝ) * d) hc
      (lt_of_le_of_ne hci.2.2.1 (hnot c hc i.2).2.symm) (fun t ht => (hnot t ht i.2).2)
    have himagHi := hstayAbove (fun t => -(η t).im) (Complex.continuous_im.comp hη).neg
      u v c (-(a.im + ((i.2 : ℝ) + 1) * d)) hc
      (neg_lt_neg (lt_of_le_of_ne hci.2.2.2 (hnotImHi c hc)))
      (fun t ht h => hnotImHi t ht (neg_injective h))
    have hinside : Set.Ioo u v ⊆ η ⁻¹' gridSquare i := by
      intro t ht
      exact ⟨(hrealLo t ht).le, (neg_lt_neg_iff.mp (hrealHi t ht)).le,
        (himagLo t ht).le, (neg_lt_neg_iff.mp (himagHi t ht)).le⟩
    have hclosed : IsClosed (gridSquare i) :=
      (isClosed_le continuous_const Complex.continuous_re).inter
        ((isClosed_le Complex.continuous_re continuous_const).inter
          ((isClosed_le continuous_const Complex.continuous_im).inter
            (isClosed_le Complex.continuous_im continuous_const)))
    have hall := closure_minimal hinside (hclosed.preimage hη)
    rw [closure_Ioo huv.ne] at hall
    exact ⟨i, hi, hall⟩
  have hgenuineSubdivision (η : ℝ → ℂ) (hη : ContDiff ℝ 1 η) (u v : ℝ) (huv : u < v)
      (hfront : ∀ t ∈ Set.Icc u v, η t ∈ frontier V)
      (hinj : Set.InjOn η (Set.Ioo u v)) :
      ∃ (cuts : Finset ℝ) (pieces : Finset (ℝ × ℝ))
        (cell : (ℝ × ℝ) → ℤ × ℤ),
        u ∈ cuts ∧ v ∈ cuts ∧ (∀ t ∈ cuts, t ∈ Set.Icc u v) ∧
        pieces = (cuts ×ˢ cuts).filter
          (fun p => p.1 < p.2 ∧ ∀ t ∈ cuts, t ≤ p.1 ∨ p.2 ≤ t) ∧
        (∀ p ∈ pieces, cell p ∈ gridCells ∧
          (∀ t ∈ Set.Icc p.1 p.2, η t ∈ gridSquare (cell p)) ∧
          (∀ z ∈ gridSquare (cell p), HasDerivAt (cellPrimitive (cell p)) (L z) z) ∧
          intervalIntegral (fun t => L (η t) * deriv η t) p.1 p.2 MeasureTheory.volume =
            cellPrimitive (cell p) (η p.2) - cellPrimitive (cell p) (η p.1)) ∧
        (intervalIntegral (fun t => L (η t) * deriv η t) u v MeasureTheory.volume =
          ∑ p ∈ pieces, (cellPrimitive (cell p) (η p.2) - cellPrimitive (cell p) (η p.1))) ∧
        ∀ t : ℝ, t ∈ cuts ↔ t = u ∨ t = v ∨
          t ∈ Set.Ioo u v ∧ η t ∈ gridCrossings := by
    have hfinite : {t ∈ Set.Ioo u v | η t ∈ gridCrossings}.Finite := by
      have himage : (η '' {t ∈ Set.Ioo u v | η t ∈ gridCrossings}).Finite := by
        apply hgridCrossingsFinite'.subset
        rintro _ ⟨t, ht, rfl⟩
        exact ht.2
      exact himage.of_finite_image (hinj.mono (fun _ ht => ht.1))
    let cuts := insert u (insert v hfinite.toFinset)
    let pieces := (cuts ×ˢ cuts).filter
      (fun p : ℝ × ℝ => p.1 < p.2 ∧ ∀ t ∈ cuts, t ≤ p.1 ∨ p.2 ≤ t)
    have hcuts (t : ℝ) : t ∈ cuts ↔ t = u ∨ t = v ∨
        t ∈ Set.Ioo u v ∧ η t ∈ gridCrossings := by
      simp only [cuts, Finset.mem_insert, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    have hbounds (t : ℝ) (ht : t ∈ cuts) : t ∈ Set.Icc u v := by
      rcases (hcuts t).mp ht with rfl | rfl | ht
      · exact ⟨le_rfl, huv.le⟩
      · exact ⟨huv.le, le_rfl⟩
      · exact ⟨ht.1.1.le, ht.1.2.le⟩
    have hint : IntervalIntegrable (fun t => L (η t) * deriv η t)
        MeasureTheory.volume u v := by
      apply ContinuousOn.intervalIntegrable_of_Icc huv.le
      intro t ht
      have hcl := frontier_subset_closure (hfront t ht)
      have hK := hcutClosureK ε ((closure_mono (show V ⊆ Ω ε from fun _ hz => hz.1)) hcl)
      exact (((hLan _ (hKH hK) (hVzeroFree _ hcl)).continuousAt.comp
        hη.continuous.continuousAt).mul
          hη.continuous_deriv_one.continuousAt).continuousWithinAt
    have hcert : ∀ p : ℝ × ℝ, ∃ i : ℤ × ℤ, p ∈ pieces →
        i ∈ gridCells ∧ (∀ t ∈ Set.Icc p.1 p.2, η t ∈ gridSquare i) ∧
        (∀ z ∈ gridSquare i, HasDerivAt (cellPrimitive i) (L z) z) ∧
        intervalIntegral (fun t => L (η t) * deriv η t) p.1 p.2 MeasureTheory.volume =
          cellPrimitive i (η p.2) - cellPrimitive i (η p.1) := by
      intro p
      by_cases hp : p ∈ pieces
      · obtain ⟨hpp, hlt, hgap⟩ := Finset.mem_filter.mp hp
        obtain ⟨hp₁, hp₂⟩ := Finset.mem_product.mp hpp
        have hsub : Set.Icc p.1 p.2 ⊆ Set.Icc u v :=
          Set.Icc_subset_Icc (hbounds _ hp₁).1 (hbounds _ hp₂).2
        have havoid : ∀ t ∈ Set.Ioo p.1 p.2, η t ∉ gridCrossings := by
          intro t ht hcross
          have htuv : t ∈ Set.Ioo u v :=
            ⟨lt_of_le_of_lt (hbounds _ hp₁).1 ht.1, lt_of_lt_of_le ht.2 (hbounds _ hp₂).2⟩
          have hcut := (hcuts t).mpr (Or.inr (Or.inr ⟨htuv, hcross⟩))
          rcases hgap t hcut with h | h <;> linarith only [h, ht.1, ht.2]
        obtain ⟨i, hi, hpath⟩ := hpathOneCell η hη.continuous p.1 p.2 hlt
          (fun t ht => hfront t (hsub ht)) havoid
        refine ⟨i, fun _ => ⟨hi, hpath, hcellPrimitive i hi, ?_⟩⟩
        apply hprimitiveIntegral (gridSquare i) (cellPrimitive i) (hcellPrimitive i hi)
          η (deriv η) p.1 p.2
        · intro t ht
          exact hpath t (by simpa only [Set.uIcc_of_le hlt.le] using ht)
        · intro t _
          exact ((hη.differentiable (by norm_num)) t).hasDerivAt
        · exact hint.mono_set (by simpa only [Set.uIcc_of_le hlt.le, Set.uIcc_of_le huv.le] using hsub)
      · exact ⟨(0, 0), fun h => (hp h).elim⟩
    choose cell hcert using hcert
    refine ⟨cuts, pieces, cell, (hcuts u).mpr (Or.inl rfl),
      (hcuts v).mpr (Or.inr (Or.inl rfl)), hbounds, rfl, hcert, ?_, hcuts⟩
    calc
      _ = ∑ p ∈ pieces, intervalIntegral (fun t => L (η t) * deriv η t)
          p.1 p.2 MeasureTheory.volume :=
        (hfiniteSubdivision cuts u v ((hcuts u).mpr (Or.inl rfl))
          ((hcuts v).mpr (Or.inr (Or.inl rfl))) hbounds _ hint).symm
      _ = _ := Finset.sum_congr rfl (fun p hp => (hcert p hp).2.2.2)
  have hcircleSubdivision (v : ℂ) (hv : v ∈ S) :=
    hgenuineSubdivision (circleMap v r) (contDiff_circleMap v r)
      0 (2 * Real.pi) (by positivity)
      (fun t _ => (hcircles v hv).1 ⟨t, rfl⟩)
      (by
        intro x hx y hy hxy
        apply eq_of_circleMap_eq hr.ne' _ hxy
        rw [abs_lt]
        constructor <;> linarith only [hx.1, hx.2, hy.1, hy.2])
  have hgammaCoordinate (v : ℂ) (hv : v ∈ H) (t : ℝ) :
      (γ v ε t - v) / (γ v ε t - star v) = circleMap 0 ε t := by
    have hw : Complex.normSq (circleMap 0 ε t) < 1 := by
      rw [Complex.normSq_eq_norm_sq, norm_circleMap_zero, abs_of_pos hε.1]
      nlinarith only [hε.1, hε.2]
    simpa only [γ, circleMap, zero_add] using
      (hcutCoordinates v hv (circleMap 0 ε t) hw).2.2.2
  have hgammaInjective (v : ℂ) (hv : v ∈ H) :
      Set.InjOn (γ v ε) (Set.Ioo (cutEnd v) (cutStart v)) := by
    intro x hx y hy hxy
    have ha := hcutAngles v hv
    apply eq_of_circleMap_eq (c := (0 : ℂ)) hε.1.ne'
    · rw [abs_lt]
      constructor <;> linarith only [ha.1, ha.2.2.1, hx.1, hx.2, hy.1, hy.2]
    · rw [← hgammaCoordinate v hv x, ← hgammaCoordinate v hv y, hxy]
  have hfullVFrontier : frontier V =
      ((⋃ i : Fin 4, closure (Ω ε) ∩ outerSupport i) ∪
        ⋃ v ∈ B, γ v ε '' Set.Icc (cutEnd v) (cutStart v)) ∪
      ⋃ v ∈ S, Metric.sphere v r := by
    simpa only [V, S, Set.mem_ofPred_eq] using hVfrontier
  have hindentationSubdivision (v : ℂ) (hv : v ∈ B) :=
    hgenuineSubdivision (γ v ε) (hgammaSmooth v ε hε.1 hε.2)
      (cutEnd v) (cutStart v) (hcutAngles v (hKH hv.1.1)).2.1
      (fun t ht => by
        rw [hfullVFrontier]
        exact Or.inl (Or.inr (Set.mem_iUnion₂.mpr ⟨v, hv, ⟨t, ht, rfl⟩⟩)))
      (hgammaInjective v (hKH hv.1.1))
  have hcircleIntersectionFinite (c₁ c₂ : ℂ) (r₁ r₂ : ℝ) (hc : c₁ ≠ c₂) :
      {z : ℂ | ‖z - c₁‖ = r₁ ∧ ‖z - c₂‖ = r₂}.Finite := by
    classical
    let s : Set ℂ := {z | ‖z - c₁‖ = r₁ ∧ ‖z - c₂‖ = r₂}
    by_cases hs : s.Subsingleton
    · exact hs.finite
    obtain ⟨p, hp, q, hq, hpq⟩ := Set.not_subsingleton_iff.mp hs
    apply (Set.toFinite ({p, q} : Set ℂ)).subset
    intro z hz
    let S₁ : EuclideanGeometry.Sphere ℂ := ⟨c₁, r₁⟩
    let S₂ : EuclideanGeometry.Sphere ℂ := ⟨c₂, r₂⟩
    have hne : S₁ ≠ S₂ := fun h => hc (congrArg EuclideanGeometry.Sphere.center h)
    have hgeom := EuclideanGeometry.eq_of_mem_sphere_of_mem_sphere_of_finrank_eq_two
      (V := ℂ) Complex.finrank_real_complex hne hpq
      (show p ∈ S₁ from by simpa [S₁, EuclideanGeometry.mem_sphere, dist_eq_norm] using hp.1)
      (show q ∈ S₁ from by simpa [S₁, EuclideanGeometry.mem_sphere, dist_eq_norm] using hq.1)
      (show z ∈ S₁ from by simpa [S₁, EuclideanGeometry.mem_sphere, dist_eq_norm] using hz.1)
      (show p ∈ S₂ from by simpa [S₂, EuclideanGeometry.mem_sphere, dist_eq_norm] using hp.2)
      (show q ∈ S₂ from by simpa [S₂, EuclideanGeometry.mem_sphere, dist_eq_norm] using hq.2)
      (show z ∈ S₂ from by simpa [S₂, EuclideanGeometry.mem_sphere, dist_eq_norm] using hz.2)
    exact hgeom
  have hKsubsetClosureO : K ⊆ closure O := by
    have hYtwo : (2 : ℝ) ≤ Y := le_max_right Y₀ 2
    intro z hz
    let ψ : ℝ → ℂ := fun t => ((1 - t : ℝ) : ℂ) * z + ((3 * t / 2 : ℝ) : ℂ) * Complex.I
    have hψre (t : ℝ) : (ψ t).re = (1 - t) * z.re := by simp [ψ]
    have hψim (t : ℝ) : (ψ t).im = (1 - t) * z.im + 3 * t / 2 := by simp [ψ]
    have hψ0 : ψ 0 = z := by simp [ψ]
    have hψcont : Continuous ψ := by dsimp [ψ]; fun_prop
    have hψmem (t : ℝ) (ht : 0 < t) (ht1 : t < 1) : ψ t ∈ O := by
      have hcoef : 0 < 1 - t := sub_pos.mpr ht1
      have hy : 2 / 3 < z.im := by
        have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
        have hn := Real.sqrt_nonneg (3 : ℝ)
        have hlow := hKlower z hz
        nlinarith only [hs, hn, hlow]
      have hnorm : 1 ≤ Complex.normSq z := by
        rw [Complex.normSq_eq_norm_sq]
        nlinarith only [hz.2.1]
      have hnormid : Complex.normSq (ψ t) - 1 =
          (1 - t) ^ 2 * (Complex.normSq z - 1) +
            t * (1 - t) * (3 * z.im - 2) + 5 / 4 * t ^ 2 := by
        rw [Complex.normSq_apply, Complex.normSq_apply, hψre, hψim]
        ring
      have hterm₁ : 0 ≤ (1 - t) ^ 2 * (Complex.normSq z - 1) :=
        mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hnorm)
      have hterm₂ : 0 ≤ t * (1 - t) * (3 * z.im - 2) :=
        mul_nonneg (mul_nonneg ht.le hcoef.le) (by linarith only [hy])
      have hterm₃ : 0 < (5 / 4 : ℝ) * t ^ 2 := by positivity
      have hsq : 1 < Complex.normSq (ψ t) := by
        linarith only [hnormid, hterm₁, hterm₂, hterm₃]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hψre, abs_mul, abs_of_pos hcoef]
        calc
          _ ≤ (1 - t) * (1 / 2) := mul_le_mul_of_nonneg_left hz.1 hcoef.le
          _ < 1 / 2 := by linarith only [ht]
      · rw [Complex.normSq_eq_norm_sq] at hsq
        nlinarith only [hsq, norm_nonneg (ψ t)]
      · rw [hψim]
        positivity
      · rw [hψim]
        have hle := mul_le_mul_of_nonneg_left hz.2.2.2 hcoef.le
        have hpos : 0 < t * (Y - 3 / 2) := mul_pos ht (by linarith only [hYtwo])
        nlinarith only [hle, hpos]
    have ht : Filter.Tendsto ψ (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds z) := by
      simpa only [hψ0] using
        (hψcont.continuousAt (x := (0 : ℝ))).tendsto.mono_left
          (show nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤ nhds 0 from nhdsWithin_le_nhds)
    apply mem_closure_of_tendsto ht
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds] with t ht ht1
    exact hψmem t ht ht1
  have hcutCenterNeZero (v : ℂ) (hv : v ∈ B) : cutCenter v ε ≠ 0 := by
    have hvim : 0 < v.im := hKH hv.1.1
    have hden : 0 < 1 - ε ^ 2 := by nlinarith only [hε.1, hε.2]
    have him : 0 < (cutCenter v ε).im := by
      simp only [cutCenter, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
        Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_add]
      exact div_pos (mul_pos hvim (by positivity)) hden
    intro heq
    rw [heq, Complex.zero_im] at him
    exact (lt_irrefl _ him)
  have houterCutIntersections (j : Fin 4) :
      (⋃ v ∈ B, outerSupport j ∩ Metric.sphere (cutCenter v ε) (cutRadius v ε)).Finite := by
    apply hBfinite.biUnion
    intro v hv
    fin_cases j
    · simpa [outerSupport, Set.inter_def, Metric.mem_sphere, dist_eq_norm] using
        hcircleIntersectionFinite 0 (cutCenter v ε) 1 (cutRadius v ε) (hcutCenterNeZero v hv).symm
    · simpa [outerSupport, Set.inter_def, Metric.mem_sphere, dist_eq_norm, and_comm] using
        hcircleVerticalFinite (cutCenter v ε) (cutRadius v ε) (1 / 2)
    · simpa [outerSupport, Set.inter_def, Metric.mem_sphere, dist_eq_norm, and_comm] using
        hcircleHorizontalFinite (cutCenter v ε) (cutRadius v ε) Y
    · simpa [outerSupport, Set.inter_def, Metric.mem_sphere, dist_eq_norm, and_comm] using
        hcircleVerticalFinite (cutCenter v ε) (cutRadius v ε) (-1 / 2)
  have hretainedOuterFrontier (j : Fin 4) (z : ℂ) (hzK : z ∈ K)
      (hzj : z ∈ outerSupport j) (hzret : z ∉ removed ε) : z ∈ frontier V := by
    have hopen : IsOpen (removed ε)ᶜ := (hremovedClosed ε hε.1 hε.2).isOpen_compl
    have hcl := hopen.inter_closure ⟨hzret, hKsubsetClosureO hzK⟩
    have heq : Ω ε = (removed ε)ᶜ ∩ O := by
      ext w
      exact and_comm
    have hzcl : z ∈ closure (Ω ε) := by
      rw [heq]
      exact hcl
    rw [hfullVFrontier]
    exact Or.inl (Or.inl (Set.mem_iUnion.mpr ⟨j, hzcl, hzj⟩))
  have hremovedFrontier : frontier (removed ε) ⊆
      ⋃ v ∈ B, Metric.sphere (cutCenter v ε) (cutRadius v ε) := by
    intro z hz
    have hzmem : z ∈ removed ε :=
      (hremovedClosed ε hε.1 hε.2).closure_subset hz.1
    obtain ⟨v, hv, hzv⟩ := Set.mem_iUnion₂.mp hzmem
    have hdisk : D v ε = Metric.closedBall (cutCenter v ε) (cutRadius v ε) :=
      (hdisks v ε (hKH hv.1.1) hε.1 hε.2).1
    rw [hdisk] at hzv
    refine Set.mem_iUnion₂.mpr ⟨v, hv, le_antisymm hzv ?_⟩
    by_contra! hlt
    have hball : Metric.ball (cutCenter v ε) (cutRadius v ε) ⊆ removed ε := by
      intro w hw
      exact Set.mem_iUnion₂.mpr ⟨v, hv, hdisk.symm ▸ Metric.ball_subset_closedBall hw⟩
    exact hz.2 (mem_interior_iff_mem_nhds.mpr
      (Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hlt) hball))
  have houterNotO (j : Fin 4) (z : ℂ) (hz : z ∈ outerSupport j) : z ∉ O := by
    intro hO
    fin_cases j
    · have hn : ‖z‖ = 1 := by simpa [outerSupport] using hz
      exact (lt_irrefl (1 : ℝ)) (hn ▸ hO.2.1)
    · have hre : z.re = 1 / 2 := by simpa [outerSupport] using hz
      have hlt := hO.1
      rw [hre, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at hlt
      exact (lt_irrefl (1 / 2 : ℝ)) hlt
    · have him : z.im = Y := by simpa [outerSupport] using hz
      exact (lt_irrefl Y) (him ▸ hO.2.2.2)
    · have hre : z.re = -1 / 2 := by simpa [outerSupport] using hz
      have habs : |z.re| = 1 / 2 := by rw [hre]; norm_num
      exact (lt_irrefl (1 / 2 : ℝ)) (habs ▸ hO.1)
  have houterSubdivision (j : Fin 4) (η : ℝ → ℂ) (hη : ContDiff ℝ 1 η)
      (u v : ℝ) (huv : u < v)
      (hpath : ∀ t ∈ Set.Icc u v, η t ∈ K ∧ η t ∈ outerSupport j)
      (hinj : Set.InjOn η (Set.Ioo u v)) :
      ∃ (cuts : Finset ℝ) (pieces retained : Finset (ℝ × ℝ)),
        u ∈ cuts ∧ v ∈ cuts ∧ (∀ t ∈ cuts, t ∈ Set.Icc u v) ∧
        pieces = (cuts ×ˢ cuts).filter
          (fun p => p.1 < p.2 ∧ ∀ t ∈ cuts, t ≤ p.1 ∨ p.2 ≤ t) ∧
        (∀ p ∈ pieces, u ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ v) ∧
        retained = pieces.filter (fun p => η ((p.1 + p.2) / 2) ∉ removed ε) ∧
        (∀ p ∈ retained, ∀ t ∈ Set.Icc p.1 p.2, η t ∈ frontier V) ∧
        (intervalIntegral (fun t => if η t ∈ removed ε then 0 else L (η t) * deriv η t)
          u v MeasureTheory.volume =
          ∑ p ∈ retained, intervalIntegral (fun t => L (η t) * deriv η t)
            p.1 p.2 MeasureTheory.volume) ∧
        (∀ t, t ∈ cuts ↔ t = u ∨ t = v ∨
          t ∈ Set.Ioo u v ∧ η t ∈ frontier (removed ε)) ∧
        (∀ p ∈ retained, ∀ t ∈ Set.Ioo p.1 p.2, η t ∉ removed ε) := by
    have hfinite : {t ∈ Set.Ioo u v | η t ∈ frontier (removed ε)}.Finite := by
      have himage : (η '' {t ∈ Set.Ioo u v | η t ∈ frontier (removed ε)}).Finite := by
        apply (houterCutIntersections j).subset
        rintro _ ⟨t, ht, rfl⟩
        obtain ⟨w, hw, htw⟩ := Set.mem_iUnion₂.mp (hremovedFrontier ht.2)
        exact Set.mem_iUnion₂.mpr ⟨w, hw, (hpath t ⟨ht.1.1.le, ht.1.2.le⟩).2, htw⟩
      exact himage.of_finite_image (hinj.mono (fun _ ht => ht.1))
    let cuts := insert u (insert v hfinite.toFinset)
    let pieces := (cuts ×ˢ cuts).filter
      (fun p : ℝ × ℝ => p.1 < p.2 ∧ ∀ t ∈ cuts, t ≤ p.1 ∨ p.2 ≤ t)
    let retained := pieces.filter (fun p => η ((p.1 + p.2) / 2) ∉ removed ε)
    have hcuts (t : ℝ) : t ∈ cuts ↔ t = u ∨ t = v ∨
        t ∈ Set.Ioo u v ∧ η t ∈ frontier (removed ε) := by
      simp only [cuts, Finset.mem_insert, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    have hbounds (t : ℝ) (ht : t ∈ cuts) : t ∈ Set.Icc u v := by
      rcases (hcuts t).mp ht with rfl | rfl | ht
      · exact ⟨le_rfl, huv.le⟩
      · exact ⟨huv.le, le_rfl⟩
      · exact ⟨ht.1.1.le, ht.1.2.le⟩
    have hpiece (p : ℝ × ℝ) (hp : p ∈ pieces) :
        u ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ v := by
      have h := Finset.mem_filter.mp hp
      exact ⟨(hbounds _ (Finset.mem_product.mp h.1).1).1, h.2.1,
        (hbounds _ (Finset.mem_product.mp h.1).2).2⟩
    have hsplit (p : ℝ × ℝ) (hp : p ∈ pieces) :
        (∀ t ∈ Set.Ioo p.1 p.2, η t ∉ removed ε) ∨
        (∀ t ∈ Set.Ioo p.1 p.2, η t ∈ interior (removed ε)) := by
      have hgap := (Finset.mem_filter.mp hp).2.2
      have hb := hpiece p hp
      have havoid : ∀ t ∈ Set.Ioo p.1 p.2, η t ∉ frontier (removed ε) := by
        intro t ht hf
        have hcut := (hcuts t).mpr (Or.inr (Or.inr
          ⟨⟨lt_of_le_of_lt hb.1 ht.1, lt_of_lt_of_le ht.2 hb.2.2⟩, hf⟩))
        rcases hgap t hcut with h | h <;> linarith only [h, ht.1, ht.2]
      have hcover : η '' Set.Ioo p.1 p.2 ⊆ (removed ε)ᶜ ∪ interior (removed ε) := by
        rintro _ ⟨t, ht, rfl⟩
        by_cases hm : η t ∈ removed ε
        · exact Or.inr (by_contra (fun hn => havoid t ht ⟨subset_closure hm, hn⟩))
        · exact Or.inl hm
      have hdisjoint : Disjoint (removed ε)ᶜ (interior (removed ε)) :=
        Set.disjoint_left.mpr (fun _ hc hi => hc (interior_subset hi))
      rcases (isPreconnected_Ioo.image _ hη.continuous.continuousOn).subset_or_subset
        (hremovedClosed ε hε.1 hε.2).isOpen_compl isOpen_interior hdisjoint hcover with h | h
      · exact Or.inl (fun t ht => h ⟨t, ht, rfl⟩)
      · exact Or.inr (fun t ht => h ⟨t, ht, rfl⟩)
    have hretained (p : ℝ × ℝ) (hp : p ∈ retained) :
        ∀ t ∈ Set.Icc p.1 p.2, η t ∈ frontier V := by
      obtain ⟨hpp, hmid⟩ := Finset.mem_filter.mp hp
      have hb := hpiece p hpp
      have hout : ∀ t ∈ Set.Ioo p.1 p.2, η t ∉ removed ε := by
        rcases hsplit p hpp with h | h
        · exact h
        · exact False.elim (hmid (interior_subset (h ((p.1 + p.2) / 2)
            ⟨by linarith only [hb.2.1], by linarith only [hb.2.1]⟩)))
      have hsub : Set.Ioo p.1 p.2 ⊆ η ⁻¹' frontier V := by
        intro t ht
        have hpt := hpath t ⟨le_trans hb.1 ht.1.le, le_trans ht.2.le hb.2.2⟩
        exact hretainedOuterFrontier j (η t) hpt.1 hpt.2 (hout t ht)
      have hclosed := closure_minimal hsub (isClosed_frontier.preimage hη.continuous)
      rwa [closure_Ioo hb.2.1.ne] at hclosed
    have hint := hretainedIntegrable η (deriv η) u v hη.continuous hη.continuous_deriv_one
      (fun t ht => by
        have h := hpath t (by simpa only [Set.uIcc_of_le huv.le] using ht)
        exact ⟨h.1, houterNotO j (η t) h.2⟩) ε hε.1 hε.2
    have hlocal (p : ℝ × ℝ) (hp : p ∈ pieces) :
        intervalIntegral (fun t => if η t ∈ removed ε then 0 else L (η t) * deriv η t)
          p.1 p.2 MeasureTheory.volume =
          if p ∈ retained then intervalIntegral (fun t => L (η t) * deriv η t)
            p.1 p.2 MeasureTheory.volume else 0 := by
      have hb := hpiece p hp
      by_cases hm : p ∈ retained
      · rw [if_pos hm]
        apply intervalIntegral.integral_congr_Ioo_of_le hb.2.1.le
        intro t ht
        rcases hsplit p hp with h | h
        · exact if_neg (h t ht)
        · exact False.elim ((Finset.mem_filter.mp hm).2 (interior_subset
            (h ((p.1 + p.2) / 2) ⟨by linarith only [hb.2.1], by linarith only [hb.2.1]⟩)))
      · rw [if_neg hm]
        calc
          _ = intervalIntegral (fun _ : ℝ => (0 : ℂ)) p.1 p.2 MeasureTheory.volume := by
            apply intervalIntegral.integral_congr_Ioo_of_le hb.2.1.le
            intro t ht
            rcases hsplit p hp with h | h
            · exact False.elim (hm (Finset.mem_filter.mpr ⟨hp,
                h ((p.1 + p.2) / 2) ⟨by linarith only [hb.2.1], by linarith only [hb.2.1]⟩⟩))
            · exact if_pos (interior_subset (h t ht))
          _ = 0 := intervalIntegral.integral_zero
    refine ⟨cuts, pieces, retained, (hcuts u).mpr (Or.inl rfl),
      (hcuts v).mpr (Or.inr (Or.inl rfl)), hbounds, rfl, hpiece, rfl, hretained, ?_, hcuts, ?_⟩
    · calc
        _ = ∑ p ∈ pieces, intervalIntegral
            (fun t => if η t ∈ removed ε then 0 else L (η t) * deriv η t)
              p.1 p.2 MeasureTheory.volume :=
          (hfiniteSubdivision cuts u v ((hcuts u).mpr (Or.inl rfl))
            ((hcuts v).mpr (Or.inr (Or.inl rfl))) hbounds _ hint).symm
        _ = ∑ p ∈ pieces, if p ∈ retained then
            intervalIntegral (fun t => L (η t) * deriv η t) p.1 p.2 MeasureTheory.volume else 0 :=
          Finset.sum_congr rfl hlocal
        _ = _ := by rw [← Finset.sum_filter]; congr 1; ext p; simp only [retained,
          Finset.mem_filter, and_self_left]
    · intro p hp t ht
      obtain ⟨hpp, hmid⟩ := Finset.mem_filter.mp hp
      rcases hsplit p hpp with hout | hin
      · exact hout t ht
      · have hb := hpiece p hpp
        exact False.elim (hmid (interior_subset (hin ((p.1 + p.2) / 2)
          ⟨by linarith only [hb.2.1], by linarith only [hb.2.1]⟩)))
  let outerPath : Fin 4 → ℝ → ℂ := ![circleMap 0 1,
    (fun t => (1 / 2 : ℂ) + (t : ℂ) * Complex.I),
    (fun t => (t : ℂ) + (Y : ℂ) * Complex.I),
    (fun t => (-1 / 2 : ℂ) + (t : ℂ) * Complex.I)]
  let outerLo : Fin 4 → ℝ := ![Real.pi / 3, Real.sqrt 3 / 2, -1 / 2, Real.sqrt 3 / 2]
  let outerHi : Fin 4 → ℝ := ![2 * Real.pi / 3, Y, 1 / 2, Y]
  have houterBounds (j : Fin 4) : outerLo j < outerHi j := by
    have hbottom : Real.sqrt 3 / 2 < Y := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg 3, hY]
    fin_cases j <;> norm_num [outerLo, outerHi] <;> linarith [Real.pi_pos]
  have houterSmooth (j : Fin 4) : ContDiff ℝ 1 (outerPath j) := by
    fin_cases j
    · exact contDiff_circleMap 0 1
    · change ContDiff ℝ 1 (fun t : ℝ => (1 / 2 : ℂ) + (t : ℂ) * Complex.I)
      exact contDiff_const.add (Complex.ofRealCLM.contDiff.mul contDiff_const)
    · change ContDiff ℝ 1 (fun t : ℝ => (t : ℂ) + (Y : ℂ) * Complex.I)
      exact Complex.ofRealCLM.contDiff.add contDiff_const
    · change ContDiff ℝ 1 (fun t : ℝ => (-1 / 2 : ℂ) + (t : ℂ) * Complex.I)
      exact contDiff_const.add (Complex.ofRealCLM.contDiff.mul contDiff_const)
  have houterPathMem (j : Fin 4) (t : ℝ) (ht : t ∈ Set.Icc (outerLo j) (outerHi j)) :
      outerPath j t ∈ K ∧ outerPath j t ∈ outerSupport j := by
    have hside (x : ℝ) (hx : |x| = 1 / 2) (t : ℝ)
        (ht : t ∈ Set.Icc (Real.sqrt 3 / 2) Y) :
        (x : ℂ) + (t : ℂ) * Complex.I ∈ K := by
      have hpos : 0 < t := lt_of_lt_of_le (by positivity) ht.1
      have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
      have hx2 : x ^ 2 = 1 / 4 := by nlinarith only [sq_abs x, hx]
      have hn : 1 ≤ ‖(x : ℂ) + (t : ℂ) * Complex.I‖ := by
        have heq := Complex.sq_norm_sub_sq_re ((x : ℂ) + (t : ℂ) * Complex.I)
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, mul_zero, sub_self, add_zero,
          Complex.add_im, Complex.mul_im, mul_one, zero_add] at heq
        nlinarith only [heq, hx2, hs, ht.1, Real.sqrt_nonneg 3, hpos,
          norm_nonneg ((x : ℂ) + (t : ℂ) * Complex.I)]
      exact ⟨by simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_self,
          add_zero] using hx.le,
        hn, by simpa using hpos, by simpa using ht.2⟩
    fin_cases j
    · refine ⟨(hfullArcMem t ht).1, ?_⟩
      change ‖circleMap 0 1 t‖ = 1
      simp only [norm_circleMap_zero, abs_one]
    · refine ⟨by simpa [outerPath] using hside (1 / 2) (by norm_num) t ht, ?_⟩
      change ((1 / 2 : ℂ) + (t : ℂ) * Complex.I).re = 1 / 2
      simp
    · have hzY : 0 < Y := lt_trans zero_lt_one hY
      have hn : Y ≤ ‖(t : ℂ) + (Y : ℂ) * Complex.I‖ := by
        simpa only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
          Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_add,
          abs_of_pos hzY] using Complex.abs_im_le_norm ((t : ℂ) + (Y : ℂ) * Complex.I)
      refine ⟨⟨?_, le_trans hY.le hn, ?_, ?_⟩, ?_⟩
      · change |((t : ℂ) + (Y : ℂ) * Complex.I).re| ≤ 1 / 2
        have ht' : -(1 / 2 : ℝ) ≤ t ∧ t ≤ 1 / 2 := by simpa [outerLo, outerHi, neg_div] using ht
        simpa using (abs_le.mpr ht')
      · change 0 < ((t : ℂ) + (Y : ℂ) * Complex.I).im
        simpa using hzY
      · simp [outerPath]
      · change ((t : ℂ) + (Y : ℂ) * Complex.I).im = Y
        simp
    · refine ⟨by simpa [outerPath] using hside (-1 / 2) (by norm_num) t ht, ?_⟩
      change ((-1 / 2 : ℂ) + (t : ℂ) * Complex.I).re = -1 / 2
      simp
  have houterInjective (j : Fin 4) :
      Set.InjOn (outerPath j) (Set.Ioo (outerLo j) (outerHi j)) := by
    intro x hx y hy hxy
    fin_cases j
    · apply eq_of_circleMap_eq (by norm_num : (1 : ℝ) ≠ 0) _ hxy
      change Real.pi / 3 < x ∧ x < 2 * Real.pi / 3 at hx
      change Real.pi / 3 < y ∧ y < 2 * Real.pi / 3 at hy
      rw [abs_lt]
      constructor <;> linarith only [hx.1, hx.2, hy.1, hy.2, Real.pi_pos]
    · simpa [outerPath] using congrArg Complex.im hxy
    · simpa [outerPath] using congrArg Complex.re hxy
    · simpa [outerPath] using congrArg Complex.im hxy
  choose outerCuts outerPieces outerRetained houterCertificate using
    (fun j => houterSubdivision j (outerPath j) (houterSmooth j)
      (outerLo j) (outerHi j) (houterBounds j) (houterPathMem j) (houterInjective j))
  have houterGridSubdivision (j : Fin 4) (p : ℝ × ℝ) (hp : p ∈ outerRetained j) := by
    have hpieces : p ∈ outerPieces j := by
      rw [(houterCertificate j).2.2.2.2.2.1] at hp
      exact (Finset.mem_filter.mp hp).1
    have hb := (houterCertificate j).2.2.2.2.1 p hpieces
    exact hgenuineSubdivision (outerPath j) (houterSmooth j) p.1 p.2 hb.2.1
      ((houterCertificate j).2.2.2.2.2.2.1 p hp)
      ((houterInjective j).mono (Set.Ioo_subset_Ioo hb.1 hb.2.2))
  -- Express the actual four outer contour terms with their positive-boundary
  -- orientations: clockwise lower arc, upward right side, leftward top,
  -- and downward left side.
  let outerSign : Fin 4 → ℂ := ![-1, 1, -1, -1]
  let outerIntegral : Fin 4 → ℂ := fun j =>
    intervalIntegral (fun t => if outerPath j t ∈ removed ε then 0 else
      L (outerPath j t) * deriv (outerPath j) t)
      (outerLo j) (outerHi j) MeasureTheory.volume
  have houterIntegralSubdivision (j : Fin 4) :
      outerIntegral j = ∑ p ∈ outerRetained j,
        intervalIntegral (fun t => L (outerPath j t) * deriv (outerPath j) t)
          p.1 p.2 MeasureTheory.volume :=
    (houterCertificate j).2.2.2.2.2.2.2.1
  have houterDeriv (t : ℝ) :
      deriv (outerPath 0) t = Complex.I * circleMap 0 1 t ∧
      deriv (outerPath 1) t = Complex.I ∧
      deriv (outerPath 2) t = 1 ∧
      deriv (outerPath 3) t = Complex.I := by
    have hvertical (x : ℂ) :
        HasDerivAt (fun t : ℝ => x + (t : ℂ) * Complex.I) Complex.I t := by
      simpa using (((hasDerivAt_id t).ofReal_comp).mul_const Complex.I).const_add x
    have htop : HasDerivAt (fun t : ℝ => (t : ℂ) + (Y : ℂ) * Complex.I) 1 t := by
      simpa using ((hasDerivAt_id t).ofReal_comp).add_const ((Y : ℂ) * Complex.I)
    refine ⟨?_, (hvertical _).deriv, htop.deriv, (hvertical _).deriv⟩
    change deriv (circleMap 0 1) t = _
    simp [mul_comm]
  have houterPathEnds (j : Fin 4) :
      outerPath j (outerLo j) = ![ρ + 1, ρ + 1,
        (-1 / 2 : ℂ) + (Y : ℂ) * Complex.I, ρ] j ∧
      outerPath j (outerHi j) = ![ρ, (1 / 2 : ℂ) + (Y : ℂ) * Complex.I,
        (1 / 2 : ℂ) + (Y : ℂ) * Complex.I,
        (-1 / 2 : ℂ) + (Y : ℂ) * Complex.I] j := by
    have hcos : Real.cos (2 * Real.pi / 3) = -1 / 2 := by
      rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring,
        Real.cos_pi_sub, Real.cos_pi_div_three]
      norm_num
    have hsin : Real.sin (2 * Real.pi / 3) = Real.sqrt 3 / 2 := by
      rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring,
        Real.sin_pi_sub, Real.sin_pi_div_three]
    fin_cases j <;> constructor <;> apply Complex.ext <;>
      norm_num [outerPath, outerLo, outerHi, circleMap_zero_re, circleMap_zero_im,
        hcos, hsin, Real.cos_pi_div_three, Real.sin_pi_div_three, ρ]
  have houterRepresentation (j : Fin 4) (z : ℂ) (hzK : z ∈ K)
      (hzj : z ∈ outerSupport j) :
      ∃ t ∈ Set.Icc (outerLo j) (outerHi j), outerPath j t = z := by
    fin_cases j
    · have hn : ‖z‖ = 1 := hzj
      have ha0 : 0 ≤ z.arg := Complex.arg_nonneg_iff.mpr hzK.2.2.1.le
      have haπ : z.arg ≤ Real.pi := Complex.arg_le_pi z
      have hc : Real.cos z.arg = z.re := by
        simpa only [hn, one_mul] using Complex.norm_mul_cos_arg z
      have hcos : Real.cos (2 * Real.pi / 3) = -1 / 2 := by
        rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring,
          Real.cos_pi_sub, Real.cos_pi_div_three]
        norm_num
      have hlow : Real.pi / 3 ≤ z.arg := by
        by_contra! hlt
        have h := Real.cos_lt_cos_of_nonneg_of_le_pi ha0
          (show Real.pi / 3 ≤ Real.pi by linarith [Real.pi_pos]) hlt
        rw [Real.cos_pi_div_three, hc] at h
        linarith only [(abs_le.mp hzK.1).2, h]
      have hhigh : z.arg ≤ 2 * Real.pi / 3 := by
        by_contra! hlt
        have h := Real.cos_lt_cos_of_nonneg_of_le_pi (by positivity) haπ hlt
        rw [hcos, hc] at h
        linarith only [(abs_le.mp hzK.1).1, h]
      refine ⟨z.arg, ⟨hlow, hhigh⟩, ?_⟩
      change circleMap 0 1 z.arg = z
      simpa only [circleMap, zero_add, hn] using Complex.norm_mul_exp_arg_mul_I z
    · refine ⟨z.im, ⟨hKlower z hzK, hzK.2.2.2⟩, ?_⟩
      apply Complex.ext
      · simpa [outerPath] using (show z.re = 1 / 2 from hzj).symm
      · simp [outerPath]
    · refine ⟨z.re, ?_, ?_⟩
      · change (-1 / 2 : ℝ) ≤ z.re ∧ z.re ≤ 1 / 2
        simpa only [neg_div] using abs_le.mp hzK.1
      · apply Complex.ext
        · simp [outerPath]
        · simpa [outerPath] using (show z.im = Y from hzj).symm
    · refine ⟨z.im, ⟨hKlower z hzK, hzK.2.2.2⟩, ?_⟩
      apply Complex.ext
      · simpa [outerPath] using (show z.re = -1 / 2 from hzj).symm
      · simp [outerPath]
  let outerWindow : Fin 4 → Set ℂ := ![
    {z | |z.re| < 1 / 2 ∧ 0 < z.im ∧ z.im < Y},
    {z | -1 / 2 < z.re ∧ 1 < ‖z‖ ∧ 0 < z.im ∧ z.im < Y},
    {z | |z.re| < 1 / 2 ∧ 1 < ‖z‖ ∧ 0 < z.im},
    {z | z.re < 1 / 2 ∧ 1 < ‖z‖ ∧ 0 < z.im ∧ z.im < Y}]
  have houterWindowOpen (j : Fin 4) : IsOpen (outerWindow j) := by
    fin_cases j
    · exact (isOpen_lt Complex.continuous_re.abs continuous_const).inter
        ((isOpen_lt continuous_const Complex.continuous_im).inter
          (isOpen_lt Complex.continuous_im continuous_const))
    · exact (isOpen_lt continuous_const Complex.continuous_re).inter
        ((isOpen_lt continuous_const continuous_norm).inter
          ((isOpen_lt continuous_const Complex.continuous_im).inter
            (isOpen_lt Complex.continuous_im continuous_const)))
    · exact (isOpen_lt Complex.continuous_re.abs continuous_const).inter
        ((isOpen_lt continuous_const continuous_norm).inter
          (isOpen_lt continuous_const Complex.continuous_im))
    · exact (isOpen_lt Complex.continuous_re continuous_const).inter
        ((isOpen_lt continuous_const continuous_norm).inter
          ((isOpen_lt continuous_const Complex.continuous_im).inter
            (isOpen_lt Complex.continuous_im continuous_const)))
  have houterPathWindow (j : Fin 4) (t : ℝ)
      (ht : t ∈ Set.Ioo (outerLo j) (outerHi j)) : outerPath j t ∈ outerWindow j := by
    have hside (x : ℝ) (hx : x = -1 / 2 ∨ x = 1 / 2) (t : ℝ)
        (ht : Real.sqrt 3 / 2 < t) :
        1 < ‖(x : ℂ) + (t : ℂ) * Complex.I‖ := by
      have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
      have hx2 : x ^ 2 = 1 / 4 := by rcases hx with rfl | rfl <;> norm_num
      have heq := Complex.sq_norm_sub_sq_re ((x : ℂ) + (t : ℂ) * Complex.I)
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, sub_self, add_zero,
        Complex.add_im, Complex.mul_im, mul_one, zero_add] at heq
      nlinarith only [heq, hs, hx2, ht, Real.sqrt_nonneg 3,
        norm_nonneg ((x : ℂ) + (t : ℂ) * Complex.I)]
    fin_cases j
    · have ht' : Real.pi / 3 < t ∧ t < 2 * Real.pi / 3 := ht
      have ht0 : 0 < t := by linarith [Real.pi_pos]
      have htπ : t < Real.pi := by linarith [Real.pi_pos]
      have hcos : Real.cos (2 * Real.pi / 3) = -1 / 2 := by
        rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring,
          Real.cos_pi_sub, Real.cos_pi_div_three]
        norm_num
      have hlo := Real.cos_lt_cos_of_nonneg_of_le_pi ht0.le
        (show 2 * Real.pi / 3 ≤ Real.pi by linarith [Real.pi_pos]) ht'.2
      have hhi := Real.cos_lt_cos_of_nonneg_of_le_pi (by positivity : 0 ≤ Real.pi / 3)
        htπ.le ht'.1
      rw [hcos] at hlo
      rw [Real.cos_pi_div_three] at hhi
      change |(circleMap 0 1 t).re| < 1 / 2 ∧ 0 < (circleMap 0 1 t).im ∧
        (circleMap 0 1 t).im < Y
      simp only [circleMap_zero_re, circleMap_zero_im, one_mul]
      exact ⟨abs_lt.mpr ⟨by linarith, hhi⟩, Real.sin_pos_of_pos_of_lt_pi ht0 htπ,
        lt_of_le_of_lt (Real.sin_le_one t) hY⟩
    · change -1 / 2 < _ ∧ 1 < _ ∧ 0 < _ ∧ _ < Y
      have ht' : Real.sqrt 3 / 2 < t ∧ t < Y := ht
      refine ⟨by norm_num [outerPath], by simpa [outerPath] using hside _ (Or.inr rfl) t ht'.1, ?_, ?_⟩
      · simpa [outerPath] using lt_trans (by positivity : (0 : ℝ) < Real.sqrt 3 / 2) ht'.1
      · simpa [outerPath] using ht'.2
    · have ht' : -1 / 2 < t ∧ t < 1 / 2 := ht
      have hy : 0 < Y := lt_trans zero_lt_one hY
      have hn : Y ≤ ‖(t : ℂ) + (Y : ℂ) * Complex.I‖ := by
        simpa only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
          Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_add,
          abs_of_pos hy] using Complex.abs_im_le_norm ((t : ℂ) + (Y : ℂ) * Complex.I)
      refine ⟨?_, lt_of_lt_of_le hY hn, ?_⟩
      · have habs : |t| < 1 / 2 := abs_lt.mpr ⟨by linarith only [ht'.1], ht'.2⟩
        simpa [outerPath] using habs
      · simpa [outerPath] using hy
    · have ht' : Real.sqrt 3 / 2 < t ∧ t < Y := ht
      refine ⟨by norm_num [outerPath], by simpa [outerPath] using hside _ (Or.inl rfl) t ht'.1, ?_, ?_⟩
      · simpa [outerPath] using lt_trans (by positivity : (0 : ℝ) < Real.sqrt 3 / 2) ht'.1
      · simpa [outerPath] using ht'.2

  have houterWindowUnique (j : Fin 4) (z : ℂ) (hz : z ∈ outerWindow j)
      (k : Fin 4) (hzk : z ∈ outerSupport k) : k = j := by
    fin_cases j <;> fin_cases k <;> try rfl
    all_goals
      norm_num [outerWindow, outerSupport, abs_lt] at hz hzk
      exfalso
      linarith only [hz, hzk]
  let outerSide : Fin 4 → ℂ → Prop := fun j z =>
    ![1 < ‖z‖, z.re < 1 / 2, z.im < Y, -1 / 2 < z.re] j
  have houterWindowSide (j : Fin 4) (z : ℂ) (hz : z ∈ outerWindow j) :
      z ∈ O ↔ outerSide j z := by
    fin_cases j <;> norm_num [outerWindow, outerSide, O, abs_lt] at hz ⊢ <;> tauto
  let outerNormal : Fin 4 → ℂ → ℂ → ℝ := fun j z u =>
    ![z.re * u.re + z.im * u.im, -u.re, -u.im, u.re] j
  have houterDet (j : Fin 4) (s : ℝ) (u : ℂ) :
      (deriv (outerPath j) s * star u).im =
        if j = 1 then -outerNormal j (outerPath j s) u
        else outerNormal j (outerPath j s) u := by
    fin_cases j
    · change (deriv (outerPath 0) s * star u).im = outerNormal 0 (outerPath 0 s) u
      rw [(houterDeriv s).1]
      simp [outerNormal, outerPath, Complex.mul_im, Complex.mul_re]
      ring
    · change (deriv (outerPath 1) s * star u).im = -outerNormal 1 (outerPath 1 s) u
      rw [(houterDeriv s).2.1]
      simp [outerNormal]
    · change (deriv (outerPath 2) s * star u).im = outerNormal 2 (outerPath 2 s) u
      rw [(houterDeriv s).2.2.1]
      simp [outerNormal]
    · change (deriv (outerPath 3) s * star u).im = outerNormal 3 (outerPath 3 s) u
      rw [(houterDeriv s).2.2.2]
      simp [outerNormal]

  have htopNotRemoved (t : ℝ) : outerPath 2 t ∉ removed ε := by
    intro hmem
    obtain ⟨v, hv, htv⟩ := Set.mem_iUnion₂.mp hmem
    have hlt := hbelowTop v hv.1 htv
    change (outerPath 2 t).im < Y at hlt
    simp [outerPath] at hlt
  have houterContour :
      intervalIntegral (retainedArc ε) (2 * Real.pi / 3) (Real.pi / 3)
          MeasureTheory.volume + verticalContribution ε + top Y =
        ∑ j : Fin 4, outerSign j * outerIntegral j := by
    have hbottom : intervalIntegral (retainedArc ε)
        (2 * Real.pi / 3) (Real.pi / 3) MeasureTheory.volume = -outerIntegral 0 := by
      rw [intervalIntegral.integral_symm]
      congr 1
      apply intervalIntegral.integral_congr
      intro t _
      change (if outerPath 0 t ∈ removed ε then 0 else
        L (outerPath 0 t) * (Complex.I * circleMap 0 1 t)) =
          (if outerPath 0 t ∈ removed ε then 0 else
            L (outerPath 0 t) * deriv (outerPath 0) t)
      rw [(houterDeriv t).1]
    have hright : outerIntegral 1 = intervalIntegral (fun t : ℝ =>
        if ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) ∈ removed ε then 0 else
          L ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) * Complex.I)
        (Real.sqrt 3 / 2) Y MeasureTheory.volume := by
      apply intervalIntegral.integral_congr
      intro t _
      dsimp only
      rw [(houterDeriv t).2.1]
      rfl
    have hleft : intervalIntegral (fun t : ℝ =>
        if ((-1 / 2 : ℂ) + (t : ℂ) * Complex.I) ∈ removed ε then 0 else
          L ((-1 / 2 : ℂ) + (t : ℂ) * Complex.I) * Complex.I)
        Y (Real.sqrt 3 / 2) MeasureTheory.volume = -outerIntegral 3 := by
      rw [intervalIntegral.integral_symm]
      congr 1
      apply intervalIntegral.integral_congr
      intro t _
      dsimp only
      rw [(houterDeriv t).2.2.2]
      rfl
    have htop : top Y = -outerIntegral 2 := by
      rw [show top Y = -intervalIntegral
          (fun t : ℝ => L ((t : ℂ) + (Y : ℂ) * Complex.I))
          (-1 / 2) (1 / 2) MeasureTheory.volume from intervalIntegral.integral_symm _ _]
      congr 1
      apply intervalIntegral.integral_congr
      intro t _
      dsimp only
      rw [if_neg (htopNotRemoved t), (houterDeriv t).2.2.1, mul_one]
      rfl
    rw [hbottom, htop]
    change -outerIntegral 0 + (_ + _) + -outerIntegral 2 = _
    rw [← hright, hleft]
    simp only [Fin.sum_univ_succ, outerSign, Matrix.cons_val_zero,
      Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero, neg_one_mul, one_mul]
    change -outerIntegral 0 + (outerIntegral 1 + -outerIntegral 3) + -outerIntegral 2 =
      -outerIntegral 0 + (outerIntegral 1 + (-outerIntegral 2 + -outerIntegral 3))
    ring
  choose outerGridCuts outerGridPieces outerGridCell houterGridCertificate using
    (fun (j : Fin 4) (p : {p // p ∈ outerRetained j}) =>
      houterGridSubdivision j p.1 p.2)
  have houterEndCorners (j : Fin 4) :
      outerPath j (outerLo j) ∈ gridCorners ∧ outerPath j (outerHi j) ∈ gridCorners := by
    have hbase : ({ρ, ρ + 1, (-1 / 2 : ℂ) + (Y : ℂ) * Complex.I,
        (1 / 2 : ℂ) + (Y : ℂ) * Complex.I} : Set ℂ) ⊆ gridCorners :=
      fun _ hz => Or.inl (Or.inl hz)
    constructor
    · apply hbase
      rw [(houterPathEnds j).1]
      fin_cases j <;> simp
    · apply hbase
      rw [(houterPathEnds j).2]
      fin_cases j <;> simp
  have hgridPointNotCorner (z : ℂ)
      (hz : ∃ n : ℤ, z.re = a.re + n * d ∨ z.im = a.im + n * d) : z ∉ gridCorners := by
    intro hcorner
    obtain ⟨n, hn | hn⟩ := hz
    · exact (hgridCorners z hcorner n).1 hn.symm
    · exact (hgridCorners z hcorner n).2 hn.symm
  have hgridCrossingNotCorner (z : ℂ) (hz : z ∈ gridCrossings) : z ∉ gridCorners := by
    apply hgridPointNotCorner z
    obtain ⟨i, _, hz⟩ := Set.mem_iUnion₂.mp hz
    rcases hz with (h | h) | (h | h)
    · exact ⟨i.1, Or.inl h.2⟩
    · exact ⟨i.1 + 1, Or.inl h.2⟩
    · exact ⟨i.2, Or.inr h.2⟩
    · exact ⟨i.2 + 1, Or.inr h.2⟩
  have houterRemovedCorner (j : Fin 4) (z : ℂ) (hz : z ∈ frontier V)
      (hzj : z ∈ outerSupport j) (hm : z ∈ removed ε) : z ∈ gridCorners := by
    have hcl : z ∈ closure (Ω ε) :=
      closure_mono (show V ⊆ Ω ε from fun _ hw => hw.1) (frontier_subset_closure hz)
    have houtside : closure (Ω ε) ⊆ (interior (removed ε))ᶜ := by
      apply closure_minimal _ isOpen_interior.isClosed_compl
      exact fun _ hw hi => hw.2 (interior_subset hi)
    have hf : z ∈ frontier (removed ε) := ⟨subset_closure hm, houtside hcl⟩
    obtain ⟨v, hv, hzv⟩ := Set.mem_iUnion₂.mp (hremovedFrontier hf)
    have hparam : z ∈ γ v ε '' Set.Icc (cutEnd v) (cutStart v) := by
      rw [← hboundaryCircleCoverage v hv]
      exact ⟨hcl, hzv⟩
    obtain ⟨t, ht, heq⟩ := hparam
    rcases eq_or_lt_of_le ht.1 with hlo | hlo
    · rw [← heq, ← hlo]
      exact Or.inr ⟨v, hv, rfl⟩
    · rcases eq_or_lt_of_le ht.2 with hhi | hhi
      · rw [← heq, hhi]
        exact Or.inl (Or.inr ⟨v, hv, rfl⟩)
      · exact False.elim (houterNotO j z hzj (heq ▸ hboundaryArcInterior v hv t ⟨hlo, hhi⟩))
  have houterCoarseEndpointCorner (j : Fin 4) (p : {p // p ∈ outerRetained j})
      (t : ℝ) (ht : t = p.1.1 ∨ t = p.1.2) : outerPath j t ∈ gridCorners := by
    have hpp : p.1 ∈ outerPieces j := by
      have hp := (congrArg (fun s : Finset (ℝ × ℝ) => p.1 ∈ s)
        (houterCertificate j).2.2.2.2.2.1).mp p.2
      exact (Finset.mem_filter.mp hp).1
    have hb := (houterCertificate j).2.2.2.2.1 p.1 hpp
    have hpair := hpp
    rw [(houterCertificate j).2.2.2.1] at hpair
    have hpairs := Finset.mem_product.mp (Finset.mem_filter.mp hpair).1
    have hcut : t ∈ outerCuts j := by rcases ht with rfl | rfl <;> tauto
    have htclosed : t ∈ Set.Icc p.1.1 p.1.2 := by
      rcases ht with rfl | rfl
      · exact ⟨le_rfl, hb.2.1.le⟩
      · exact ⟨hb.2.1.le, le_rfl⟩
    rcases ((houterCertificate j).2.2.2.2.2.2.2.2.1 t).mp hcut with h | h | h
    · rw [h]
      exact (houterEndCorners j).1
    · rw [h]
      exact (houterEndCorners j).2
    · exact houterRemovedCorner j (outerPath j t)
        ((houterCertificate j).2.2.2.2.2.2.1 p.1 p.2 t htclosed)
        (houterPathMem j t ⟨le_trans hb.1 htclosed.1, le_trans htclosed.2 hb.2.2⟩).2
        ((hremovedClosed ε hε.1 hε.2).closure_subset h.2.1)

  let outerEndpoints : ℂ := ∑ j : Fin 4, outerSign j *
    ∑ p : {p // p ∈ outerRetained j}, ∑ q ∈ outerGridPieces j p,
      (cellPrimitive (outerGridCell j p q) (outerPath j q.2) -
        cellPrimitive (outerGridCell j p q) (outerPath j q.1))
  have houterEndpointSum :
      intervalIntegral (retainedArc ε) (2 * Real.pi / 3) (Real.pi / 3)
          MeasureTheory.volume + verticalContribution ε + top Y = outerEndpoints := by
    rw [houterContour]
    apply Finset.sum_congr rfl
    intro j _
    apply congrArg (outerSign j * ·)
    rw [houterIntegralSubdivision, ← Finset.sum_coe_sort]
    apply Finset.sum_congr rfl
    intro p _
    exact (houterGridCertificate j p).2.2.2.2.2.1
  let : Fintype {v // v ∈ B} := hBfinite.fintype
  choose indentationCuts indentationPieces indentationCell hindentationCertificate using
    (fun v : {v // v ∈ B} => hindentationSubdivision v.1 v.2)
  let indentationEndpoints : ℂ := -∑ v : {v // v ∈ B}, ∑ p ∈ indentationPieces v,
    (cellPrimitive (indentationCell v p) (γ v.1 ε p.2) -
      cellPrimitive (indentationCell v p) (γ v.1 ε p.1))
  have hindentationEndpointSum :
      (∑ v ∈ hBfinite.toFinset, indent v (fun _ => cutStart v) (fun _ => cutEnd v) ε) =
        indentationEndpoints := by
    rw [Finset.sum_subtype hBfinite.toFinset (fun v => hBfinite.mem_toFinset)]
    change _ = -(∑ v : {v // v ∈ B}, _)
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro v _
    change intervalIntegral _ (cutStart v.1) (cutEnd v.1) MeasureTheory.volume = _
    rw [intervalIntegral.integral_symm, (hindentationCertificate v).2.2.2.2.2.1]
  let : Fintype {v // v ∈ S} := hSfinite.fintype
  choose excisionCuts excisionPieces excisionCell hexcisionCertificate using
    (fun v : {v // v ∈ S} => hcircleSubdivision v.1 v.2)
  let excisionEndpoints : ℂ := -∑ v : {v // v ∈ S}, ∑ p ∈ excisionPieces v,
    (cellPrimitive (excisionCell v p) (circleMap v.1 r p.2) -
      cellPrimitive (excisionCell v p) (circleMap v.1 r p.1))
  have hexcisionEndpointSum :
      (∑ v ∈ hOzerosFinite.toFinset,
        intervalIntegral (fun t => L (circleMap v r t) * deriv (circleMap v r) t)
          (2 * Real.pi) 0 MeasureTheory.volume) = excisionEndpoints := by
    rw [Finset.sum_subtype hOzerosFinite.toFinset (fun v =>
      show v ∈ hOzerosFinite.toFinset ↔ v ∈ S by
        simp only [S, hzeros, Set.Finite.mem_toFinset])]
    change _ = -(∑ v : {v // v ∈ S}, _)
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro v _
    rw [intervalIntegral.integral_symm, (hexcisionCertificate v).2.2.2.2.2.1]
  have hexcisionArtificialIncidence (v : {v // v ∈ S}) (p : ℝ × ℝ)
      (hp : p ∈ excisionPieces v) (j : Fin 4) (s t : ℝ)
      (ht : t ∈ Set.Ioo (0 : ℝ) 1)
      (heq : circleMap v.1 r s = cellEdge (excisionCell v p) j t) :
      (p.1 = s → ∃! q : ℝ × ℝ, q ∈ retainedPieces (excisionCell v p) j ∧ q.1 = t) ∧
      (p.2 = s → ∃! q : ℝ × ℝ, q ∈ retainedPieces (excisionCell v p) j ∧ q.2 = t) := by
    let i := excisionCell v p
    have hsphere : cellEdge i j t ∈ Metric.sphere v.1 r := by
      rw [← heq]
      exact circleMap_mem_sphere v.1 hr.le s
    have hfront : cellEdge i j t ∈ frontier V := by
      rw [← heq]
      exact (hcircles v.1 v.2).1 ⟨s, rfl⟩
    have hcut : t ∈ edgeCuts i j :=
      (hedgeCutsMem i j t).mpr (Or.inr (Or.inr ⟨⟨ht.1.le, ht.2.le⟩, hfront⟩))
    let normal := (cellEdge i j t - v.1).re * (cellVelocity i j).re +
      (cellEdge i j t - v.1).im * (cellVelocity i j).im
    have hnormal : normal ≠ 0 :=
      hcellCircleNormalNe i j t (v.1, r) (Or.inr ⟨v.1, v.2, rfl⟩) hsphere
    have hdet : (deriv (circleMap v.1 r) s * star (cellVelocity i j)).im = normal := by
      rw [hcircleTangent, heq]
    have hlt : p.1 < p.2 := by
      rw [(hexcisionCertificate v).2.2.2.1] at hp
      exact (Finset.mem_filter.mp hp).2.1
    have hsign := hcellPathEndpointSigns (circleMap v.1 r) s _
      ((differentiable_circleMap v.1 r s).hasDerivAt) i j t heq p.1 p.2 hlt
      (fun x hx => ((hexcisionCertificate v).2.2.2.2.1 p hp).2.1 x ⟨hx.1.le, hx.2.le⟩)
      (by rwa [hdet])
    rw [hdet] at hsign
    have hincidence := hfiniteRetainedEndpointIncidence
      (edgeCuts i j) (edgePieces i j) (retainedPieces i j) (hedgePieceMem i j)
      (fun _ hq => (Finset.mem_filter.mp hq).1) (cellEdge i j) V
      (hretainedPieceInterior i j)
      (fun q hq hn x hx hz => hunretainedPieceExterior i j q hq hn x hx (subset_closure hz))
      0 1 t normal ((hedgeCutsMem i j 0).mpr (Or.inl rfl))
      ((hedgeCutsMem i j 1).mpr (Or.inr (Or.inl rfl))) hcut ht.1 ht.2
      (hexcisionEdgeCrossing i j t v.1 v.2 hsphere)
    exact ⟨fun h => hincidence.1.mpr (hsign.1 h), fun h => hincidence.2.mpr (hsign.2 h)⟩
  have hexcisionGenuineIncidence (i : ℤ × ℤ) (j : Fin 4) (q : ℝ × ℝ)
      (hq : q ∈ retainedPieces i j) (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1)
      (v : {v // v ∈ S}) (s : ℝ) (hs : s ∈ Set.Ioo (0 : ℝ) (2 * Real.pi))
      (heq : cellEdge i j t = circleMap v.1 r s) :
      (q.1 = t → ∃! p : ℝ × ℝ,
        p ∈ excisionPieces v ∧ p.1 = s ∧ excisionCell v p = i) ∧
      (q.2 = t → ∃! p : ℝ × ℝ,
        p ∈ excisionPieces v ∧ p.2 = s ∧ excisionCell v p = i) := by
    have hfront : cellEdge i j t ∈ frontier V := by
      rw [heq]
      exact (hcircles v.1 v.2).1 ⟨s, rfl⟩
    have hcross : cellEdge i j t ∈ gridCrossings := by
      fin_cases j
      · exact hgridCrossingContains _ hfront i.2
          (Or.inr (by simpa using (hcellEdgeCoordinates i 0 t).2))
      · exact hgridCrossingContains _ hfront (i.1 + 1)
          (Or.inl (by simpa using (hcellEdgeCoordinates i 1 t).1))
      · exact hgridCrossingContains _ hfront (i.2 + 1)
          (Or.inr (by simpa using (hcellEdgeCoordinates i 2 t).2))
      · exact hgridCrossingContains _ hfront i.1
          (Or.inl (by simpa using (hcellEdgeCoordinates i 3 t).1))
    have hcut : s ∈ excisionCuts v :=
      ((hexcisionCertificate v).2.2.2.2.2.2 s).mpr
        (Or.inr (Or.inr ⟨hs, heq ▸ hcross⟩))
    have hpieces : ∀ p, p ∈ excisionPieces v ↔ p.1 ∈ excisionCuts v ∧
        p.2 ∈ excisionCuts v ∧ p.1 < p.2 ∧
          ∀ t ∈ excisionCuts v, t ≤ p.1 ∨ p.2 ≤ t := by
      intro p
      rw [(hexcisionCertificate v).2.2.2.1]
      simp only [Finset.mem_filter, Finset.mem_product, and_assoc]
    have hincidence := hfinitePieceIncidence (excisionCuts v) (excisionPieces v)
      hpieces s hcut
    have hsign := hexcisionEndpointOrientation i j q hq t v.1 v.2 s heq
    constructor
    · intro hqt
      obtain ⟨p, hp, hunique⟩ := hincidence.1
        ⟨2 * Real.pi, (hexcisionCertificate v).2.1, hs.2⟩
      refine ⟨p, ⟨hp.1, hp.2, ?_⟩, fun w hw => hunique w ⟨hw.1, hw.2.1⟩⟩
      exact hcellPathEndpointCell (circleMap v.1 r) s _
        (differentiable_circleMap v.1 r s).hasDerivAt i j t ht heq.symm
        (excisionCell v p) p.1 p.2 ((hpieces p).mp hp.1).2.2.1
        ((hexcisionCertificate v).2.2.2.2.1 p hp.1).2.1 (Or.inl ⟨hp.2, hsign.1 hqt⟩)
    · intro hqt
      obtain ⟨p, hp, hunique⟩ := hincidence.2
        ⟨0, (hexcisionCertificate v).1, hs.1⟩
      refine ⟨p, ⟨hp.1, hp.2, ?_⟩, fun w hw => hunique w ⟨hw.1, hw.2.1⟩⟩
      exact hcellPathEndpointCell (circleMap v.1 r) s _
        (differentiable_circleMap v.1 r s).hasDerivAt i j t ht heq.symm
        (excisionCell v p) p.1 p.2 ((hpieces p).mp hp.1).2.2.1
        ((hexcisionCertificate v).2.2.2.2.1 p hp.1).2.1 (Or.inr ⟨hp.2, hsign.2 hqt⟩)
  -- The two parameter endpoints of each excision circle are the same
  -- geometric point in the same cell, so their actual primitive terms cancel.
  have hexcisionSeamReduction (v : {v // v ∈ S}) :
      (∑ p ∈ excisionPieces v,
        (cellPrimitive (excisionCell v p) (circleMap v.1 r p.2) -
          cellPrimitive (excisionCell v p) (circleMap v.1 r p.1))) =
      ∑ p ∈ excisionPieces v,
        ((if p.2 = 2 * Real.pi then 0 else
            cellPrimitive (excisionCell v p) (circleMap v.1 r p.2)) -
          (if p.1 = 0 then 0 else
            cellPrimitive (excisionCell v p) (circleMap v.1 r p.1))) := by
    apply hclosedSubdivisionEndpointReduction (excisionCuts v) (excisionPieces v)
      0 (2 * Real.pi) (hexcisionCertificate v).1 (hexcisionCertificate v).2.1
      (by positivity) _ (circleMap v.1 r) (excisionCell v) gridSquare
      (fun p hp => ((hexcisionCertificate v).2.2.2.2.1 p hp).2.1)
      (by simpa only [zero_add] using periodic_circleMap v.1 r 0)
      (hgridCellUnique _ (hgridCircleSeams v.1 v.2)) cellPrimitive
    intro p
    rw [(hexcisionCertificate v).2.2.2.1]
    simp only [Finset.mem_filter, Finset.mem_product, and_assoc]
  let excisionCrossingEndpoints : ℂ := -∑ v : {v // v ∈ S}, ∑ p ∈ excisionPieces v,
    ((if p.2 = 2 * Real.pi then 0 else
        cellPrimitive (excisionCell v p) (circleMap v.1 r p.2)) -
      (if p.1 = 0 then 0 else
        cellPrimitive (excisionCell v p) (circleMap v.1 r p.1)))
  have hexcisionEndpointReduction : excisionEndpoints = excisionCrossingEndpoints := by
    apply congrArg Neg.neg
    exact Finset.sum_congr rfl (fun v _ => hexcisionSeamReduction v)
  -- Reindex the excision endpoints by the actual retained grid endpoints.
  have hgridLineBoundary (z : ℂ) (i : ℤ × ℤ) (hi : z ∈ gridSquare i)
      (hn : ∃ n : ℤ, z.re = a.re + n * d ∨ z.im = a.im + n * d) :
      z.re = a.re + (i.1 : ℝ) * d ∨ z.re = a.re + ((i.1 : ℝ) + 1) * d ∨
        z.im = a.im + (i.2 : ℝ) * d ∨ z.im = a.im + ((i.2 : ℝ) + 1) * d := by
    obtain ⟨n, hn | hn⟩ := hn
    · have hlo : i.1 ≤ n := by
        exact_mod_cast (le_of_mul_le_mul_right (by linarith only [hi.1, hn]) hd :
          (i.1 : ℝ) ≤ n)
      have hhi : n ≤ i.1 + 1 := by
        exact_mod_cast (le_of_mul_le_mul_right (by linarith only [hi.2.1, hn]) hd :
          (n : ℝ) ≤ (i.1 : ℝ) + 1)
      have heq : n = i.1 ∨ n = i.1 + 1 := by omega
      rcases heq with rfl | rfl
      · exact Or.inl hn
      · exact Or.inr (Or.inl (by simpa only [Int.cast_add, Int.cast_one] using hn))
    · have hlo : i.2 ≤ n := by
        exact_mod_cast (le_of_mul_le_mul_right (by linarith only [hi.2.2.1, hn]) hd :
          (i.2 : ℝ) ≤ n)
      have hhi : n ≤ i.2 + 1 := by
        exact_mod_cast (le_of_mul_le_mul_right (by linarith only [hi.2.2.2, hn]) hd :
          (n : ℝ) ≤ (i.2 : ℝ) + 1)
      have heq : n = i.2 ∨ n = i.2 + 1 := by omega
      rcases heq with rfl | rfl
      · exact Or.inr (Or.inr (Or.inl hn))
      · exact Or.inr (Or.inr (Or.inr (by simpa only [Int.cast_add, Int.cast_one] using hn)))
  have hcrossingCellEdge (z : ℂ) (hz : z ∈ gridCrossings) (i : ℤ × ℤ)
      (hi : z ∈ gridSquare i) :
      ∃ j : Fin 4, ∃ t ∈ Set.Ioo (0 : ℝ) 1, cellEdge i j t = z := by
    obtain ⟨l, _, hz⟩ := Set.mem_iUnion₂.mp hz
    have hfront : z ∈ frontier V := by
      rcases hz with (h | h) | (h | h) <;> exact h.1
    have hline : ∃ n : ℤ, z.re = a.re + n * d ∨ z.im = a.im + n * d := by
      rcases hz with (h | h) | (h | h)
      · exact ⟨l.1, Or.inl h.2⟩
      · exact ⟨l.1 + 1, Or.inl h.2⟩
      · exact ⟨l.2, Or.inr h.2⟩
      · exact ⟨l.2 + 1, Or.inr h.2⟩
    have hedge : z ∈ ⋃ j : Fin 4, cellEdge i j '' Set.Icc 0 1 := by
      rw [hcellBoundarySides]
      exact ⟨hi, hgridLineBoundary z i hi hline⟩
    obtain ⟨j, t, ht, heq⟩ := Set.mem_iUnion.mp hedge
    have ht0 : t ≠ 0 := by
      intro h
      rw [h, (hcellEdgeEndpoints i j).1] at heq
      exact hcellVertexAvoidsFrontier i j (heq.symm ▸ hfront)
    have ht1 : t ≠ 1 := by
      intro h
      rw [h, (hcellEdgeEndpoints i j).2] at heq
      exact hcellVertexAvoidsFrontier i (cellNext j) (heq.symm ▸ hfront)
    exact ⟨j, t, ⟨lt_of_le_of_ne ht.1 ht0.symm, lt_of_le_of_ne ht.2 ht1⟩, heq⟩
  have hcellEdgeInteriorUnique (i : ℤ × ℤ) (j l : Fin 4) (t u : ℝ)
      (ht : t ∈ Set.Ioo (0 : ℝ) 1) (hu : u ∈ Set.Ioo (0 : ℝ) 1)
      (heq : cellEdge i j t = cellEdge i l u) : j = l ∧ t = u := by
    have htd : 0 < t * d ∧ t * d < d :=
      ⟨mul_pos ht.1 hd, by simpa only [one_mul] using mul_lt_mul_of_pos_right ht.2 hd⟩
    have hud : 0 < u * d ∧ u * d < d :=
      ⟨mul_pos hu.1 hd, by simpa only [one_mul] using mul_lt_mul_of_pos_right hu.2 hd⟩
    have hx := congrArg Complex.re heq
    have hy := congrArg Complex.im heq
    rw [(hcellEdgeCoordinates i j t).1, (hcellEdgeCoordinates i l u).1] at hx
    rw [(hcellEdgeCoordinates i j t).2, (hcellEdgeCoordinates i l u).2] at hy
    have hindices : j = l := by
      fin_cases j <;> fin_cases l <;> norm_num at hx hy ⊢ <;>
        linarith only [htd.1, htd.2, hud.1, hud.2, hd, hx, hy]
    subst l
    exact ⟨rfl, hcellEdgeInjective i j heq⟩
  let pieceEndpoint : Bool → (ℝ × ℝ) → ℝ := fun b p => if b then p.2 else p.1
  let circleSeam : Bool → ℝ := fun b => if b then 2 * Real.pi else 0
  let excisionEndpointPieces (v : {v // v ∈ S}) (b : Bool) :=
    (excisionPieces v).filter (fun p => pieceEndpoint b p ≠ circleSeam b)
  let excisionGridEndpoints (v : {v // v ∈ S}) (b : Bool) :=
    retainedGridPieces.filter (fun e => pieceEndpoint b e.2.2 ∈ Set.Ioo (0 : ℝ) 1 ∧
      ∃ s ∈ Set.Ioo (0 : ℝ) (2 * Real.pi),
        cellEdge e.1 e.2.1 (pieceEndpoint b e.2.2) = circleMap v.1 r s)
  have hexcisionEndpointInterior (v : {v // v ∈ S}) (b : Bool) (p : ℝ × ℝ)
      (hp : p ∈ excisionEndpointPieces v b) :
      pieceEndpoint b p ∈ Set.Ioo (0 : ℝ) (2 * Real.pi) ∧
        circleMap v.1 r (pieceEndpoint b p) ∈ gridCrossings := by
    obtain ⟨hpp, hpne⟩ := Finset.mem_filter.mp hp
    have hpairs := hpp
    rw [(hexcisionCertificate v).2.2.2.1] at hpairs
    obtain ⟨hp₁, hp₂⟩ := Finset.mem_product.mp (Finset.mem_filter.mp hpairs).1
    have hlt := (Finset.mem_filter.mp hpairs).2.1
    have h₁ := (hexcisionCertificate v).2.2.1 p.1 hp₁
    have h₂ := (hexcisionCertificate v).2.2.1 p.2 hp₂
    have hmem : pieceEndpoint b p ∈ excisionCuts v := by
      cases b <;> assumption
    have hstrict : pieceEndpoint b p ∈ Set.Ioo (0 : ℝ) (2 * Real.pi) := by
      cases b
      · exact ⟨lt_of_le_of_ne h₁.1 hpne.symm, lt_of_lt_of_le hlt h₂.2⟩
      · exact ⟨lt_of_le_of_lt h₁.1 hlt, lt_of_le_of_ne h₂.2 hpne⟩
    refine ⟨hstrict, ?_⟩
    rcases ((hexcisionCertificate v).2.2.2.2.2.2 _).mp hmem with h | h | h
    · exact (ne_of_gt hstrict.1 h).elim
    · exact (ne_of_lt hstrict.2 h).elim
    · exact h.2
  let excisionEndpointMatch (v : {v // v ∈ S}) (b : Bool)
      (p : ℝ × ℝ) (e : (ℤ × ℤ) × Fin 4 × (ℝ × ℝ)) : Prop :=
    excisionCell v p = e.1 ∧
      circleMap v.1 r (pieceEndpoint b p) = cellEdge e.1 e.2.1 (pieceEndpoint b e.2.2)
  have hexcisionEndpointRow (v : {v // v ∈ S}) (b : Bool) (p : ℝ × ℝ)
      (hp : p ∈ excisionEndpointPieces v b) :
      ∃! e, e ∈ excisionGridEndpoints v b ∧ excisionEndpointMatch v b p e := by
    have hpp := (Finset.mem_filter.mp hp).1
    obtain ⟨hs, hcross⟩ := hexcisionEndpointInterior v b p hp
    have hpairs := hpp
    rw [(hexcisionCertificate v).2.2.2.1] at hpairs
    have hlt := (Finset.mem_filter.mp hpairs).2.1
    have hbound : pieceEndpoint b p ∈ Set.Icc p.1 p.2 := by
      cases b
      · exact ⟨le_rfl, hlt.le⟩
      · exact ⟨hlt.le, le_rfl⟩
    have hcell := ((hexcisionCertificate v).2.2.2.2.1 p hpp).2.1 _ hbound
    obtain ⟨j, t, ht, hpoint⟩ := hcrossingCellEdge _ hcross (excisionCell v p) hcell
    have hinc := hexcisionArtificialIncidence v p hpp j (pieceEndpoint b p) t ht hpoint.symm
    have hq : ∃! q, q ∈ retainedPieces (excisionCell v p) j ∧ pieceEndpoint b q = t := by
      cases b
      · exact hinc.1 rfl
      · exact hinc.2 rfl
    obtain ⟨q, ⟨hq, hqt⟩, hqunique⟩ := hq
    let e : (ℤ × ℤ) × Fin 4 × (ℝ × ℝ) := (excisionCell v p, j, q)
    have he : e ∈ excisionGridEndpoints v b := by
      refine Finset.mem_filter.mpr ⟨(hretainedGridMem e).mpr
        ⟨((hexcisionCertificate v).2.2.2.2.1 p hpp).1, hq⟩, ?_⟩
      exact ⟨hqt.symm ▸ ht, pieceEndpoint b p, hs, by simpa only [e, hqt] using hpoint⟩
    refine ⟨e, ⟨he, rfl, by simpa only [e, hqt] using hpoint.symm⟩, ?_⟩
    intro e' he'
    obtain ⟨he'mem, he'cell, he'point⟩ := he'
    have ht' := (Finset.mem_filter.mp he'mem).2.1
    have hq' := ((hretainedGridMem e').mp (Finset.mem_filter.mp he'mem).1).2
    have hpath : cellEdge (excisionCell v p) j t =
        cellEdge (excisionCell v p) e'.2.1 (pieceEndpoint b e'.2.2) := by
      simpa only [he'cell] using hpoint.trans he'point
    obtain ⟨hj, hparam⟩ := hcellEdgeInteriorUnique _ _ _ _ _ ht ht' hpath
    have hpq : e'.2.2 = q := hqunique e'.2.2
      ⟨by simpa only [he'cell, hj] using hq', hparam.symm⟩
    exact Prod.ext he'cell.symm (Prod.ext hj.symm hpq)
  have hexcisionEndpointColumn (v : {v // v ∈ S}) (b : Bool)
      (e : (ℤ × ℤ) × Fin 4 × (ℝ × ℝ)) (he : e ∈ excisionGridEndpoints v b) :
      ∃! p, p ∈ excisionEndpointPieces v b ∧ excisionEndpointMatch v b p e := by
    obtain ⟨hemem, ht, s, hs, heq⟩ := Finset.mem_filter.mp he
    have hq := ((hretainedGridMem e).mp hemem).2
    have hinc := hexcisionGenuineIncidence e.1 e.2.1 e.2.2 hq
      (pieceEndpoint b e.2.2) ht v s hs heq
    have hp : ∃! p, p ∈ excisionPieces v ∧ pieceEndpoint b p = s ∧ excisionCell v p = e.1 := by
      cases b
      · exact hinc.1 rfl
      · exact hinc.2 rfl
    obtain ⟨p, ⟨hpp, hps, hcell⟩, hpunique⟩ := hp
    have hp : p ∈ excisionEndpointPieces v b := by
      refine Finset.mem_filter.mpr ⟨hpp, ?_⟩
      rw [hps]
      cases b
      · exact ne_of_gt hs.1
      · exact ne_of_lt hs.2
    refine ⟨p, ⟨hp, hcell, by rw [hps]; exact heq.symm⟩, ?_⟩
    intro q hq
    obtain ⟨hqmem, hqcell, hqpoint⟩ := hq
    have hsq := (hexcisionEndpointInterior v b q hqmem).1
    have hparam : pieceEndpoint b q = s := by
      apply eq_of_circleMap_eq hr.ne' _ (hqpoint.trans heq)
      rw [abs_lt]
      constructor <;> linarith only [hs.1, hs.2, hsq.1, hsq.2]
    exact hpunique q ⟨(Finset.mem_filter.mp hqmem).1, hparam, hqcell⟩
  have hexcisionEndpointSumReindex (v : {v // v ∈ S}) (b : Bool) :
      (∑ p ∈ excisionEndpointPieces v b,
        cellPrimitive (excisionCell v p) (circleMap v.1 r (pieceEndpoint b p))) =
      ∑ e ∈ excisionGridEndpoints v b,
        cellPrimitive e.1 (cellEdge e.1 e.2.1 (pieceEndpoint b e.2.2)) := by
    let f := fun p => cellPrimitive (excisionCell v p) (circleMap v.1 r (pieceEndpoint b p))
    let g := fun e : (ℤ × ℤ) × Fin 4 × (ℝ × ℝ) =>
      cellPrimitive e.1 (cellEdge e.1 e.2.1 (pieceEndpoint b e.2.2))
    have hrow (p : ℝ × ℝ) (hp : p ∈ excisionEndpointPieces v b) :
        f p = ∑ e ∈ excisionGridEndpoints v b,
          if excisionEndpointMatch v b p e then f p else 0 := by
      obtain ⟨e, ⟨he, hrel⟩, hu⟩ := hexcisionEndpointRow v b p hp
      rw [Finset.sum_eq_single e, if_pos hrel]
      · intro e' he' hne
        exact if_neg (fun h => hne (hu e' ⟨he', h⟩))
      · exact fun h => (h he).elim
    have hcolumn (e : (ℤ × ℤ) × Fin 4 × (ℝ × ℝ)) (he : e ∈ excisionGridEndpoints v b) :
        (∑ p ∈ excisionEndpointPieces v b,
          if excisionEndpointMatch v b p e then f p else 0) = g e := by
      obtain ⟨p, ⟨hp, hrel⟩, hu⟩ := hexcisionEndpointColumn v b e he
      rw [Finset.sum_eq_single p, if_pos hrel]
      · exact congrArg₂ cellPrimitive hrel.1 hrel.2
      · intro p' hp' hne
        exact if_neg (fun h => hne (hu p' ⟨hp', h⟩))
      · exact fun h => (h hp).elim
    calc
      _ = ∑ p ∈ excisionEndpointPieces v b, ∑ e ∈ excisionGridEndpoints v b,
          if excisionEndpointMatch v b p e then f p else 0 := Finset.sum_congr rfl hrow
      _ = ∑ e ∈ excisionGridEndpoints v b, ∑ p ∈ excisionEndpointPieces v b,
          if excisionEndpointMatch v b p e then f p else 0 := Finset.sum_comm
      _ = _ := Finset.sum_congr rfl hcolumn
  let excisionGridContribution : ℂ := ∑ v : {v // v ∈ S},
    ((∑ e ∈ excisionGridEndpoints v true,
      cellPrimitive e.1 (cellEdge e.1 e.2.1 e.2.2.2)) -
      ∑ e ∈ excisionGridEndpoints v false,
        cellPrimitive e.1 (cellEdge e.1 e.2.1 e.2.2.1))
  have hexcisionGridCancellation : excisionCrossingEndpoints = -excisionGridContribution := by
    apply congrArg Neg.neg
    apply Finset.sum_congr rfl
    intro v _
    rw [Finset.sum_sub_distrib]
    have hsplit (b : Bool) :
        (∑ p ∈ excisionPieces v,
          if pieceEndpoint b p = circleSeam b then 0 else
            cellPrimitive (excisionCell v p) (circleMap v.1 r (pieceEndpoint b p))) =
        ∑ e ∈ excisionGridEndpoints v b,
          cellPrimitive e.1 (cellEdge e.1 e.2.1 (pieceEndpoint b e.2.2)) := by
      rw [← hexcisionEndpointSumReindex v b]
      simp only [excisionEndpointPieces, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro p _
      by_cases h : pieceEndpoint b p = circleSeam b <;> simp [h]
    exact congrArg₂ (· - ·) (hsplit true) (hsplit false)

  -- Match the interior indentation endpoints with retained grid endpoints;
  -- keep the two arc ends explicit for the outer-contour joins.
  have hindentationArtificialIncidence (v : {v // v ∈ B}) (p : ℝ × ℝ)
      (hp : p ∈ indentationPieces v) (j : Fin 4) (s t : ℝ)
      (ht : t ∈ Set.Ioo (0 : ℝ) 1)
      (hs : s ∈ Set.Ioo (cutEnd v.1) (cutStart v.1))
      (heq : γ v.1 ε s = cellEdge (indentationCell v p) j t) :
      (p.1 = s → ∃! q : ℝ × ℝ, q ∈ retainedPieces (indentationCell v p) j ∧ q.1 = t) ∧
      (p.2 = s → ∃! q : ℝ × ℝ, q ∈ retainedPieces (indentationCell v p) j ∧ q.2 = t) := by
    let i := indentationCell v p
    have hsphere : cellEdge i j t ∈ Metric.sphere (cutCenter v.1 ε) (cutRadius v.1 ε) := by
      rw [← heq]
      exact hgammaSphere v.1 (hKH v.2.1.1) ε hε.1 hε.2 s
    have hfront : cellEdge i j t ∈ frontier V := by
      rw [← heq]
      rw [hfullVFrontier]
      exact Or.inl (Or.inr (Set.mem_iUnion₂.mpr
        ⟨v.1, v.2, s, ⟨hs.1.le, hs.2.le⟩, rfl⟩))
    have hcut : t ∈ edgeCuts i j :=
      (hedgeCutsMem i j t).mpr (Or.inr (Or.inr ⟨⟨ht.1.le, ht.2.le⟩, hfront⟩))
    let normal := (cellEdge i j t - cutCenter v.1 ε).re * (cellVelocity i j).re +
      (cellEdge i j t - cutCenter v.1 ε).im * (cellVelocity i j).im
    have hnormal : normal ≠ 0 :=
      hcellCircleNormalNe i j t (cutCenter v.1 ε, cutRadius v.1 ε)
        (Or.inl (Or.inr ⟨v.1, v.2, rfl⟩)) hsphere
    obtain ⟨speed, hspeed, hderiv⟩ := hgammaTangent v.1 ε hε.1 hε.2 s
    have hdet : (deriv (γ v.1 ε) s * star (cellVelocity i j)).im = speed * normal := by
      rw [hderiv, heq]
      simp [normal, i, Complex.mul_im, Complex.mul_re]
      ring
    have hlt : p.1 < p.2 := by
      rw [(hindentationCertificate v).2.2.2.1] at hp
      exact (Finset.mem_filter.mp hp).2.1
    have hsign := hcellPathEndpointSigns (γ v.1 ε) s _
      (((hgammaSmooth v.1 ε hε.1 hε.2).differentiable (by norm_num) s).hasDerivAt) i j t heq p.1 p.2 hlt
      (fun x hx => ((hindentationCertificate v).2.2.2.2.1 p hp).2.1 x ⟨hx.1.le, hx.2.le⟩)
      (by rw [hdet]; exact mul_ne_zero hspeed.ne' hnormal)
    rw [hdet] at hsign
    have hincidence := hfiniteRetainedEndpointIncidence
      (edgeCuts i j) (edgePieces i j) (retainedPieces i j) (hedgePieceMem i j)
      (fun _ hq => (Finset.mem_filter.mp hq).1) (cellEdge i j) V
      (hretainedPieceInterior i j)
      (fun q hq hn x hx hz => hunretainedPieceExterior i j q hq hn x hx (subset_closure hz))
      0 1 t normal ((hedgeCutsMem i j 0).mpr (Or.inl rfl))
      ((hedgeCutsMem i j 1).mpr (Or.inr (Or.inl rfl))) hcut ht.1 ht.2
      (hindentationEdgeCrossing i j t v.1 v.2 s hs heq.symm)
    exact ⟨fun h => hincidence.1.mpr ((mul_pos_iff_of_pos_left hspeed).mp (hsign.1 h)),
      fun h => hincidence.2.mpr (neg_of_mul_neg_right (hsign.2 h) hspeed.le)⟩
  have hindentationGenuineIncidence (i : ℤ × ℤ) (j : Fin 4) (q : ℝ × ℝ)
      (hq : q ∈ retainedPieces i j) (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1)
      (v : {v // v ∈ B}) (s : ℝ) (hs : s ∈ Set.Ioo (cutEnd v.1) (cutStart v.1))
      (heq : cellEdge i j t = γ v.1 ε s) :
      (q.1 = t → ∃! p : ℝ × ℝ,
        p ∈ indentationPieces v ∧ p.1 = s ∧ indentationCell v p = i) ∧
      (q.2 = t → ∃! p : ℝ × ℝ,
        p ∈ indentationPieces v ∧ p.2 = s ∧ indentationCell v p = i) := by
    have hfront : cellEdge i j t ∈ frontier V := by
      rw [heq]
      rw [hfullVFrontier]
      exact Or.inl (Or.inr (Set.mem_iUnion₂.mpr
        ⟨v.1, v.2, s, ⟨hs.1.le, hs.2.le⟩, rfl⟩))
    have hcross : cellEdge i j t ∈ gridCrossings := by
      fin_cases j
      · exact hgridCrossingContains _ hfront i.2
          (Or.inr (by simpa using (hcellEdgeCoordinates i 0 t).2))
      · exact hgridCrossingContains _ hfront (i.1 + 1)
          (Or.inl (by simpa using (hcellEdgeCoordinates i 1 t).1))
      · exact hgridCrossingContains _ hfront (i.2 + 1)
          (Or.inr (by simpa using (hcellEdgeCoordinates i 2 t).2))
      · exact hgridCrossingContains _ hfront i.1
          (Or.inl (by simpa using (hcellEdgeCoordinates i 3 t).1))
    have hcut : s ∈ indentationCuts v :=
      ((hindentationCertificate v).2.2.2.2.2.2 s).mpr
        (Or.inr (Or.inr ⟨hs, heq ▸ hcross⟩))
    have hpieces : ∀ p, p ∈ indentationPieces v ↔ p.1 ∈ indentationCuts v ∧
        p.2 ∈ indentationCuts v ∧ p.1 < p.2 ∧
          ∀ t ∈ indentationCuts v, t ≤ p.1 ∨ p.2 ≤ t := by
      intro p
      rw [(hindentationCertificate v).2.2.2.1]
      simp only [Finset.mem_filter, Finset.mem_product, and_assoc]
    have hincidence := hfinitePieceIncidence (indentationCuts v) (indentationPieces v)
      hpieces s hcut
    have hsign := hindentationEndpointOrientation i j q hq t v.1 v.2 s hs heq
    constructor
    · intro hqt
      obtain ⟨p, hp, hunique⟩ := hincidence.1
        ⟨cutStart v.1, (hindentationCertificate v).2.1, hs.2⟩
      refine ⟨p, ⟨hp.1, hp.2, ?_⟩, fun w hw => hunique w ⟨hw.1, hw.2.1⟩⟩
      exact hcellPathEndpointCell (γ v.1 ε) s _
        ((hgammaSmooth v.1 ε hε.1 hε.2).differentiable (by norm_num) s).hasDerivAt i j t ht heq.symm
        (indentationCell v p) p.1 p.2 ((hpieces p).mp hp.1).2.2.1
        ((hindentationCertificate v).2.2.2.2.1 p hp.1).2.1 (Or.inl ⟨hp.2, hsign.1 hqt⟩)
    · intro hqt
      obtain ⟨p, hp, hunique⟩ := hincidence.2
        ⟨cutEnd v.1, (hindentationCertificate v).1, hs.1⟩
      refine ⟨p, ⟨hp.1, hp.2, ?_⟩, fun w hw => hunique w ⟨hw.1, hw.2.1⟩⟩
      exact hcellPathEndpointCell (γ v.1 ε) s _
        ((hgammaSmooth v.1 ε hε.1 hε.2).differentiable (by norm_num) s).hasDerivAt i j t ht heq.symm
        (indentationCell v p) p.1 p.2 ((hpieces p).mp hp.1).2.2.1
        ((hindentationCertificate v).2.2.2.2.1 p hp.1).2.1 (Or.inr ⟨hp.2, hsign.2 hqt⟩)
  let indentationEnd (v : {v // v ∈ B}) (b : Bool) : ℝ :=
    if b then cutStart v.1 else cutEnd v.1
  let indentationCrossingEndpoints : ℂ := -∑ v : {v // v ∈ B}, ∑ p ∈ indentationPieces v,
    ((if p.2 = cutStart v.1 then 0 else
        cellPrimitive (indentationCell v p) (γ v.1 ε p.2)) -
      (if p.1 = cutEnd v.1 then 0 else
        cellPrimitive (indentationCell v p) (γ v.1 ε p.1)))
  let indentationJoinEndpoints : ℂ := -∑ v : {v // v ∈ B}, ∑ p ∈ indentationPieces v,
    ((if p.2 = cutStart v.1 then cellPrimitive (indentationCell v p) (γ v.1 ε p.2) else 0) -
      (if p.1 = cutEnd v.1 then cellPrimitive (indentationCell v p) (γ v.1 ε p.1) else 0))
  have hindentationEndpointReduction :
      indentationEndpoints = indentationCrossingEndpoints + indentationJoinEndpoints := by
    rw [← neg_add]
    apply congrArg Neg.neg
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _
    split_ifs <;> ring
  let indentationEndpointPieces (v : {v // v ∈ B}) (b : Bool) :=
    (indentationPieces v).filter (fun p => pieceEndpoint b p ≠ indentationEnd v b)
  let indentationGridEndpoints (v : {v // v ∈ B}) (b : Bool) :=
    retainedGridPieces.filter (fun e => pieceEndpoint b e.2.2 ∈ Set.Ioo (0 : ℝ) 1 ∧
      ∃ s ∈ Set.Ioo (cutEnd v.1) (cutStart v.1),
        cellEdge e.1 e.2.1 (pieceEndpoint b e.2.2) = γ v.1 ε s)
  have hindentationEndpointInterior (v : {v // v ∈ B}) (b : Bool) (p : ℝ × ℝ)
      (hp : p ∈ indentationEndpointPieces v b) :
      pieceEndpoint b p ∈ Set.Ioo (cutEnd v.1) (cutStart v.1) ∧
        γ v.1 ε (pieceEndpoint b p) ∈ gridCrossings := by
    obtain ⟨hpp, hpne⟩ := Finset.mem_filter.mp hp
    have hpairs := hpp
    rw [(hindentationCertificate v).2.2.2.1] at hpairs
    obtain ⟨hp₁, hp₂⟩ := Finset.mem_product.mp (Finset.mem_filter.mp hpairs).1
    have hlt := (Finset.mem_filter.mp hpairs).2.1
    have h₁ := (hindentationCertificate v).2.2.1 p.1 hp₁
    have h₂ := (hindentationCertificate v).2.2.1 p.2 hp₂
    have hmem : pieceEndpoint b p ∈ indentationCuts v := by
      cases b <;> assumption
    have hstrict : pieceEndpoint b p ∈ Set.Ioo (cutEnd v.1) (cutStart v.1) := by
      cases b
      · exact ⟨lt_of_le_of_ne h₁.1 hpne.symm, lt_of_lt_of_le hlt h₂.2⟩
      · exact ⟨lt_of_le_of_lt h₁.1 hlt, lt_of_le_of_ne h₂.2 hpne⟩
    refine ⟨hstrict, ?_⟩
    rcases ((hindentationCertificate v).2.2.2.2.2.2 _).mp hmem with h | h | h
    · exact (ne_of_gt hstrict.1 h).elim
    · exact (ne_of_lt hstrict.2 h).elim
    · exact h.2
  let indentationEndpointMatch (v : {v // v ∈ B}) (b : Bool)
      (p : ℝ × ℝ) (e : (ℤ × ℤ) × Fin 4 × (ℝ × ℝ)) : Prop :=
    indentationCell v p = e.1 ∧
      γ v.1 ε (pieceEndpoint b p) = cellEdge e.1 e.2.1 (pieceEndpoint b e.2.2)
  have hindentationEndpointRow (v : {v // v ∈ B}) (b : Bool) (p : ℝ × ℝ)
      (hp : p ∈ indentationEndpointPieces v b) :
      ∃! e, e ∈ indentationGridEndpoints v b ∧ indentationEndpointMatch v b p e := by
    have hpp := (Finset.mem_filter.mp hp).1
    obtain ⟨hs, hcross⟩ := hindentationEndpointInterior v b p hp
    have hpairs := hpp
    rw [(hindentationCertificate v).2.2.2.1] at hpairs
    have hlt := (Finset.mem_filter.mp hpairs).2.1
    have hbound : pieceEndpoint b p ∈ Set.Icc p.1 p.2 := by
      cases b
      · exact ⟨le_rfl, hlt.le⟩
      · exact ⟨hlt.le, le_rfl⟩
    have hcell := ((hindentationCertificate v).2.2.2.2.1 p hpp).2.1 _ hbound
    obtain ⟨j, t, ht, hpoint⟩ := hcrossingCellEdge _ hcross (indentationCell v p) hcell
    have hinc := hindentationArtificialIncidence v p hpp j (pieceEndpoint b p) t ht hs hpoint.symm
    have hq : ∃! q, q ∈ retainedPieces (indentationCell v p) j ∧ pieceEndpoint b q = t := by
      cases b
      · exact hinc.1 rfl
      · exact hinc.2 rfl
    obtain ⟨q, ⟨hq, hqt⟩, hqunique⟩ := hq
    let e : (ℤ × ℤ) × Fin 4 × (ℝ × ℝ) := (indentationCell v p, j, q)
    have he : e ∈ indentationGridEndpoints v b := by
      refine Finset.mem_filter.mpr ⟨(hretainedGridMem e).mpr
        ⟨((hindentationCertificate v).2.2.2.2.1 p hpp).1, hq⟩, ?_⟩
      exact ⟨hqt.symm ▸ ht, pieceEndpoint b p, hs, by simpa only [e, hqt] using hpoint⟩
    refine ⟨e, ⟨he, rfl, by simpa only [e, hqt] using hpoint.symm⟩, ?_⟩
    intro e' he'
    obtain ⟨he'mem, he'cell, he'point⟩ := he'
    have ht' := (Finset.mem_filter.mp he'mem).2.1
    have hq' := ((hretainedGridMem e').mp (Finset.mem_filter.mp he'mem).1).2
    have hpath : cellEdge (indentationCell v p) j t =
        cellEdge (indentationCell v p) e'.2.1 (pieceEndpoint b e'.2.2) := by
      simpa only [he'cell] using hpoint.trans he'point
    obtain ⟨hj, hparam⟩ := hcellEdgeInteriorUnique _ _ _ _ _ ht ht' hpath
    have hpq : e'.2.2 = q := hqunique e'.2.2
      ⟨by simpa only [he'cell, hj] using hq', hparam.symm⟩
    exact Prod.ext he'cell.symm (Prod.ext hj.symm hpq)
  have hindentationEndpointColumn (v : {v // v ∈ B}) (b : Bool)
      (e : (ℤ × ℤ) × Fin 4 × (ℝ × ℝ)) (he : e ∈ indentationGridEndpoints v b) :
      ∃! p, p ∈ indentationEndpointPieces v b ∧ indentationEndpointMatch v b p e := by
    obtain ⟨hemem, ht, s, hs, heq⟩ := Finset.mem_filter.mp he
    have hq := ((hretainedGridMem e).mp hemem).2
    have hinc := hindentationGenuineIncidence e.1 e.2.1 e.2.2 hq
      (pieceEndpoint b e.2.2) ht v s hs heq
    have hp : ∃! p, p ∈ indentationPieces v ∧ pieceEndpoint b p = s ∧ indentationCell v p = e.1 := by
      cases b
      · exact hinc.1 rfl
      · exact hinc.2 rfl
    obtain ⟨p, ⟨hpp, hps, hcell⟩, hpunique⟩ := hp
    have hp : p ∈ indentationEndpointPieces v b := by
      refine Finset.mem_filter.mpr ⟨hpp, ?_⟩
      rw [hps]
      cases b
      · exact ne_of_gt hs.1
      · exact ne_of_lt hs.2
    refine ⟨p, ⟨hp, hcell, by rw [hps]; exact heq.symm⟩, ?_⟩
    intro q hq
    obtain ⟨hqmem, hqcell, hqpoint⟩ := hq
    have hsq := (hindentationEndpointInterior v b q hqmem).1
    have hparam : pieceEndpoint b q = s := by
      exact hgammaInjective v.1 (hKH v.2.1.1) hsq hs (hqpoint.trans heq)
    exact hpunique q ⟨(Finset.mem_filter.mp hqmem).1, hparam, hqcell⟩
  have hindentationEndpointSumReindex (v : {v // v ∈ B}) (b : Bool) :
      (∑ p ∈ indentationEndpointPieces v b,
        cellPrimitive (indentationCell v p) (γ v.1 ε (pieceEndpoint b p))) =
      ∑ e ∈ indentationGridEndpoints v b,
        cellPrimitive e.1 (cellEdge e.1 e.2.1 (pieceEndpoint b e.2.2)) := by
    let f := fun p => cellPrimitive (indentationCell v p) (γ v.1 ε (pieceEndpoint b p))
    let g := fun e : (ℤ × ℤ) × Fin 4 × (ℝ × ℝ) =>
      cellPrimitive e.1 (cellEdge e.1 e.2.1 (pieceEndpoint b e.2.2))
    have hrow (p : ℝ × ℝ) (hp : p ∈ indentationEndpointPieces v b) :
        f p = ∑ e ∈ indentationGridEndpoints v b,
          if indentationEndpointMatch v b p e then f p else 0 := by
      obtain ⟨e, ⟨he, hrel⟩, hu⟩ := hindentationEndpointRow v b p hp
      rw [Finset.sum_eq_single e, if_pos hrel]
      · intro e' he' hne
        exact if_neg (fun h => hne (hu e' ⟨he', h⟩))
      · exact fun h => (h he).elim
    have hcolumn (e : (ℤ × ℤ) × Fin 4 × (ℝ × ℝ)) (he : e ∈ indentationGridEndpoints v b) :
        (∑ p ∈ indentationEndpointPieces v b,
          if indentationEndpointMatch v b p e then f p else 0) = g e := by
      obtain ⟨p, ⟨hp, hrel⟩, hu⟩ := hindentationEndpointColumn v b e he
      rw [Finset.sum_eq_single p, if_pos hrel]
      · exact congrArg₂ cellPrimitive hrel.1 hrel.2
      · intro p' hp' hne
        exact if_neg (fun h => hne (hu p' ⟨hp', h⟩))
      · exact fun h => (h hp).elim
    calc
      _ = ∑ p ∈ indentationEndpointPieces v b, ∑ e ∈ indentationGridEndpoints v b,
          if indentationEndpointMatch v b p e then f p else 0 := Finset.sum_congr rfl hrow
      _ = ∑ e ∈ indentationGridEndpoints v b, ∑ p ∈ indentationEndpointPieces v b,
          if indentationEndpointMatch v b p e then f p else 0 := Finset.sum_comm
      _ = _ := Finset.sum_congr rfl hcolumn
  let indentationGridContribution : ℂ := ∑ v : {v // v ∈ B},
    ((∑ e ∈ indentationGridEndpoints v true,
      cellPrimitive e.1 (cellEdge e.1 e.2.1 e.2.2.2)) -
      ∑ e ∈ indentationGridEndpoints v false,
        cellPrimitive e.1 (cellEdge e.1 e.2.1 e.2.2.1))
  have hindentationGridCancellation : indentationCrossingEndpoints = -indentationGridContribution := by
    apply congrArg Neg.neg
    apply Finset.sum_congr rfl
    intro v _
    rw [Finset.sum_sub_distrib]
    have hsplit (b : Bool) :
        (∑ p ∈ indentationPieces v,
          if pieceEndpoint b p = indentationEnd v b then 0 else
            cellPrimitive (indentationCell v p) (γ v.1 ε (pieceEndpoint b p))) =
        ∑ e ∈ indentationGridEndpoints v b,
          cellPrimitive e.1 (cellEdge e.1 e.2.1 (pieceEndpoint b e.2.2)) := by
      rw [← hindentationEndpointSumReindex v b]
      simp only [indentationEndpointPieces, Finset.sum_filter, ite_not]
    exact congrArg₂ (· - ·) (hsplit true) (hsplit false)

  have hretainedIntegralEndpoint (e : (ℤ × ℤ) × Fin 4 × (ℝ × ℝ))
      (he : e ∈ retainedGridPieces) :
      retainedIntegral e =
        cellPrimitive e.1 (cellEdge e.1 e.2.1 e.2.2.2) -
          cellPrimitive e.1 (cellEdge e.1 e.2.1 e.2.2.1) := by
    obtain ⟨hi, hp⟩ := (hretainedGridMem e).mp he
    have hb := (hedgePieceMem e.1 e.2.1 e.2.2).mp (Finset.mem_filter.mp hp).1
    have hbound : Set.Icc e.2.2.1 e.2.2.2 ⊆ Set.Icc (0 : ℝ) 1 :=
      Set.Icc_subset_Icc (hedgeCutsBounds e.1 e.2.1 hb.1).1
        (hedgeCutsBounds e.1 e.2.1 hb.2.1).2
    apply hprimitiveIntegral (gridSquare e.1) (cellPrimitive e.1) (hcellPrimitive e.1 hi)
      (cellEdge e.1 e.2.1) (fun _ => cellVelocity e.1 e.2.1) e.2.2.1 e.2.2.2
    · intro t ht
      exact hcellEdgeMem e.1 e.2.1 t (hbound
        (by simpa only [Set.uIcc_of_le hb.2.2.1.le] using ht))
    · intro t _
      exact hcellEdgeDeriv e.1 e.2.1 t
    · apply ContinuousOn.intervalIntegrable_of_Icc hb.2.2.1.le
      intro t ht
      have hcl := hretainedPieceClosure e.1 e.2.1 e.2.2 hp t ht
      have hK := hcutClosureK ε ((closure_mono (show V ⊆ Ω ε from fun _ hz => hz.1)) hcl)
      exact (((hLan _ (hKH hK) (hVzeroFree _ hcl)).continuousAt.comp
        (hcellEdgeContinuous e.1 e.2.1).continuousAt).mul continuousAt_const).continuousWithinAt
  let gridEndpoints : ℂ := ∑ e ∈ retainedGridPieces,
    (cellPrimitive e.1 (cellEdge e.1 e.2.1 e.2.2.2) -
      cellPrimitive e.1 (cellEdge e.1 e.2.1 e.2.2.1))
  have hgridEndpointSum :
      (∑ e ∈ retainedGridPieces, retainedIntegral e) = gridEndpoints :=
    Finset.sum_congr rfl hretainedIntegralEndpoint
  have hdisjointGridSum (cells : Finset (ℤ × ℤ)) (pieces : (ℤ × ℤ) → Fin 4 → Finset (ℝ × ℝ))
      (f : ((ℤ × ℤ) × Fin 4 × (ℝ × ℝ)) → ℂ) :
      (∑ e ∈ cells.biUnion (fun i => Finset.univ.biUnion (fun j : Fin 4 =>
        (pieces i j).image (fun p => (i, j, p)))), f e) =
        ∑ i ∈ cells, ∑ j : Fin 4, ∑ p ∈ pieces i j, f (i, j, p) := by
    classical
    rw [Finset.sum_biUnion]
    · apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_biUnion]
      · apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_image
        intro p _ q _ hpq
        exact congrArg (fun e : (ℤ × ℤ) × Fin 4 × (ℝ × ℝ) => e.2.2) hpq
      · intro j _ k _ hne
        apply Finset.disjoint_left.mpr
        intro e he hek
        obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp he
        obtain ⟨q, _, heq⟩ := Finset.mem_image.mp hek
        exact hne (congrArg (fun e : (ℤ × ℤ) × Fin 4 × (ℝ × ℝ) => e.2.1) heq).symm
    · intro i _ k _ hne
      apply Finset.disjoint_left.mpr
      intro e he hek
      obtain ⟨j, _, he⟩ := Finset.mem_biUnion.mp he
      obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp he
      obtain ⟨l, _, hek⟩ := Finset.mem_biUnion.mp hek
      obtain ⟨q, _, heq⟩ := Finset.mem_image.mp hek
      exact hne (congrArg (fun e : (ℤ × ℤ) × Fin 4 × (ℝ × ℝ) => e.1) heq).symm
  -- In each cell the four vertex terms cancel cyclically. Only the
  -- retained edge endpoints on the genuine frontier remain.
  have hgridCellEndpointReduction (i : ℤ × ℤ) :
      (∑ j : Fin 4, ∑ p ∈ retainedPieces i j,
        (cellPrimitive i (cellEdge i j p.2) - cellPrimitive i (cellEdge i j p.1))) =
      ∑ j : Fin 4, ∑ p ∈ retainedPieces i j,
        ((if p.2 = 1 then 0 else cellPrimitive i (cellEdge i j p.2)) -
          (if p.1 = 0 then 0 else cellPrimitive i (cellEdge i j p.1))) := by
    have hbalance :
        (∑ j : Fin 4, ∑ p ∈ retainedPieces i j,
          if p.2 = 1 then cellPrimitive i (cellEdge i j p.2) else 0) =
        ∑ j : Fin 4, ∑ p ∈ retainedPieces i j,
          if p.1 = 0 then cellPrimitive i (cellEdge i j p.1) else 0 := by
      simp_rw [(hgridCellVertexSums i _ (cellPrimitive i)).2,
        (hgridCellVertexSums i _ (cellPrimitive i)).1]
      exact Equiv.sum_comp cellNext
        (fun j => if cellVertex i j ∈ V then cellPrimitive i (cellVertex i j) else 0)
    have hsplit (j : Fin 4) (p : ℝ × ℝ) :
        cellPrimitive i (cellEdge i j p.2) - cellPrimitive i (cellEdge i j p.1) =
        ((if p.2 = 1 then 0 else cellPrimitive i (cellEdge i j p.2)) -
          (if p.1 = 0 then 0 else cellPrimitive i (cellEdge i j p.1))) +
        ((if p.2 = 1 then cellPrimitive i (cellEdge i j p.2) else 0) -
          (if p.1 = 0 then cellPrimitive i (cellEdge i j p.1) else 0)) := by
      split_ifs <;> ring
    calc
      _ = (∑ j : Fin 4, ∑ p ∈ retainedPieces i j,
          ((if p.2 = 1 then 0 else cellPrimitive i (cellEdge i j p.2)) -
            (if p.1 = 0 then 0 else cellPrimitive i (cellEdge i j p.1)))) +
        ((∑ j : Fin 4, ∑ p ∈ retainedPieces i j,
          if p.2 = 1 then cellPrimitive i (cellEdge i j p.2) else 0) -
          ∑ j : Fin 4, ∑ p ∈ retainedPieces i j,
            if p.1 = 0 then cellPrimitive i (cellEdge i j p.1) else 0) := by
        simp_rw [hsplit, Finset.sum_add_distrib, Finset.sum_sub_distrib]
      _ = _ := by rw [hbalance, sub_self, add_zero]
  let gridCrossingEndpoints : ℂ := ∑ i ∈ hgridFinite.toFinset,
    ∑ j : Fin 4, ∑ p ∈ retainedPieces i j,
      ((if p.2 = 1 then 0 else cellPrimitive i (cellEdge i j p.2)) -
        (if p.1 = 0 then 0 else cellPrimitive i (cellEdge i j p.1)))
  have hgridEndpointReduction : gridEndpoints = gridCrossingEndpoints := by
    dsimp only [gridEndpoints, gridCrossingEndpoints, retainedGridPieces]
    rw [hdisjointGridSum]
    exact Finset.sum_congr rfl (fun i _ => hgridCellEndpointReduction i)
  -- The hole disks are disjoint, so each retained grid endpoint is
  -- charged to at most one excision or indentation component.
  let gridSeam : Bool → ℝ := fun b => if b then 1 else 0
  let allGridEndpoints (b : Bool) := retainedGridPieces.filter
    (fun e => pieceEndpoint b e.2.2 ≠ gridSeam b)
  let holeGridEndpoints (b : Bool) : Sum {v // v ∈ S} {v // v ∈ B} →
      Finset ((ℤ × ℤ) × Fin 4 × (ℝ × ℝ)) :=
    Sum.elim (fun v => excisionGridEndpoints v b) (fun v => indentationGridEndpoints v b)
  have hholeGridSubset (b : Bool) (v : Sum {v // v ∈ S} {v // v ∈ B}) :
      holeGridEndpoints b v ⊆ allGridEndpoints b := by
    intro e he
    have hmem : e ∈ retainedGridPieces ∧ pieceEndpoint b e.2.2 ∈ Set.Ioo (0 : ℝ) 1 := by
      cases v with
      | inl v => exact ⟨(Finset.mem_filter.mp he).1, (Finset.mem_filter.mp he).2.1⟩
      | inr v => exact ⟨(Finset.mem_filter.mp he).1, (Finset.mem_filter.mp he).2.1⟩
    refine Finset.mem_filter.mpr ⟨hmem.1, ?_⟩
    cases b
    · exact ne_of_gt hmem.2.1
    · exact ne_of_lt hmem.2.2
  have hexcisionGridPoint (b : Bool) (v : {v // v ∈ S})
      (e : (ℤ × ℤ) × Fin 4 × (ℝ × ℝ)) (he : e ∈ excisionGridEndpoints v b) :
      cellEdge e.1 e.2.1 (pieceEndpoint b e.2.2) ∈ Metric.closedBall v.1 r := by
    obtain ⟨_, _, s, _, heq⟩ := Finset.mem_filter.mp he
    rw [heq]
    exact Metric.sphere_subset_closedBall (circleMap_mem_sphere v.1 hr.le s)
  have hindentationGridPoint (b : Bool) (v : {v // v ∈ B})
      (e : (ℤ × ℤ) × Fin 4 × (ℝ × ℝ)) (he : e ∈ indentationGridEndpoints v b) :
      cellEdge e.1 e.2.1 (pieceEndpoint b e.2.2) ∈ D v.1 ε := by
    obtain ⟨_, _, s, _, heq⟩ := Finset.mem_filter.mp he
    rw [heq]
    exact (hgammaOnCut v.1 (hKH v.2.1.1) ε hε.1 hε.2 s).1
  have hholeGridUnique (b : Bool) (e : (ℤ × ℤ) × Fin 4 × (ℝ × ℝ))
      (u v : Sum {v // v ∈ S} {v // v ∈ B})
      (hu : e ∈ holeGridEndpoints b u) (hv : e ∈ holeGridEndpoints b v) : u = v := by
    cases u with
    | inl u =>
      have hzu := hexcisionGridPoint b u e hu
      cases v with
      | inl v =>
        have hzv := hexcisionGridPoint b v e hv
        have huv : u = v := by
          apply Subtype.ext
          by_contra hne
          exact Set.disjoint_left.mp (hexcisionDisjoint u.2 v.2 hne) hzu hzv
        exact congrArg Sum.inl huv
      | inr v =>
        have hzv := hindentationGridPoint b v e hv
        exact ((hexcisionInside u.1 u.2 hzu).2
          (Set.mem_iUnion₂.mpr ⟨v.1, v.2, hzv⟩)).elim
    | inr u =>
      have hzu := hindentationGridPoint b u e hu
      cases v with
      | inl v =>
        have hzv := hexcisionGridPoint b v e hv
        exact ((hexcisionInside v.1 v.2 hzv).2
          (Set.mem_iUnion₂.mpr ⟨u.1, u.2, hzu⟩)).elim
      | inr v =>
        have hzv := hindentationGridPoint b v e hv
        have huv : u = v := by
          apply Subtype.ext
          by_contra hne
          exact Set.disjoint_left.mp (hboundaryDisjoint u.2.1 v.2.1 hne) hzu hzv
        exact congrArg Sum.inr huv
  let outerGridEndpoints (b : Bool) := (allGridEndpoints b).filter
    (fun e => ∀ v : Sum {v // v ∈ S} {v // v ∈ B}, e ∉ holeGridEndpoints b v)
  have hgridEndpointPartition (b : Bool)
      (f : ((ℤ × ℤ) × Fin 4 × (ℝ × ℝ)) → ℂ) :
      (∑ e ∈ allGridEndpoints b, f e) =
        (∑ e ∈ outerGridEndpoints b, f e) +
          (∑ v : {v // v ∈ S}, ∑ e ∈ excisionGridEndpoints v b, f e) +
          ∑ v : {v // v ∈ B}, ∑ e ∈ indentationGridEndpoints v b, f e := by
    have hrow (e : (ℤ × ℤ) × Fin 4 × (ℝ × ℝ)) :
        f e = (if ∀ v, e ∉ holeGridEndpoints b v then f e else 0) +
          ∑ v : Sum {v // v ∈ S} {v // v ∈ B},
            if e ∈ holeGridEndpoints b v then f e else 0 := by
      by_cases he : ∃ v, e ∈ holeGridEndpoints b v
      · obtain ⟨v, hv⟩ := he
        rw [if_neg (fun h => h v hv), zero_add, Finset.sum_eq_single v, if_pos hv]
        · intro w _ hne
          exact if_neg (fun hw => hne (hholeGridUnique b e w v hw hv))
        · simp
      · have hn : ∀ v, e ∉ holeGridEndpoints b v := by simpa only [not_exists] using he
        simp only [if_pos hn, if_neg (hn _), Finset.sum_const_zero, add_zero]
    have hfilter (v : Sum {v // v ∈ S} {v // v ∈ B}) :
        (allGridEndpoints b).filter (fun e => e ∈ holeGridEndpoints b v) =
          holeGridEndpoints b v := by
      ext e
      exact ⟨fun h => (Finset.mem_filter.mp h).2,
        fun h => Finset.mem_filter.mpr ⟨hholeGridSubset b v h, h⟩⟩
    calc
      _ = (∑ e ∈ allGridEndpoints b,
            if ∀ v, e ∉ holeGridEndpoints b v then f e else 0) +
          ∑ e ∈ allGridEndpoints b, ∑ v : Sum {v // v ∈ S} {v // v ∈ B},
            if e ∈ holeGridEndpoints b v then f e else 0 := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun e _ => hrow e)
      _ = (∑ e ∈ outerGridEndpoints b, f e) +
          ∑ v : Sum {v // v ∈ S} {v // v ∈ B}, ∑ e ∈ holeGridEndpoints b v, f e := by
        rw [Finset.sum_comm]
        congr 1
        · exact (Finset.sum_filter _ _).symm
        · apply Finset.sum_congr rfl
          intro v _
          rw [← Finset.sum_filter, hfilter]
      _ = _ := by
        rw [Fintype.sum_sum_type]
        dsimp only [holeGridEndpoints, Sum.elim_inl, Sum.elim_inr]
        ring
  let outerGridContribution : ℂ :=
    (∑ e ∈ outerGridEndpoints true, cellPrimitive e.1 (cellEdge e.1 e.2.1 e.2.2.2)) -
      ∑ e ∈ outerGridEndpoints false, cellPrimitive e.1 (cellEdge e.1 e.2.1 e.2.2.1)
  have hgridBoundaryPartition :
      gridCrossingEndpoints =
        outerGridContribution + excisionGridContribution + indentationGridContribution := by
    have hsplit (b : Bool) :
        (∑ e ∈ retainedGridPieces,
          if pieceEndpoint b e.2.2 = gridSeam b then 0 else
            cellPrimitive e.1 (cellEdge e.1 e.2.1 (pieceEndpoint b e.2.2))) =
        ∑ e ∈ allGridEndpoints b,
          cellPrimitive e.1 (cellEdge e.1 e.2.1 (pieceEndpoint b e.2.2)) := by
      simp only [allGridEndpoints, Finset.sum_filter, ite_not]
    change (∑ i ∈ hgridFinite.toFinset, ∑ j : Fin 4, ∑ p ∈ retainedPieces i j, _) = _
    rw [← hdisjointGridSum hgridFinite.toFinset retainedPieces
      (fun e =>
        (if e.2.2.2 = 1 then 0 else cellPrimitive e.1 (cellEdge e.1 e.2.1 e.2.2.2)) -
          (if e.2.2.1 = 0 then 0 else cellPrimitive e.1 (cellEdge e.1 e.2.1 e.2.2.1)))]
    change (∑ e ∈ retainedGridPieces,
      ((if e.2.2.2 = 1 then 0 else cellPrimitive e.1 (cellEdge e.1 e.2.1 e.2.2.2)) -
        (if e.2.2.1 = 0 then 0 else cellPrimitive e.1 (cellEdge e.1 e.2.1 e.2.2.1)))) = _
    have htrue := hsplit true
    have hfalse := hsplit false
    simp only [pieceEndpoint, gridSeam, Bool.false_eq_true, ↓reduceIte] at htrue hfalse
    rw [Finset.sum_sub_distrib, htrue, hfalse,
      hgridEndpointPartition true, hgridEndpointPartition false]
    dsimp only [outerGridContribution, excisionGridContribution, indentationGridContribution]
    simp only [Finset.sum_sub_distrib]
    ring

  suffices hboundaryAssembly :
      intervalIntegral (retainedArc ε) (2 * Real.pi / 3) (Real.pi / 3)
          MeasureTheory.volume + verticalContribution ε + top Y +
        (∑ v ∈ hBfinite.toFinset, indent v (fun _ => cutStart v) (fun _ => cutEnd v) ε) +
        (∑ v ∈ hOzerosFinite.toFinset,
          intervalIntegral (fun t => L (circleMap v r t) * deriv (circleMap v r) t)
            (2 * Real.pi) 0 MeasureTheory.volume) =
        -(∑ e ∈ retainedGridPieces, retainedIntegral e) by
    rw [hboundaryAssembly, hretainedGridCancellation, neg_zero]
  have houterLocalSide (j : Fin 4) (s : ℝ)
      (hs : s ∈ Set.Ioo (outerLo j) (outerHi j)) (hm : outerPath j s ∉ removed ε) :
      ∀ᶠ w in nhds (outerPath j s), w ∈ V ↔ outerSide j w := by
    have hnot : outerPath j s ∉ Ω ε := fun h =>
      houterNotO j _ (houterPathMem j s ⟨hs.1.le, hs.2.le⟩).2 h.1
    filter_upwards [(houterWindowOpen j).mem_nhds (houterPathWindow j s hs),
      (hremovedClosed ε hε.1 hε.2).isOpen_compl.mem_nhds hm,
      hexcisionAway (outerPath j s) hnot] with w hw hn heq
    rw [heq]
    exact ⟨fun h => (houterWindowSide j w hw).mp h.1,
      fun h => ⟨(houterWindowSide j w hw).mpr h, hn⟩⟩
  have hcellVelocityCoordinates (i : ℤ × ℤ) (j : Fin 4) : cellVelocity i j =
      ![(d : ℂ), (d : ℂ) * Complex.I, -(d : ℂ), -(d : ℂ) * Complex.I] j := by
    fin_cases j <;> norm_num [cellVelocity, cellVertex, cellNext, Equiv.addRight,
      gridVertex, Fin.add_def] <;> ring
  have houterNormalNe (j : Fin 4) (s : ℝ) (i : ℤ × ℤ) (l : Fin 4) (t : ℝ)
      (heq : outerPath j s = cellEdge i l t) :
      outerNormal j (outerPath j s) (cellVelocity i l) ≠ 0 := by
    fin_cases j
    · change outerPath 0 s = cellEdge i l t at heq
      change (outerPath 0 s).re * (cellVelocity i l).re +
        (outerPath 0 s).im * (cellVelocity i l).im ≠ 0
      have hz : cellEdge i l t ∈ Metric.sphere 0 1 := by
        rw [← heq]
        change circleMap 0 1 s ∈ Metric.sphere 0 1
        exact circleMap_mem_sphere 0 (by norm_num) s
      rw [heq]
      simpa only [sub_zero] using
        hcellCircleNormalNe i l t (0, 1) (Or.inl (Or.inl rfl)) hz
    · change outerPath 1 s = cellEdge i l t at heq
      change -(cellVelocity i l).re ≠ 0
      have hre : (cellEdge i l t).re = 1 / 2 := by rw [← heq]; simp [outerPath]
      rw [(hcellEdgeCoordinates i l t).1] at hre
      rw [hcellVelocityCoordinates]
      fin_cases l
      · simpa using neg_ne_zero.mpr hd.ne'
      · exact False.elim (hgridVerticalRight (i.1 + 1)
          (by simpa [Int.cast_add] using hre))
      · simpa using hd.ne'
      · exact False.elim (hgridVerticalRight i.1 (by simpa using hre))
    · change outerPath 2 s = cellEdge i l t at heq
      change -(cellVelocity i l).im ≠ 0
      have him : (cellEdge i l t).im = Y := by rw [← heq]; simp [outerPath]
      rw [(hcellEdgeCoordinates i l t).2] at him
      rw [hcellVelocityCoordinates]
      fin_cases l
      · exact False.elim (hgridHorizontalTop i.2 (by simpa using him))
      · simpa using neg_ne_zero.mpr hd.ne'
      · exact False.elim (hgridHorizontalTop (i.2 + 1)
          (by simpa [Int.cast_add] using him))
      · simpa using hd.ne'
    · change outerPath 3 s = cellEdge i l t at heq
      change (cellVelocity i l).re ≠ 0
      have hre : (cellEdge i l t).re = -1 / 2 := by rw [← heq]; simp [outerPath]
      rw [(hcellEdgeCoordinates i l t).1] at hre
      rw [hcellVelocityCoordinates]
      fin_cases l
      · simpa using hd.ne'
      · exact False.elim (hgridVerticalLeft (i.1 + 1)
          (by simpa [Int.cast_add] using hre))
      · simpa using neg_ne_zero.mpr hd.ne'
      · exact False.elim (hgridVerticalLeft i.1 (by simpa using hre))
  have houterEdgeCrossing (j : Fin 4) (s : ℝ)
      (hs : s ∈ Set.Ioo (outerLo j) (outerHi j)) (hm : outerPath j s ∉ removed ε)
      (i : ℤ × ℤ) (l : Fin 4) (t : ℝ) (heq : outerPath j s = cellEdge i l t) :
      ∀ᶠ x in nhds t, cellEdge i l x ∈ V ↔
        0 < (x - t) * outerNormal j (outerPath j s) (cellVelocity i l) := by
    have hlocal := houterLocalSide j s hs hm
    rw [heq] at hlocal
    have hlinear (x : ℝ) : cellEdge i l x =
        cellEdge i l t + ((x - t : ℝ) : ℂ) * cellVelocity i l := by
      dsimp only [cellEdge, cellVelocity]
      push_cast
      ring
    fin_cases j
    · change outerPath 0 s = cellEdge i l t at heq
      change ∀ᶠ w in nhds (cellEdge i l t), w ∈ V ↔ outerSide 0 w at hlocal
      change ∀ᶠ x in nhds t, cellEdge i l x ∈ V ↔
        0 < (x - t) * outerNormal 0 (outerPath 0 s) (cellVelocity i l)
      have hz : cellEdge i l t ∈ Metric.sphere 0 1 := by
        rw [← heq]
        change circleMap 0 1 s ∈ Metric.sphere 0 1
        exact circleMap_mem_sphere 0 (by norm_num) s
      have hout : ∀ᶠ w in nhds (cellEdge i l t), w ∈ V ↔ (1 : ℝ) < ‖w - 0‖ := by
        simpa only [outerSide, Matrix.cons_val_zero, sub_zero] using hlocal
      have hcross := hcircleEdgeCrossing i l t (0, 1) (Or.inl (Or.inl rfl))
        (by norm_num) hz hout
      simpa only [outerNormal, Matrix.cons_val_zero, heq, sub_zero] using hcross
    · have hre : (cellEdge i l t).re = 1 / 2 := by rw [← heq]; simp [outerPath]
      filter_upwards [(hcellEdgeContinuous i l).continuousAt.eventually hlocal] with x hx
      rw [hx]
      change (cellEdge i l x).re < 1 / 2 ↔ 0 < (x - t) * -(cellVelocity i l).re
      rw [hlinear]
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero, hre]
      constructor <;> intro h <;> nlinarith only [h]
    · have him : (cellEdge i l t).im = Y := by rw [← heq]; simp [outerPath]
      filter_upwards [(hcellEdgeContinuous i l).continuousAt.eventually hlocal] with x hx
      rw [hx]
      change (cellEdge i l x).im < Y ↔ 0 < (x - t) * -(cellVelocity i l).im
      rw [hlinear]
      simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, add_zero, him]
      constructor <;> intro h <;> nlinarith only [h]
    · have hre : (cellEdge i l t).re = -1 / 2 := by rw [← heq]; simp [outerPath]
      filter_upwards [(hcellEdgeContinuous i l).continuousAt.eventually hlocal] with x hx
      rw [hx]
      change -1 / 2 < (cellEdge i l x).re ↔ 0 < (x - t) * (cellVelocity i l).re
      rw [hlinear]
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero, hre]
      constructor <;> intro h <;> nlinarith only [h]

  have houterCoarseBounds (j : Fin 4) (p : {p // p ∈ outerRetained j}) :
      outerLo j ≤ p.1.1 ∧ p.1.1 < p.1.2 ∧ p.1.2 ≤ outerHi j := by
    have hp := (congrArg (fun s : Finset (ℝ × ℝ) => p.1 ∈ s)
      (houterCertificate j).2.2.2.2.2.1).mp p.2
    exact (houterCertificate j).2.2.2.2.1 p.1 (Finset.mem_filter.mp hp).1
  have houterCoarseInterior (j : Fin 4) (p : {p // p ∈ outerRetained j}) (s : ℝ)
      (hs : s ∈ Set.Ioo p.1.1 p.1.2) :
      s ∈ Set.Ioo (outerLo j) (outerHi j) ∧ outerPath j s ∉ removed ε := by
    have hb := houterCoarseBounds j p
    exact ⟨⟨lt_of_le_of_lt hb.1 hs.1, lt_of_lt_of_le hs.2 hb.2.2⟩,
      (houterCertificate j).2.2.2.2.2.2.2.2.2 p.1 p.2 s hs⟩
  have hgridEdgeCrossing (i : ℤ × ℤ) (l : Fin 4) (t : ℝ)
      (hz : cellEdge i l t ∈ frontier V) : cellEdge i l t ∈ gridCrossings := by
    fin_cases l
    · exact hgridCrossingContains _ hz i.2
        (Or.inr (by simpa using (hcellEdgeCoordinates i 0 t).2))
    · exact hgridCrossingContains _ hz (i.1 + 1)
        (Or.inl (by simpa using (hcellEdgeCoordinates i 1 t).1))
    · exact hgridCrossingContains _ hz (i.2 + 1)
        (Or.inr (by simpa using (hcellEdgeCoordinates i 2 t).2))
    · exact hgridCrossingContains _ hz i.1
        (Or.inl (by simpa using (hcellEdgeCoordinates i 3 t).1))
  let outerPieceBool (j : Fin 4) (b : Bool) : Bool := if j = 1 then !b else b
  have houterArtificialIncidence (j : Fin 4) (p : {p // p ∈ outerRetained j})
      (q : ℝ × ℝ) (hq : q ∈ outerGridPieces j p) (l : Fin 4) (s t : ℝ)
      (ht : t ∈ Set.Ioo (0 : ℝ) 1) (hs : s ∈ Set.Ioo p.1.1 p.1.2)
      (heq : outerPath j s = cellEdge (outerGridCell j p q) l t) (b : Bool)
      (hqs : pieceEndpoint (outerPieceBool j b) q = s) :
      ∃! e : ℝ × ℝ, e ∈ retainedPieces (outerGridCell j p q) l ∧ pieceEndpoint b e = t := by
    let i := outerGridCell j p q
    have hglobal := houterCoarseInterior j p s hs
    have hfront : cellEdge i l t ∈ frontier V := by
      rw [← heq]
      exact (houterCertificate j).2.2.2.2.2.2.1 p.1 p.2 s ⟨hs.1.le, hs.2.le⟩
    have hcut : t ∈ edgeCuts i l :=
      (hedgeCutsMem i l t).mpr (Or.inr (Or.inr ⟨⟨ht.1.le, ht.2.le⟩, hfront⟩))
    let normal := outerNormal j (outerPath j s) (cellVelocity i l)
    have hnormal : normal ≠ 0 := houterNormalNe j s i l t heq
    have hdet : (deriv (outerPath j) s * star (cellVelocity i l)).im =
        if j = 1 then -normal else normal := houterDet j s (cellVelocity i l)
    have hpair := hq
    rw [(houterGridCertificate j p).2.2.2.1] at hpair
    have hlt := (Finset.mem_filter.mp hpair).2.1
    have hsign := hcellPathEndpointSigns (outerPath j) s _
      (((houterSmooth j).differentiable (by norm_num)) s).hasDerivAt i l t heq q.1 q.2 hlt
      (fun x hx => ((houterGridCertificate j p).2.2.2.2.1 q hq).2.1 x ⟨hx.1.le, hx.2.le⟩)
      (by rw [hdet]; split_ifs <;> simpa only [neg_ne_zero] using hnormal)
    rw [hdet] at hsign
    have hincidence := hfiniteRetainedEndpointIncidence
      (edgeCuts i l) (edgePieces i l) (retainedPieces i l) (hedgePieceMem i l)
      (fun _ he => (Finset.mem_filter.mp he).1) (cellEdge i l) V
      (hretainedPieceInterior i l)
      (fun e he hn x hx hz => hunretainedPieceExterior i l e he hn x hx (subset_closure hz))
      0 1 t normal ((hedgeCutsMem i l 0).mpr (Or.inl rfl))
      ((hedgeCutsMem i l 1).mpr (Or.inr (Or.inl rfl))) hcut ht.1 ht.2
      (houterEdgeCrossing j s hglobal.1 hglobal.2 i l t heq)
    cases b
    · apply hincidence.1.mpr
      by_cases hj : j = 1
      · have hqend : q.2 = s := by simpa [outerPieceBool, pieceEndpoint, hj] using hqs
        have hn := hsign.2 hqend
        rw [if_pos hj] at hn
        linarith only [hn]
      · have hqstart : q.1 = s := by simpa [outerPieceBool, pieceEndpoint, hj] using hqs
        simpa only [if_neg hj] using hsign.1 hqstart
    · apply hincidence.2.mpr
      by_cases hj : j = 1
      · have hqstart : q.1 = s := by simpa [outerPieceBool, pieceEndpoint, hj] using hqs
        have hn := hsign.1 hqstart
        rw [if_pos hj] at hn
        linarith only [hn]
      · have hqend : q.2 = s := by simpa [outerPieceBool, pieceEndpoint, hj] using hqs
        simpa only [if_neg hj] using hsign.2 hqend
  have houterGenuineIncidence (i : ℤ × ℤ) (l : Fin 4) (e : ℝ × ℝ)
      (he : e ∈ retainedPieces i l) (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1)
      (j : Fin 4) (p : {p // p ∈ outerRetained j}) (s : ℝ)
      (hs : s ∈ Set.Ioo p.1.1 p.1.2) (heq : cellEdge i l t = outerPath j s)
      (b : Bool) (het : pieceEndpoint b e = t) :
      ∃! q : ℝ × ℝ, q ∈ outerGridPieces j p ∧
        pieceEndpoint (outerPieceBool j b) q = s ∧ outerGridCell j p q = i := by
    have hglobal := houterCoarseInterior j p s hs
    have hfront : cellEdge i l t ∈ frontier V := by
      rw [heq]
      exact (houterCertificate j).2.2.2.2.2.2.1 p.1 p.2 s ⟨hs.1.le, hs.2.le⟩
    have hcross := hgridEdgeCrossing i l t hfront
    have hcut : s ∈ outerGridCuts j p :=
      ((houterGridCertificate j p).2.2.2.2.2.2 s).mpr
        (Or.inr (Or.inr ⟨hs, heq ▸ hcross⟩))
    have hpieces : ∀ q, q ∈ outerGridPieces j p ↔ q.1 ∈ outerGridCuts j p ∧
        q.2 ∈ outerGridCuts j p ∧ q.1 < q.2 ∧
          ∀ t ∈ outerGridCuts j p, t ≤ q.1 ∨ q.2 ≤ t := by
      intro q
      rw [(houterGridCertificate j p).2.2.2.1]
      simp only [Finset.mem_filter, Finset.mem_product, and_assoc]
    have hincidence := hfinitePieceIncidence (outerGridCuts j p) (outerGridPieces j p)
      hpieces s hcut
    have hlt := ((hedgePieceMem i l e).mp (Finset.mem_filter.mp he).1).2.2.1
    have hsign := hoccupiedEndpointSigns (cellEdge i l) V t _ e.1 e.2 hlt
      (hretainedPieceInterior i l e he)
      (houterEdgeCrossing j s hglobal.1 hglobal.2 i l t heq.symm)
    have hdet := houterDet j s (cellVelocity i l)
    have hchoose (c : Bool)
        (hsign : if c then (deriv (outerPath j) s * star (cellVelocity i l)).im < 0
          else 0 < (deriv (outerPath j) s * star (cellVelocity i l)).im) :
        ∃! q : ℝ × ℝ, q ∈ outerGridPieces j p ∧
          pieceEndpoint c q = s ∧ outerGridCell j p q = i := by
      cases c
      · obtain ⟨q, hq, hu⟩ := hincidence.1 ⟨p.1.2, (houterGridCertificate j p).2.1, hs.2⟩
        refine ⟨q, ⟨hq.1, hq.2, ?_⟩, fun w hw => hu w ⟨hw.1, hw.2.1⟩⟩
        exact hcellPathEndpointCell (outerPath j) s _
          (((houterSmooth j).differentiable (by norm_num)) s).hasDerivAt i l t ht heq.symm
          (outerGridCell j p q) q.1 q.2 ((hpieces q).mp hq.1).2.2.1
          ((houterGridCertificate j p).2.2.2.2.1 q hq.1).2.1 (Or.inl ⟨hq.2, hsign⟩)
      · obtain ⟨q, hq, hu⟩ := hincidence.2 ⟨p.1.1, (houterGridCertificate j p).1, hs.1⟩
        refine ⟨q, ⟨hq.1, hq.2, ?_⟩, fun w hw => hu w ⟨hw.1, hw.2.1⟩⟩
        exact hcellPathEndpointCell (outerPath j) s _
          (((houterSmooth j).differentiable (by norm_num)) s).hasDerivAt i l t ht heq.symm
          (outerGridCell j p q) q.1 q.2 ((hpieces q).mp hq.1).2.2.1
          ((houterGridCertificate j p).2.2.2.2.1 q hq.1).2.1 (Or.inr ⟨hq.2, hsign⟩)
    apply hchoose (outerPieceBool j b)
    cases b
    · have hn := hsign.1 het
      by_cases hj : j = 1
      · simp only [outerPieceBool, if_pos hj, Bool.not_false, ↓reduceIte]
        rw [hdet, if_pos hj]
        linarith only [hn]
      · simp only [outerPieceBool, if_neg hj, Bool.false_eq_true, ↓reduceIte]
        simpa only [hdet, if_neg hj] using hn
    · have hn := hsign.2 het
      by_cases hj : j = 1
      · simp only [outerPieceBool, if_pos hj, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        rw [hdet, if_pos hj]
        linarith only [hn]
      · simp only [outerPieceBool, if_neg hj, ↓reduceIte]
        simpa only [hdet, if_neg hj] using hn

  let outerEndpointPieces (u : Σ j : Fin 4, {p // p ∈ outerRetained j}) (b : Bool) :=
    (outerGridPieces u.1 u.2).filter (fun q =>
      pieceEndpoint (outerPieceBool u.1 b) q ≠ pieceEndpoint (outerPieceBool u.1 b) u.2.1)
  let outerFamily (u : Σ j : Fin 4, {p // p ∈ outerRetained j}) (b : Bool) :=
    retainedGridPieces.filter (fun e => pieceEndpoint b e.2.2 ∈ Set.Ioo (0 : ℝ) 1 ∧
      ∃ s ∈ Set.Ioo u.2.1.1 u.2.1.2,
        cellEdge e.1 e.2.1 (pieceEndpoint b e.2.2) = outerPath u.1 s)
  have houterEndpointInterior (u : Σ j : Fin 4, {p // p ∈ outerRetained j}) (b : Bool)
      (q : ℝ × ℝ) (hq : q ∈ outerEndpointPieces u b) :
      pieceEndpoint (outerPieceBool u.1 b) q ∈ Set.Ioo u.2.1.1 u.2.1.2 ∧
        outerPath u.1 (pieceEndpoint (outerPieceBool u.1 b) q) ∈ gridCrossings := by
    obtain ⟨hqq, hne⟩ := Finset.mem_filter.mp hq
    have hpairs := hqq
    rw [(houterGridCertificate u.1 u.2).2.2.2.1] at hpairs
    obtain ⟨h₁, h₂⟩ := Finset.mem_product.mp (Finset.mem_filter.mp hpairs).1
    have hlt := (Finset.mem_filter.mp hpairs).2.1
    have hb₁ := (houterGridCertificate u.1 u.2).2.2.1 q.1 h₁
    have hb₂ := (houterGridCertificate u.1 u.2).2.2.1 q.2 h₂
    have hmem : pieceEndpoint (outerPieceBool u.1 b) q ∈ outerGridCuts u.1 u.2 := by
      cases h : outerPieceBool u.1 b <;> simp only [pieceEndpoint, Bool.false_eq_true,
        ↓reduceIte] <;> assumption
    have hstrict : pieceEndpoint (outerPieceBool u.1 b) q ∈ Set.Ioo u.2.1.1 u.2.1.2 := by
      cases h : outerPieceBool u.1 b
      · simp only [h, pieceEndpoint, Bool.false_eq_true, ↓reduceIte] at hne ⊢
        exact ⟨lt_of_le_of_ne hb₁.1 hne.symm, lt_of_lt_of_le hlt hb₂.2⟩
      · simp only [h, pieceEndpoint, ↓reduceIte] at hne ⊢
        exact ⟨lt_of_le_of_lt hb₁.1 hlt, lt_of_le_of_ne hb₂.2 hne⟩
    refine ⟨hstrict, ?_⟩
    rcases ((houterGridCertificate u.1 u.2).2.2.2.2.2.2 _).mp hmem with h | h | h
    · exact (ne_of_gt hstrict.1 h).elim
    · exact (ne_of_lt hstrict.2 h).elim
    · exact h.2
  let outerEndpointMatch (u : Σ j : Fin 4, {p // p ∈ outerRetained j}) (b : Bool)
      (q : ℝ × ℝ) (e : (ℤ × ℤ) × Fin 4 × (ℝ × ℝ)) : Prop :=
    outerGridCell u.1 u.2 q = e.1 ∧
      outerPath u.1 (pieceEndpoint (outerPieceBool u.1 b) q) =
        cellEdge e.1 e.2.1 (pieceEndpoint b e.2.2)
  have houterEndpointRow (u : Σ j : Fin 4, {p // p ∈ outerRetained j}) (b : Bool)
      (q : ℝ × ℝ) (hq : q ∈ outerEndpointPieces u b) :
      ∃! e, e ∈ outerFamily u b ∧ outerEndpointMatch u b q e := by
    have hqq := (Finset.mem_filter.mp hq).1
    obtain ⟨hs, hcross⟩ := houterEndpointInterior u b q hq
    have hpairs := hqq
    rw [(houterGridCertificate u.1 u.2).2.2.2.1] at hpairs
    have hlt := (Finset.mem_filter.mp hpairs).2.1
    have hbound : pieceEndpoint (outerPieceBool u.1 b) q ∈ Set.Icc q.1 q.2 := by
      cases h : outerPieceBool u.1 b
      · exact ⟨le_rfl, hlt.le⟩
      · exact ⟨hlt.le, le_rfl⟩
    have hcell := ((houterGridCertificate u.1 u.2).2.2.2.2.1 q hqq).2.1 _ hbound
    obtain ⟨l, t, ht, hpoint⟩ := hcrossingCellEdge _ hcross (outerGridCell u.1 u.2 q) hcell
    obtain ⟨p, ⟨hp, hpt⟩, hpunique⟩ := houterArtificialIncidence u.1 u.2 q hqq l
      (pieceEndpoint (outerPieceBool u.1 b) q) t ht hs hpoint.symm b rfl
    let e : (ℤ × ℤ) × Fin 4 × (ℝ × ℝ) := (outerGridCell u.1 u.2 q, l, p)
    have he : e ∈ outerFamily u b := by
      refine Finset.mem_filter.mpr ⟨(hretainedGridMem e).mpr
        ⟨((houterGridCertificate u.1 u.2).2.2.2.2.1 q hqq).1, hp⟩, ?_⟩
      exact ⟨hpt.symm ▸ ht, pieceEndpoint (outerPieceBool u.1 b) q, hs,
        by simpa only [e, hpt] using hpoint⟩
    refine ⟨e, ⟨he, rfl, by simpa only [e, hpt] using hpoint.symm⟩, ?_⟩
    intro e' he'
    obtain ⟨he'mem, he'cell, he'point⟩ := he'
    have ht' := (Finset.mem_filter.mp he'mem).2.1
    have hp' := ((hretainedGridMem e').mp (Finset.mem_filter.mp he'mem).1).2
    have hpath : cellEdge (outerGridCell u.1 u.2 q) l t =
        cellEdge (outerGridCell u.1 u.2 q) e'.2.1 (pieceEndpoint b e'.2.2) := by
      simpa only [he'cell] using hpoint.trans he'point
    obtain ⟨hl, hparam⟩ := hcellEdgeInteriorUnique _ _ _ _ _ ht ht' hpath
    have hpq : e'.2.2 = p := hpunique e'.2.2
      ⟨by simpa only [he'cell, hl] using hp', hparam.symm⟩
    exact Prod.ext he'cell.symm (Prod.ext hl.symm hpq)
  have houterEndpointColumn (u : Σ j : Fin 4, {p // p ∈ outerRetained j}) (b : Bool)
      (e : (ℤ × ℤ) × Fin 4 × (ℝ × ℝ)) (he : e ∈ outerFamily u b) :
      ∃! q, q ∈ outerEndpointPieces u b ∧ outerEndpointMatch u b q e := by
    obtain ⟨hemem, ht, s, hs, heq⟩ := Finset.mem_filter.mp he
    have hp := ((hretainedGridMem e).mp hemem).2
    obtain ⟨q, ⟨hqq, hqs, hcell⟩, hqunique⟩ := houterGenuineIncidence e.1 e.2.1 e.2.2 hp
      (pieceEndpoint b e.2.2) ht u.1 u.2 s hs heq b rfl
    have hq : q ∈ outerEndpointPieces u b := by
      refine Finset.mem_filter.mpr ⟨hqq, ?_⟩
      rw [hqs]
      cases h : outerPieceBool u.1 b
      · exact ne_of_gt hs.1
      · exact ne_of_lt hs.2
    refine ⟨q, ⟨hq, hcell, by rw [hqs]; exact heq.symm⟩, ?_⟩
    intro w hw
    obtain ⟨hwmem, hwcell, hwpoint⟩ := hw
    have hsw := (houterEndpointInterior u b w hwmem).1
    have hparam : pieceEndpoint (outerPieceBool u.1 b) w = s :=
      houterInjective u.1 (houterCoarseInterior u.1 u.2 _ hsw).1
        (houterCoarseInterior u.1 u.2 s hs).1 (hwpoint.trans heq)
    exact hqunique w ⟨(Finset.mem_filter.mp hwmem).1, hparam, hwcell⟩
  have houterEndpointSumReindex (u : Σ j : Fin 4, {p // p ∈ outerRetained j}) (b : Bool) :
      (∑ q ∈ outerEndpointPieces u b,
        cellPrimitive (outerGridCell u.1 u.2 q)
          (outerPath u.1 (pieceEndpoint (outerPieceBool u.1 b) q))) =
      ∑ e ∈ outerFamily u b,
        cellPrimitive e.1 (cellEdge e.1 e.2.1 (pieceEndpoint b e.2.2)) := by
    let f := fun q => cellPrimitive (outerGridCell u.1 u.2 q)
      (outerPath u.1 (pieceEndpoint (outerPieceBool u.1 b) q))
    let g := fun e : (ℤ × ℤ) × Fin 4 × (ℝ × ℝ) =>
      cellPrimitive e.1 (cellEdge e.1 e.2.1 (pieceEndpoint b e.2.2))
    have hrow (q : ℝ × ℝ) (hq : q ∈ outerEndpointPieces u b) :
        f q = ∑ e ∈ outerFamily u b, if outerEndpointMatch u b q e then f q else 0 := by
      obtain ⟨e, ⟨he, hrel⟩, hu⟩ := houterEndpointRow u b q hq
      rw [Finset.sum_eq_single e, if_pos hrel]
      · intro e' he' hne
        exact if_neg (fun h => hne (hu e' ⟨he', h⟩))
      · exact fun h => (h he).elim
    have hcolumn (e : (ℤ × ℤ) × Fin 4 × (ℝ × ℝ)) (he : e ∈ outerFamily u b) :
        (∑ q ∈ outerEndpointPieces u b, if outerEndpointMatch u b q e then f q else 0) = g e := by
      obtain ⟨q, ⟨hq, hrel⟩, hu⟩ := houterEndpointColumn u b e he
      rw [Finset.sum_eq_single q, if_pos hrel]
      · exact congrArg₂ cellPrimitive hrel.1 hrel.2
      · intro q' hq' hne
        exact if_neg (fun h => hne (hu q' ⟨hq', h⟩))
      · exact fun h => (h hq).elim
    calc
      _ = ∑ q ∈ outerEndpointPieces u b, ∑ e ∈ outerFamily u b,
          if outerEndpointMatch u b q e then f q else 0 := Finset.sum_congr rfl hrow
      _ = ∑ e ∈ outerFamily u b, ∑ q ∈ outerEndpointPieces u b,
          if outerEndpointMatch u b q e then f q else 0 := Finset.sum_comm
      _ = _ := Finset.sum_congr rfl hcolumn

  have houterCoarseMem (j : Fin 4) (p : {p // p ∈ outerRetained j}) :
      p.1.1 ∈ outerCuts j ∧ p.1.2 ∈ outerCuts j ∧ p.1.1 < p.1.2 ∧
        ∀ t ∈ outerCuts j, t ≤ p.1.1 ∨ p.1.2 ≤ t := by
    have hp := (congrArg (fun s : Finset (ℝ × ℝ) => p.1 ∈ s)
      (houterCertificate j).2.2.2.2.2.1).mp p.2
    have hpiece := (Finset.mem_filter.mp hp).1
    rw [(houterCertificate j).2.2.2.1] at hpiece
    simpa only [Finset.mem_filter, Finset.mem_product, and_assoc] using hpiece
  have houterCoarseUnique (j : Fin 4) (p q : {p // p ∈ outerRetained j}) (s : ℝ)
      (hp : s ∈ Set.Ioo p.1.1 p.1.2) (hq : s ∈ Set.Ioo q.1.1 q.1.2) : p = q := by
    have hpc := houterCoarseMem j p
    have hqc := houterCoarseMem j q
    apply Subtype.ext
    apply Prod.ext
    · apply le_antisymm
      · rcases hqc.2.2.2 p.1.1 hpc.1 with h | h
        · exact h
        · linarith only [h, hp.1, hq.2]
      · rcases hpc.2.2.2 q.1.1 hqc.1 with h | h
        · exact h
        · linarith only [h, hq.1, hp.2]
    · apply le_antisymm
      · rcases hpc.2.2.2 q.1.2 hqc.2.1 with h | h
        · linarith only [h, hp.1, hq.2]
        · exact h
      · rcases hqc.2.2.2 p.1.2 hpc.2.1 with h | h
        · linarith only [h, hq.1, hp.2]
        · exact h
  have houterRetainedAt (j : Fin 4) (p : ℝ × ℝ) (hp : p ∈ outerPieces j)
      (s : ℝ) (hs : s ∈ Set.Ioo p.1 p.2) (hsout : outerPath j s ∉ removed ε) :
      p ∈ outerRetained j := by
    have hb := (houterCertificate j).2.2.2.2.1 p hp
    have hpair := hp
    rw [(houterCertificate j).2.2.2.1] at hpair
    have hgap := (Finset.mem_filter.mp hpair).2.2
    have havoid : ∀ t ∈ Set.Ioo p.1 p.2, outerPath j t ∉ frontier (removed ε) := by
      intro t ht hf
      have hcut := ((houterCertificate j).2.2.2.2.2.2.2.2.1 t).mpr
        (Or.inr (Or.inr ⟨⟨lt_of_le_of_lt hb.1 ht.1, lt_of_lt_of_le ht.2 hb.2.2⟩, hf⟩))
      rcases hgap t hcut with h | h <;> linarith only [h, ht.1, ht.2]
    have hcover : outerPath j '' Set.Ioo p.1 p.2 ⊆
        (removed ε)ᶜ ∪ interior (removed ε) := by
      rintro _ ⟨t, ht, rfl⟩
      by_cases hm : outerPath j t ∈ removed ε
      · exact Or.inr (by_contra (fun hn => havoid t ht ⟨subset_closure hm, hn⟩))
      · exact Or.inl hm
    have hdisjoint : Disjoint (removed ε)ᶜ (interior (removed ε)) :=
      Set.disjoint_left.mpr (fun _ hc hi => hc (interior_subset hi))
    have hout : ∀ t ∈ Set.Ioo p.1 p.2, outerPath j t ∉ removed ε := by
      rcases (isPreconnected_Ioo.image _ (houterSmooth j).continuous.continuousOn).subset_or_subset
        (hremovedClosed ε hε.1 hε.2).isOpen_compl isOpen_interior hdisjoint hcover with h | h
      · exact fun t ht => h ⟨t, ht, rfl⟩
      · exact False.elim (hsout (interior_subset (h ⟨s, hs, rfl⟩)))
    rw [(houterCertificate j).2.2.2.2.2.1]
    exact Finset.mem_filter.mpr ⟨hp, hout ((p.1 + p.2) / 2)
      ⟨by linarith only [hb.2.1], by linarith only [hb.2.1]⟩⟩
  have houterCoarseCover (j : Fin 4) (s : ℝ)
      (hs : s ∈ Set.Ioo (outerLo j) (outerHi j))
      (hsout : outerPath j s ∉ removed ε) :
      ∃ p : {p // p ∈ outerRetained j}, s ∈ Set.Ioo p.1.1 p.1.2 := by
    have hsnot : s ∉ outerCuts j := by
      intro hsCut
      rcases ((houterCertificate j).2.2.2.2.2.2.2.2.1 s).mp hsCut with h | h | h
      · exact (ne_of_gt hs.1) h
      · exact (ne_of_lt hs.2) h
      · exact hsout ((hremovedClosed ε hε.1 hε.2).closure_subset h.2.1)
    let below := (outerCuts j).filter (fun t => t < s)
    let above := (outerCuts j).filter (fun t => s < t)
    have hl : below.Nonempty := ⟨outerLo j, Finset.mem_filter.mpr ⟨(houterCertificate j).1, hs.1⟩⟩
    have hu : above.Nonempty := ⟨outerHi j, Finset.mem_filter.mpr ⟨(houterCertificate j).2.1, hs.2⟩⟩
    let x := below.max' hl
    let y := above.min' hu
    have hx := Finset.mem_filter.mp (below.max'_mem hl)
    have hy := Finset.mem_filter.mp (above.min'_mem hu)
    have hp : (x, y) ∈ outerPieces j := by
      rw [(houterCertificate j).2.2.2.1]
      refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx.1, hy.1⟩,
        lt_trans hx.2 hy.2, ?_⟩
      intro t ht
      have hts : t ≠ s := fun heq => hsnot (heq ▸ ht)
      rcases lt_or_gt_of_ne hts with h | h
      · exact Or.inl (below.le_max' t (Finset.mem_filter.mpr ⟨ht, h⟩))
      · exact Or.inr (above.min'_le t (Finset.mem_filter.mpr ⟨ht, h⟩))
    exact ⟨⟨(x, y), houterRetainedAt j (x, y) hp s ⟨hx.2, hy.2⟩ hsout⟩, hx.2, hy.2⟩
  have hgridEdgeLine (i : ℤ × ℤ) (l : Fin 4) (t : ℝ) :
      ∃ n : ℤ, (cellEdge i l t).re = a.re + n * d ∨
        (cellEdge i l t).im = a.im + n * d := by
    fin_cases l
    · exact ⟨i.2, Or.inr (by simpa using (hcellEdgeCoordinates i 0 t).2)⟩
    · exact ⟨i.1 + 1, Or.inl (by simpa using (hcellEdgeCoordinates i 1 t).1)⟩
    · exact ⟨i.2 + 1, Or.inr (by simpa using (hcellEdgeCoordinates i 2 t).2)⟩
    · exact ⟨i.1, Or.inl (by simpa using (hcellEdgeCoordinates i 3 t).1)⟩
  have hallGridEndpointFacts (b : Bool) (e : (ℤ × ℤ) × Fin 4 × (ℝ × ℝ))
      (he : e ∈ allGridEndpoints b) :
      pieceEndpoint b e.2.2 ∈ Set.Ioo (0 : ℝ) 1 ∧
        cellEdge e.1 e.2.1 (pieceEndpoint b e.2.2) ∈ frontier V := by
    obtain ⟨hemem, hne⟩ := Finset.mem_filter.mp he
    have hp := ((hretainedGridMem e).mp hemem).2
    obtain ⟨h₁, h₂, hlt, _⟩ := (hedgePieceMem e.1 e.2.1 e.2.2).mp (Finset.mem_filter.mp hp).1
    have hb₁ := hedgeCutsBounds e.1 e.2.1 h₁
    have hb₂ := hedgeCutsBounds e.1 e.2.1 h₂
    have hf := hretainedPieceEndpoints e.1 e.2.1 e.2.2 hp
    cases b
    · change e.2.2.1 ≠ 0 at hne
      exact ⟨⟨lt_of_le_of_ne hb₁.1 hne.symm, lt_of_lt_of_le hlt hb₂.2⟩,
        hf.1.resolve_left (fun h => hne h.1)⟩
    · change e.2.2.2 ≠ 1 at hne
      exact ⟨⟨lt_of_le_of_lt hb₁.1 hlt, lt_of_le_of_ne hb₂.2 hne⟩,
        hf.2.resolve_left (fun h => hne h.1)⟩
  have houterFamilySubset (u : Σ j : Fin 4, {p // p ∈ outerRetained j}) (b : Bool) :
      outerFamily u b ⊆ outerGridEndpoints b := by
    intro e he
    obtain ⟨hemem, ht, s, hs, heq⟩ := Finset.mem_filter.mp he
    have hglobal := houterCoarseInterior u.1 u.2 s hs
    have hnO : cellEdge e.1 e.2.1 (pieceEndpoint b e.2.2) ∉ O := by
      rw [heq]
      exact houterNotO u.1 _ (houterPathMem u.1 s ⟨hglobal.1.1.le, hglobal.1.2.le⟩).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hemem, ?_⟩, ?_⟩
    · cases b
      · exact ne_of_gt ht.1
      · exact ne_of_lt ht.2
    · intro v hv
      cases v with
      | inl v => exact hnO (hexcisionInside v.1 v.2 (hexcisionGridPoint b v e hv)).1
      | inr v =>
        apply hglobal.2
        rw [← heq]
        exact Set.mem_iUnion₂.mpr ⟨v.1, v.2, hindentationGridPoint b v e hv⟩
  have houterFamilyUnique (b : Bool) (e : (ℤ × ℤ) × Fin 4 × (ℝ × ℝ))
      (u v : Σ j : Fin 4, {p // p ∈ outerRetained j})
      (hu : e ∈ outerFamily u b) (hv : e ∈ outerFamily v b) : u = v := by
    rcases u with ⟨j, p⟩
    rcases v with ⟨k, q⟩
    obtain ⟨_, _, s, hs, heq⟩ := Finset.mem_filter.mp hu
    obtain ⟨_, _, t, ht, heq'⟩ := Finset.mem_filter.mp hv
    have hglobal := houterCoarseInterior j p s hs
    have hglobal' := houterCoarseInterior k q t ht
    have hpoint : outerPath j s = outerPath k t := heq.symm.trans heq'
    have hkj : k = j := houterWindowUnique j (outerPath j s) (houterPathWindow j s hglobal.1) k
      (by rw [hpoint]; exact (houterPathMem k t ⟨hglobal'.1.1.le, hglobal'.1.2.le⟩).2)
    subst k
    have hst : s = t := houterInjective j hglobal.1 hglobal'.1 hpoint
    subst t
    have hpq : p = q := houterCoarseUnique j p q s hs ht
    subst q
    rfl

  have houterFamilyCover (b : Bool) (e : (ℤ × ℤ) × Fin 4 × (ℝ × ℝ))
      (he : e ∈ outerGridEndpoints b) :
      ∃ u : Σ j : Fin 4, {p // p ∈ outerRetained j}, e ∈ outerFamily u b := by
    obtain ⟨hall, hholes⟩ := Finset.mem_filter.mp he
    have hemem := (Finset.mem_filter.mp hall).1
    obtain ⟨ht, hfront⟩ := hallGridEndpointFacts b e hall
    let z := cellEdge e.1 e.2.1 (pieceEndpoint b e.2.2)
    have hline := hgridEdgeLine e.1 e.2.1 (pieceEndpoint b e.2.2)
    have hncorner : z ∉ gridCorners := hgridPointNotCorner z hline
    have houter : ∃ j : Fin 4, z ∈ closure (Ω ε) ∧ z ∈ outerSupport j := by
      have hclassified := hfront
      rw [hfullVFrontier] at hclassified
      rcases hclassified with (hout | hind) | hexc
      · exact Set.mem_iUnion.mp hout
      · obtain ⟨v, hv, s, hs, heq⟩ := Set.mem_iUnion₂.mp hind
        change γ v ε s = z at heq
        have hlo : s ≠ cutEnd v := by
          intro h
          apply hncorner
          rw [← heq, h]
          exact Or.inr ⟨v, hv, rfl⟩
        have hhi : s ≠ cutStart v := by
          intro h
          apply hncorner
          rw [← heq, h]
          exact Or.inl (Or.inr ⟨v, hv, rfl⟩)
        have hs' : s ∈ Set.Ioo (cutEnd v) (cutStart v) :=
          ⟨lt_of_le_of_ne hs.1 hlo.symm, lt_of_le_of_ne hs.2 hhi⟩
        exact False.elim (hholes (Sum.inr ⟨v, hv⟩)
          (Finset.mem_filter.mpr ⟨hemem, ht, s, hs', heq.symm⟩))
      · obtain ⟨v, hv, hzv⟩ := Set.mem_iUnion₂.mp hexc
        have hnseam : z ≠ circleMap v r 0 := by
          intro h
          obtain ⟨n, hn | hn⟩ := hline
          · exact (hgridCircleSeams v hv n).1 (by simpa only [← h] using hn.symm)
          · exact (hgridCircleSeams v hv n).2 (by simpa only [← h] using hn.symm)
        have hparam : z ∈ circleMap v r '' Set.Ioc 0 (2 * Real.pi) := by
          rw [image_circleMap_Ioc, abs_of_pos hr]
          exact hzv
        obtain ⟨s, hs, heq⟩ := hparam
        have hsne : s ≠ 2 * Real.pi := by
          intro h
          apply hnseam
          rw [← heq, h]
          simpa only [zero_add] using periodic_circleMap v r 0
        exact False.elim (hholes (Sum.inl ⟨v, hv⟩)
          (Finset.mem_filter.mpr ⟨hemem, ht, s,
            ⟨hs.1, lt_of_le_of_ne hs.2 hsne⟩, heq.symm⟩))
    obtain ⟨j, hzcl, hzj⟩ := houter
    have hnremoved : z ∉ removed ε :=
      fun hm => hncorner (houterRemovedCorner j z hfront hzj hm)
    obtain ⟨s, hs, heq⟩ := houterRepresentation j z (hcutClosureK ε hzcl) hzj
    have hlo : s ≠ outerLo j := by
      intro h
      apply hncorner
      rw [← heq, h]
      exact (houterEndCorners j).1
    have hhi : s ≠ outerHi j := by
      intro h
      apply hncorner
      rw [← heq, h]
      exact (houterEndCorners j).2
    have hs' : s ∈ Set.Ioo (outerLo j) (outerHi j) :=
      ⟨lt_of_le_of_ne hs.1 hlo.symm, lt_of_le_of_ne hs.2 hhi⟩
    obtain ⟨p, hp⟩ := houterCoarseCover j s hs' (heq.symm ▸ hnremoved)
    exact ⟨⟨j, p⟩, Finset.mem_filter.mpr ⟨hemem, ht, s, hp, heq.symm⟩⟩
  have houterFamilySum (b : Bool) (f : ((ℤ × ℤ) × Fin 4 × (ℝ × ℝ)) → ℂ) :
      (∑ e ∈ outerGridEndpoints b, f e) =
        ∑ u : Σ j : Fin 4, {p // p ∈ outerRetained j}, ∑ e ∈ outerFamily u b, f e := by
    have hrow (e : (ℤ × ℤ) × Fin 4 × (ℝ × ℝ)) (he : e ∈ outerGridEndpoints b) :
        f e = ∑ u : Σ j : Fin 4, {p // p ∈ outerRetained j},
          if e ∈ outerFamily u b then f e else 0 := by
      obtain ⟨u, hu⟩ := houterFamilyCover b e he
      rw [Finset.sum_eq_single u, if_pos hu]
      · intro v _ hne
        exact if_neg (fun hv => hne (houterFamilyUnique b e v u hv hu))
      · exact fun h => (h (Finset.mem_univ u)).elim
    calc
      _ = ∑ e ∈ outerGridEndpoints b, ∑ u : Σ j : Fin 4, {p // p ∈ outerRetained j},
          if e ∈ outerFamily u b then f e else 0 := Finset.sum_congr rfl hrow
      _ = ∑ u : Σ j : Fin 4, {p // p ∈ outerRetained j}, ∑ e ∈ outerGridEndpoints b,
          if e ∈ outerFamily u b then f e else 0 := Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro u _
        rw [← Finset.sum_filter]
        congr 1
        ext e
        simp only [Finset.mem_filter]
        exact ⟨fun h => h.2, fun h => ⟨houterFamilySubset u b h, h⟩⟩

  have hindentationJoinZero : indentationJoinEndpoints = 0 := by
    change -(∑ v : {v // v ∈ B}, ∑ p ∈ indentationPieces v, _) = 0
    rw [neg_eq_zero]
    apply Finset.sum_eq_zero
    intro v _
    apply Finset.sum_eq_zero
    intro p hp
    have hpair := hp
    rw [(hindentationCertificate v).2.2.2.1] at hpair
    have hlt := (Finset.mem_filter.mp hpair).2.1
    have hpath := ((hindentationCertificate v).2.2.2.2.1 p hp).2.1
    have hstart : p.1 = cutEnd v.1 →
        cellPrimitive (indentationCell v p) (γ v.1 ε p.1) = 0 := by
      intro heq
      apply hcellPrimitiveJoin
      · rw [heq]
        exact Or.inr ⟨v.1, v.2, rfl⟩
      · exact hpath p.1 ⟨le_rfl, hlt.le⟩
    have hend : p.2 = cutStart v.1 →
        cellPrimitive (indentationCell v p) (γ v.1 ε p.2) = 0 := by
      intro heq
      apply hcellPrimitiveJoin
      · rw [heq]
        exact Or.inl (Or.inr ⟨v.1, v.2, rfl⟩)
      · exact hpath p.2 ⟨hlt.le, le_rfl⟩
    split_ifs with h₂ h₁ h₁
    · rw [hend h₂, hstart h₁, sub_self]
    · rw [hend h₂, sub_self]
    · rw [hstart h₁, sub_self]
    · exact sub_self 0
  let outerCrossingEndpoints : ℂ := ∑ j : Fin 4, outerSign j *
    ∑ p : {p // p ∈ outerRetained j}, ∑ q ∈ outerGridPieces j p,
      ((if q.2 = p.1.2 then 0 else cellPrimitive (outerGridCell j p q) (outerPath j q.2)) -
        (if q.1 = p.1.1 then 0 else cellPrimitive (outerGridCell j p q) (outerPath j q.1)))
  have houterEndpointReduction : outerEndpoints = outerCrossingEndpoints := by
    apply Finset.sum_congr rfl
    intro j _
    apply congrArg (outerSign j * ·)
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro q hq
    have hpair := hq
    rw [(houterGridCertificate j p).2.2.2.1] at hpair
    have hlt := (Finset.mem_filter.mp hpair).2.1
    have hpath := ((houterGridCertificate j p).2.2.2.2.1 q hq).2.1
    have hstart : q.1 = p.1.1 →
        cellPrimitive (outerGridCell j p q) (outerPath j q.1) = 0 := by
      intro heq
      exact hcellPrimitiveJoin _ _ (houterCoarseEndpointCorner j p q.1 (Or.inl heq))
        (hpath q.1 ⟨le_rfl, hlt.le⟩)
    have hend : q.2 = p.1.2 →
        cellPrimitive (outerGridCell j p q) (outerPath j q.2) = 0 := by
      intro heq
      exact hcellPrimitiveJoin _ _ (houterCoarseEndpointCorner j p q.2 (Or.inr heq))
        (hpath q.2 ⟨hlt.le, le_rfl⟩)
    split_ifs with h₂ h₁ h₁
    · rw [hend h₂, hstart h₁]
    · rw [hend h₂]
    · rw [hstart h₁]
    · rfl

  have houterGridCancellation : outerCrossingEndpoints = -outerGridContribution := by
    have hsplit (u : Σ j : Fin 4, {p // p ∈ outerRetained j}) (b : Bool) :
        (∑ q ∈ outerGridPieces u.1 u.2,
          if pieceEndpoint (outerPieceBool u.1 b) q = pieceEndpoint (outerPieceBool u.1 b) u.2.1
          then 0 else cellPrimitive (outerGridCell u.1 u.2 q)
            (outerPath u.1 (pieceEndpoint (outerPieceBool u.1 b) q))) =
        ∑ e ∈ outerFamily u b,
          cellPrimitive e.1 (cellEdge e.1 e.2.1 (pieceEndpoint b e.2.2)) := by
      rw [← houterEndpointSumReindex u b]
      simp only [outerEndpointPieces, Finset.sum_filter, ite_not]
    have hsign (j : Fin 4) : outerSign j = if j = 1 then 1 else -1 := by
      fin_cases j <;> norm_num [outerSign]
    dsimp only [outerCrossingEndpoints, outerGridContribution]
    rw [houterFamilySum true, houterFamilySum false, ← Finset.sum_sub_distrib,
      Fintype.sum_sigma, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro p _
    rw [Finset.sum_sub_distrib]
    have h₀ := hsplit ⟨j, p⟩ false
    have h₁ := hsplit ⟨j, p⟩ true
    by_cases hj : j = 1
    · simp only [outerPieceBool, if_pos hj, Bool.not_false, Bool.not_true,
        pieceEndpoint, Bool.false_eq_true, ↓reduceIte] at h₀ h₁
      rw [hsign j, if_pos hj, h₀, h₁]
      ring
    · simp only [outerPieceBool, if_neg hj, pieceEndpoint, Bool.false_eq_true, ↓reduceIte] at h₀ h₁
      rw [hsign j, if_neg hj, h₁, h₀]
      ring

  rw [houterEndpointSum, hindentationEndpointSum, hexcisionEndpointSum, hgridEndpointSum,
    hgridEndpointReduction, hexcisionEndpointReduction, hexcisionGridCancellation,
    hindentationEndpointReduction, hindentationGridCancellation, hgridBoundaryPartition,
    hindentationJoinZero, houterEndpointReduction, houterGridCancellation]
  ring

end Submission
