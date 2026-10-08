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
