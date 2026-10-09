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
      exact_mod_cast h
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
          _ = _ := congrArg₂ (fun a b : ℕ => a * b)
            (Submission.p10_17ae7b7d_to_prime_power_count p (N.factorization p)
              hPrime hExponent) (ih hsN)
  change count N = ModularCurve.cuspCount N
  rw [Submission.p10_17ae7b7d_to_cusp_count_factorization N]
  calc
    count N = count (N.primeFactors.prod (fun p => p ^ N.factorization p)) :=
      congrArg count (Nat.prod_primeFactors_pow_factorization (NeZero.ne N))
    _ = _ := hProduct N.primeFactors (Finset.Subset.refl _)
