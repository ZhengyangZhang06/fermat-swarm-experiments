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
