/-
Copyright 2026 Anthropic, PBC. Licensed under Apache-2.0; see LICENSE.
Source: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_CuspForm_span_heckeTLin_eigen_eq_top.lean
Modified: replaced the proof with sorry and removed P2M proof imports.
Requires the upstream Definitions modules and their dependencies.
-/

import Definitions.Def_ModularForm_HeckeOperatorForms
attribute [-instance] FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2
attribute [-simp] FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero

theorem CuspForm.span_heckeTLin_eigen_eq_top (M : ℕ) [NeZero M] :
    Submodule.span ℂ {v : CuspForm (CongruenceSubgroup.Gamma0 M) 2 |
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M), ∃ c : ℂ,
        CuspForm.heckeTLin 2 hℓ hℓM v = c • v} = ⊤ := by
  sorry

open Filter Asymptotics
open scoped Topology

namespace Submission

/-- Vanishing through degree `b` is equivalent to decay of order `b + 1` at infinity.
`natCast_le_analyticOrderAt` supplies the local Taylor factorization; continuity bounds
its analytic factor near zero. The inverse q-parameter transfers the decay bound to a
punctured neighborhood, where any smaller finite analytic order gives a contradiction. -/
theorem f036cc6b1f_fd_coeff_decay :
    ∀ (Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)) (k : ℤ)
      (f : ModularForm Γ k), (1 : ℝ) ∈ Γ.strictPeriods → ∀ b : ℕ,
      (∀ n : ℕ, n ≤ b → (UpperHalfPlane.qExpansion 1 f).coeff n = 0) ↔
        ∃ C Y : ℝ, 0 ≤ C ∧ ∀ z : UpperHalfPlane, Y ≤ z.im →
          ‖f z‖ ≤ C * Real.exp (-2 * Real.pi * ((b + 1 : ℕ) : ℝ) * z.im) := by
  intro Γ k f hΓ b
  let F := UpperHalfPlane.cuspFunction 1 f
  have hF : AnalyticAt ℂ F 0 :=
    ModularFormClass.analyticAt_cuspFunction_zero f zero_lt_one hΓ
  -- Taylor coefficients vanish through b exactly when the analytic order is at least b + 1.
  have hcoeff : (∀ n : ℕ, n ≤ b → (UpperHalfPlane.qExpansion 1 f).coeff n = 0) ↔
      ((b + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt F 0 := by
    rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hF]
    simp only [UpperHalfPlane.qExpansion_coeff, mul_eq_zero, inv_eq_zero,
      Nat.cast_eq_zero, Nat.factorial_ne_zero, false_or, Nat.lt_succ_iff, F]
  have hnorm (z : UpperHalfPlane) (n : ℕ) :
      ‖Function.Periodic.qParam 1 z ^ n‖ =
        Real.exp (-2 * Real.pi * (n : ℝ) * z.im) := by
    rw [norm_pow, Function.Periodic.norm_qParam, div_one, UpperHalfPlane.coe_im,
      ← Real.exp_nat_mul]
    congr 1
    ring
  rw [hcoeff]
  constructor
  · intro horder
    -- Factor out the required power of q and bound the remaining analytic factor.
    obtain ⟨g, hg, hfg⟩ := (natCast_le_analyticOrderAt hF).mp horder
    have hbig : F =O[𝓝 0] (fun q : ℂ => q ^ (b + 1)) := by
      have hg' := hg.continuousAt.tendsto.isBigO_one ℂ
      have hp := (isBigO_refl (fun q : ℂ => q ^ (b + 1)) (𝓝 0)).mul hg'
      simp only [mul_one] at hp
      apply hp.congr' _ EventuallyEq.rfl
      filter_upwards [hfg] with q hq
      simpa only [sub_zero, smul_eq_mul] using hq.symm
    have hupper := hbig.comp_tendsto (UpperHalfPlane.qParam_tendsto_atImInfty
      (show (0 : ℝ) < 1 from zero_lt_one))
    obtain ⟨C, hC, hbound⟩ := hupper.exists_pos
    have hevent : ∀ᶠ z : UpperHalfPlane in UpperHalfPlane.atImInfty,
        ‖f z‖ ≤ C * Real.exp (-2 * Real.pi * ((b + 1 : ℕ) : ℝ) * z.im) := by
      filter_upwards [hbound.bound] with z hz
      simpa only [Function.comp_apply, F, SlashInvariantFormClass.eq_cuspFunction f z hΓ
        one_ne_zero, hnorm] using hz
    obtain ⟨Y, hY⟩ := (UpperHalfPlane.atImInfty_mem _).mp hevent
    exact ⟨C, Y, hC.le, hY⟩
  · rintro ⟨C, Y, _hC, hbound⟩
    -- Pull the height bound back to the punctured q-disk using the inverse parameter.
    have hinv := (Function.Periodic.invQParam_tendsto (show (0 : ℝ) < 1 from zero_lt_one))
    have hheight : ∀ᶠ q : ℂ in 𝓝[≠] 0,
        max Y 1 ≤ (Function.Periodic.invQParam 1 q).im :=
      (tendsto_comap_iff.mp hinv).eventually (eventually_ge_atTop (max Y 1))
    have hbig : F =O[𝓝[≠] 0] (fun q : ℂ => q ^ (b + 1)) := by
      apply IsBigO.of_bound C
      filter_upwards [hheight, self_mem_nhdsWithin] with q hq hq0
      have him : 0 < (Function.Periodic.invQParam 1 q).im :=
        lt_of_lt_of_le zero_lt_one ((le_max_right Y 1).trans hq)
      let z : UpperHalfPlane := ⟨Function.Periodic.invQParam 1 q, him⟩
      have hqz : Function.Periodic.qParam 1 z = q :=
        Function.Periodic.qParam_right_inv one_ne_zero hq0
      have hfz : F q = f z := by
        rw [← hqz]
        exact SlashInvariantFormClass.eq_cuspFunction f z hΓ one_ne_zero
      rw [hfz, ← hqz, hnorm]
      exact hbound z ((le_max_left Y 1).trans hq)
    -- A smaller finite order would give a nonzero factor whose limit is forced to be zero.
    by_contra horder
    have hfinite : analyticOrderAt F 0 ≠ ⊤ := by
      intro ht
      exact horder (ht ▸ le_top)
    obtain ⟨g, hg, hg0, hfg⟩ := hF.analyticOrderAt_ne_top.mp hfinite
    let m := analyticOrderNatAt F 0
    have hm : m < b + 1 := by
      have : ¬ ((b + 1 : ℕ) : ℕ∞) ≤ (m : ℕ∞) := by
        simpa only [m, Nat.cast_analyticOrderNatAt hfinite] using horder
      exact lt_of_not_ge (by exact_mod_cast this)
    have hlittle : F =o[𝓝[≠] 0] (fun q : ℂ => q ^ m) :=
      hbig.trans_isLittleO ((isLittleO_pow_pow hm).mono nhdsWithin_le_nhds)
    have hquot : (fun q : ℂ => F q / q ^ m) =ᶠ[𝓝[≠] 0] g := by
      filter_upwards [hfg.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with q hq hq0
      simp only [sub_zero, smul_eq_mul] at hq
      rw [hq, mul_div_cancel_left₀ _ (pow_ne_zero _ hq0)]
    exact hg0 (tendsto_nhds_unique hg.continuousAt.continuousWithinAt
      (hlittle.tendsto_div_nhds_zero.congr' hquot))

end Submission
