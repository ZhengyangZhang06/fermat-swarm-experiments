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
open scoped ModularForm

namespace Submission

/-- Above a common height, every coset factor other than the identity has norm at most one,
so the modular-form norm is bounded by the identity factor with constant `C = 1`. -/
theorem f036cc6b1f_fd_norm_bound :
    ∀ (M : ℕ) [NeZero M] (f : CuspForm (CongruenceSubgroup.Gamma0 M) 2),
      ∃ C Y : ℝ, 0 ≤ C ∧ ∀ z : UpperHalfPlane, Y ≤ z.im →
        ‖ModularForm.norm (MonoidHom.range (Matrix.SpecialLinearGroup.mapGL ℝ :
          Matrix.SpecialLinearGroup (Fin 2) ℤ →*
            Matrix.GeneralLinearGroup (Fin 2) ℝ)) f z‖ ≤ C * ‖f z‖ := by
  intro M _ f
  classical
  let H := MonoidHom.range (Matrix.SpecialLinearGroup.mapGL ℝ :
    Matrix.SpecialLinearGroup (Fin 2) ℤ →* Matrix.GeneralLinearGroup (Fin 2) ℝ)
  let Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ) := CongruenceSubgroup.Gamma0 M
  let Q := H ⧸ Γ.subgroupOf H
  let : Fintype Q := Fintype.ofFinite Q
  -- Arithmeticity packages the cusp condition for every integral slash translate.
  have hzero (q : Q) : UpperHalfPlane.IsZeroAtImInfty (SlashInvariantForm.quotientFunc f q) := by
    induction q using Quotient.inductionOn with
    | h r =>
      obtain ⟨g, hg⟩ := r.property
      change UpperHalfPlane.IsZeroAtImInfty ((f : UpperHalfPlane → ℂ) ∣[2] r.val⁻¹)
      rw [← hg, ← map_inv]
      simpa only [ModularForm.SL_slash, Matrix.SpecialLinearGroup.mapGL,
        MonoidHom.comp_apply, algebraMap_int_eq] using
          CuspFormClass.zero_at_infty_slash f g⁻¹
  have hbound (q : Q) : ∀ᶠ z in UpperHalfPlane.atImInfty,
      ‖SlashInvariantForm.quotientFunc f q z‖ ≤ 1 := by
    obtain ⟨Y, hY⟩ := UpperHalfPlane.isZeroAtImInfty_iff.mp (hzero q) 1 zero_lt_one
    exact (UpperHalfPlane.atImInfty_mem _).mpr ⟨Y, hY⟩
  -- Finiteness of Q makes the eventual bounds hold at one common height.
  obtain ⟨Y, hY⟩ := (UpperHalfPlane.atImInfty_mem _).mp (Filter.eventually_all.mpr hbound)
  refine ⟨1, Y, zero_le_one, ?_⟩
  intro z hz
  let q₀ : Q := ⟦(1 : H)⟧
  have hid : SlashInvariantForm.quotientFunc f q₀ z = f z := by
    simp [q₀]
  have hprod : ∏ q ∈ Finset.univ.erase q₀, ‖SlashInvariantForm.quotientFunc f q z‖ ≤ 1 :=
    Finset.prod_le_one (fun q _ ↦ norm_nonneg _) (fun q _ ↦ hY z hz q)
  calc
    ‖ModularForm.norm H f z‖ = ∏ q : Q, ‖SlashInvariantForm.quotientFunc f q z‖ := by
      simp only [ModularForm.coe_norm, Finset.prod_apply, norm_prod]
      rfl
    _ = ‖f z‖ * ∏ q ∈ Finset.univ.erase q₀, ‖SlashInvariantForm.quotientFunc f q z‖ := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ q₀), hid]
    _ ≤ 1 * ‖f z‖ := by
      simpa using mul_le_mul_of_nonneg_left hprod (norm_nonneg (f z))

end Submission

/-- The weight-two Sturm bound for `Gamma0 M`, obtained from the level-one norm. -/
theorem f036cc6b1f_fd_sturm (M : ℕ) [NeZero M]
    (f : CuspForm (CongruenceSubgroup.Gamma0 M) 2)
    (hf : ∀ n : ℕ, n ≤ (2 * (CongruenceSubgroup.Gamma0 M).index) / 12 →
      (UpperHalfPlane.qExpansion 1 f).coeff n = 0) : f = 0 := by
  classical
  let Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ) := CongruenceSubgroup.Gamma0 M
  let H := MonoidHom.range (Matrix.SpecialLinearGroup.mapGL ℝ :
    Matrix.SpecialLinearGroup (Fin 2) ℤ →* Matrix.GeneralLinearGroup (Fin 2) ℝ)
  let b := (2 * (CongruenceSubgroup.Gamma0 M).index) / 12
  have hperiod : (1 : ℝ) ∈ Γ.strictPeriods := by
    simp [Γ]
  obtain ⟨Cf, Yf, hCf, hf_decay⟩ :=
    (Submission.f036cc6b1f_fd_coeff_decay Γ 2 (ModularFormClass.modularForm f)
      hperiod b).mp hf
  -- Mapping into GL₂ preserves the index in the image of SL₂(ℤ).
  have hcard : Nat.card (H ⧸ Γ.subgroupOf H) = (CongruenceSubgroup.Gamma0 M).index := by
    change ((CongruenceSubgroup.Gamma0 M).map (Matrix.SpecialLinearGroup.mapGL ℝ)).relIndex H = _
    dsimp only [H]
    rw [MonoidHom.range_eq_map,
      Subgroup.relIndex_map_map_of_injective _ _ Matrix.SpecialLinearGroup.mapGL_injective,
      Subgroup.relIndex_top_right]
  have hweight : (2 : ℤ) * Nat.card (H ⧸ Γ.subgroupOf H) =
      ((2 * (CongruenceSubgroup.Gamma0 M).index : ℕ) : ℤ) := by
    rw [hcard]
    simp
  let N := ModularForm.mcast hweight (ModularForm.norm H f)
  obtain ⟨Cn, Yn, hCn, hnorm_bound⟩ := Submission.f036cc6b1f_fd_norm_bound M f
  have hNcoeff : ∀ n : ℕ, n ≤ b → (UpperHalfPlane.qExpansion 1 N).coeff n = 0 := by
    apply (Submission.f036cc6b1f_fd_coeff_decay H _ N one_mem_strictPeriods_SL b).mpr
    refine ⟨Cn * Cf, max Yf Yn, mul_nonneg hCn hCf, ?_⟩
    intro z hz
    calc
      ‖N z‖ ≤ Cn * ‖f z‖ := hnorm_bound z ((le_max_right Yf Yn).trans hz)
      _ ≤ Cn * (Cf * Real.exp (-2 * Real.pi * ((b + 1 : ℕ) : ℝ) * z.im)) :=
        mul_le_mul_of_nonneg_left (hf_decay z ((le_max_left Yf Yn).trans hz)) hCn
      _ = (Cn * Cf) * Real.exp (-2 * Real.pi * ((b + 1 : ℕ) : ℝ) * z.im) :=
        (mul_assoc _ _ _).symm
  have hNzero : N = 0 := by
    apply ModularForm.sturm_bound_levelOne_nat
    have horder := PowerSeries.nat_le_order (UpperHalfPlane.qExpansion 1 N) (b + 1)
      (fun n hn => hNcoeff n (Nat.lt_succ_iff.mp hn))
    exact lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self b) horder
  have hnorm_zero : ModularForm.norm H f = 0 :=
    (ModularForm.mcast_eq_zero_iff hweight rfl _).mp hNzero
  exact DFunLike.coe_injective ((ModularForm.norm_eq_zero_iff H f).mp hnorm_zero)
