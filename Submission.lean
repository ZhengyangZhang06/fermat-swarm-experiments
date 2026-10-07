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

theorem Submission.f036cc6b1f_pic_dd_ae_orbit_zero :
    ∀ (Δ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) (E : Set UpperHalfPlane) (A : UpperHalfPlane → ℝ), MeasurableSet E → Measurable A → (∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane), ∃ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, γ ∈ Δ ∧ γ • z ∈ E) → (∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), γ ∈ Δ → ∀ z : UpperHalfPlane, A (γ • z) = A z) → (∀ᵐ z ∂((MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane).restrict E), A z = 0) → ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane), A z = 0 := by
  intro Δ E A hE _hA hcover hinv hzero
  have : Countable (Matrix (Fin 2) (Fin 2) ℤ) :=
    inferInstanceAs (Countable (Fin 2 → Fin 2 → ℤ))
  have : Countable (Matrix.SpecialLinearGroup (Fin 2) ℤ) :=
    inferInstanceAs (Countable {g : Matrix (Fin 2) (Fin 2) ℤ // g.det = 1})
  have hzero' : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane),
      z ∈ E → A z = 0 :=
    (MeasureTheory.ae_restrict_iff' hE).mp hzero
  have htranslate : ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane),
        γ • z ∈ E → A (γ • z) = 0 := by
    intro γ
    exact (MeasureTheory.measurePreserving_smul (Matrix.SpecialLinearGroup.mapGL ℝ γ)
      (MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane)).quasiMeasurePreserving.ae
        hzero'
  have hall : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane),
      ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, γ • z ∈ E → A (γ • z) = 0 :=
    MeasureTheory.ae_all_iff.mpr htranslate
  filter_upwards [hcover, hall] with z hz hzall
  obtain ⟨γ, hγ, hzE⟩ := hz
  exact (hinv γ hγ z).symm.trans (hzall γ hzE)
theorem Submission.f036cc6b1f_pic_dd_open_pos :
    MeasureTheory.Measure.IsOpenPosMeasure
      (MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane) := by
  let : MeasureTheory.Measure.IsOpenPosMeasure
      ((MeasureTheory.volume : MeasureTheory.Measure ℂ).comap UpperHalfPlane.coe) :=
    MeasureTheory.Measure.IsOpenPosMeasure.comap _ UpperHalfPlane.isOpenEmbedding_coe
  rw [UpperHalfPlane.volume_def]
  apply MeasureTheory.Measure.AbsolutelyContinuous.isOpenPosMeasure
    (μ := (MeasureTheory.volume : MeasureTheory.Measure ℂ).comap UpperHalfPlane.coe)
  apply MeasureTheory.withDensity_absolutelyContinuous'
  · have hw : Continuous (fun z : UpperHalfPlane ↦
        (1 / NNReal.mk z.im z.im_pos.le : NNReal) ^ 2) := by
      refine .pow (.div₀ continuous_const ?_ ?_) _
      · exact UpperHalfPlane.continuous_im.subtype_mk _
      · exact fun z ↦ NNReal.ne_iff.mp z.im_ne_zero
    exact hw.measurable.coe_nnreal_ennreal.aemeasurable
  · exact Filter.Eventually.of_forall fun z ↦
      ENNReal.coe_ne_zero.mpr (pow_ne_zero 2
        (div_ne_zero one_ne_zero (NNReal.ne_iff.mp z.im_ne_zero)))

namespace Submission

open MeasureTheory

theorem f036cc6b1f_pic_diagonal_definite :
    ∀ (Δ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) (E : Set UpperHalfPlane),
      MeasurableSet E →
      (∀ᵐ z ∂(volume : Measure UpperHalfPlane),
        ∃ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, γ ∈ Δ ∧ γ • z ∈ E) →
      ∀ f : CuspForm Δ 2,
        IntegrableOn (UpperHalfPlane.petersson 2 f f) E (volume : Measure UpperHalfPlane) →
        integral ((volume : Measure UpperHalfPlane).restrict E)
          (UpperHalfPlane.petersson 2 f f) = 0 → f = 0 := by
  intro Δ E hE hcover f hf hzero
  let A : UpperHalfPlane → ℝ := fun z => (UpperHalfPlane.petersson 2 f f z).re
  have hA (z : UpperHalfPlane) : A z = Complex.normSq (f z) * z.im ^ 2 := by
    simp [A, UpperHalfPlane.petersson, ← Complex.normSq_eq_conj_mul_self,
      ← Complex.ofReal_pow]
  have hcont : Continuous A :=
    Complex.continuous_re.comp (UpperHalfPlane.petersson_continuous 2
      (CuspFormClass.holo f).continuous (CuspFormClass.holo f).continuous)
  have hnonneg : 0 ≤ A := by
    intro z
    rw [Pi.zero_apply, hA]
    exact mul_nonneg (Complex.normSq_nonneg _) (sq_nonneg _)
  have hint : Integrable A ((volume : Measure UpperHalfPlane).restrict E) := hf.re
  have hint_zero : integral ((volume : Measure UpperHalfPlane).restrict E) A = 0 := by
    calc
      _ = (integral ((volume : Measure UpperHalfPlane).restrict E)
          (UpperHalfPlane.petersson 2 f f)).re := integral_re hf
      _ = 0 := by rw [hzero]; rfl
  have hzero_E : ∀ᵐ z ∂((volume : Measure UpperHalfPlane).restrict E), A z = 0 :=
    (integral_eq_zero_iff_of_nonneg hnonneg hint).mp hint_zero
  have hinv (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (hγ : γ ∈ Δ)
      (z : UpperHalfPlane) : A (γ • z) = A z := by
    have hγ' : (γ : Matrix.GeneralLinearGroup (Fin 2) ℝ) ∈
        (Δ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)) :=
      Subgroup.mem_map.mpr ⟨γ, hγ, rfl⟩
    exact congrArg Complex.re
      (SlashInvariantFormClass.petersson_smul (f := f) (f' := f) (τ := z) hγ')
  have hzero_ae : ∀ᵐ z ∂(volume : Measure UpperHalfPlane), A z = 0 :=
    f036cc6b1f_pic_dd_ae_orbit_zero Δ E A hE hcont.measurable hcover hinv hzero_E
  have : Measure.IsOpenPosMeasure (volume : Measure UpperHalfPlane) :=
    f036cc6b1f_pic_dd_open_pos
  have hzero_all : A = 0 := Measure.eq_of_ae_eq hzero_ae hcont continuous_const
  apply CuspForm.ext
  intro z
  change f z = 0
  apply Complex.normSq_eq_zero.mp
  have hz : Complex.normSq (f z) * z.im ^ 2 = 0 := by
    rw [← hA, hzero_all]
    rfl
  exact (mul_eq_zero.mp hz).resolve_right (pow_ne_zero _ z.im_ne_zero)

end Submission

theorem CuspForm.span_heckeTLin_eigen_eq_top (M : ℕ) [NeZero M] :
    Submodule.span ℂ {v : CuspForm (CongruenceSubgroup.Gamma0 M) 2 |
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M), ∃ c : ℂ,
        CuspForm.heckeTLin 2 hℓ hℓM v = c • v} = ⊤ := by
  sorry

theorem Submission.f036cc6b1f_tdi_planar_exp_integrable_fd :
    ∀ (a : ℝ), 0 < a → MeasureTheory.IntegrableOn
      (fun z : UpperHalfPlane => Real.exp (-a * z.im)) ModularGroup.fd
      ((MeasureTheory.volume : MeasureTheory.Measure ℂ).comap UpperHalfPlane.coe) := by
  intro a ha
  let b : ℝ := Real.sqrt 3 / 2
  have hy : MeasureTheory.IntegrableOn (fun y : ℝ => Real.exp (-a * y))
      (Set.Ici b) :=
    (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr
      (exp_neg_integrableOn_Ioi b ha)
  have hx : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ))
      (Set.Icc (-(1 / 2 : ℝ)) (1 / 2)) :=
    MeasureTheory.integrableOn_const (by
      rw [Real.volume_Icc]
      exact ENNReal.ofReal_ne_top)
  have hprod : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => Real.exp (-a * p.2))
      (Set.Icc (-(1 / 2 : ℝ)) (1 / 2) ×ˢ Set.Ici b) := by
    change MeasureTheory.Integrable _
      (((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod MeasureTheory.volume).restrict _)
    rw [← MeasureTheory.Measure.prod_restrict]
    simpa only [one_mul] using hx.mul_prod hy
  have hc : MeasureTheory.IntegrableOn (fun z : ℂ => Real.exp (-a * z.im))
      (Complex.measurableEquivRealProd ⁻¹'
        (Set.Icc (-(1 / 2 : ℝ)) (1 / 2) ×ˢ Set.Ici b)) :=
    (Complex.volume_preserving_equiv_real_prod.integrableOn_comp_preimage
      Complex.measurableEquivRealProd.measurableEmbedding).mpr hprod
  have hi : MeasureTheory.IntegrableOn (fun z : ℂ => Real.exp (-a * z.im))
      (UpperHalfPlane.coe '' ModularGroup.fd) := by
    apply hc.mono_set
    rintro _ ⟨z, hz, rfl⟩
    change z.re ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2) ∧ b ≤ z.im
    constructor
    · exact abs_le.mp hz.2
    · dsimp [b]
      have hsq := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hz
      have hpos := z.im_pos
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg (3 : ℝ)]
  have ht := (UpperHalfPlane.measurableEmbedding_coe.integrableOn_iff_comap
    (Set.image_subset_range UpperHalfPlane.coe ModularGroup.fd)).mp hi
  simpa only [Set.preimage_image_eq _ UpperHalfPlane.coe_injective, Function.comp_def,
    UpperHalfPlane.coe_im] using ht

theorem Submission.f036cc6b1f_tdi_petersson_integrable_of_exp_product_bound
    (u v : UpperHalfPlane → ℂ) (a C Y : ℝ)
    (hu : Continuous u) (hv : Continuous v) (ha : 0 < a) (_hC : 0 ≤ C)
    (hbound : ∀ z : UpperHalfPlane, Y ≤ z.im →
      ‖u z * v z‖ ≤ C * Real.exp (-a * z.im)) :
    MeasureTheory.IntegrableOn (UpperHalfPlane.petersson 2 u v) ModularGroup.fd
      (MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane) := by
  let ν : MeasureTheory.Measure UpperHalfPlane :=
    (MeasureTheory.volume : MeasureTheory.Measure ℂ).comap UpperHalfPlane.coe
  let W : UpperHalfPlane → ℂ := fun z ↦ (starRingEnd ℂ) (u z) * v z
  let L : ℝ := max 1 Y
  let D := ModularGroup.truncatedFundamentalDomain L
  let E := ModularGroup.fd ∩ {z : UpperHalfPlane | L < z.im}
  have hW : Continuous W := (Complex.continuous_conj.comp hu).mul hv
  -- The lower truncation is compact and planar measure is finite on compact sets.
  have hD : MeasureTheory.IntegrableOn W D ν :=
    hW.continuousOn.integrableOn_compact
      (ModularGroup.isCompact_truncatedFundamentalDomain L)
  have hEmeas : MeasurableSet E :=
    ModularGroup.isClosed_fd.measurableSet.inter
      (isOpen_lt continuous_const UpperHalfPlane.continuous_im).measurableSet
  -- On the tail, use precisely the supplied planar exponential-integrability interface.
  have hmajor : MeasureTheory.IntegrableOn
      (fun z : UpperHalfPlane ↦ C * Real.exp (-a * z.im)) E ν :=
    ((Submission.f036cc6b1f_tdi_planar_exp_integrable_fd a ha).mono_set
      Set.inter_subset_left).const_mul C
  have hE : MeasureTheory.IntegrableOn W E ν := by
    refine hmajor.mono' hW.aestronglyMeasurable ?_
    filter_upwards [MeasureTheory.ae_restrict_mem hEmeas] with z hz
    have hY : Y ≤ z.im := (le_max_right 1 Y).trans hz.2.le
    simpa only [W, norm_mul, Complex.norm_conj] using hbound z hY
  have hpartition : D ∪ E = ModularGroup.fd := by
    ext z
    change (z ∈ ModularGroup.fd ∧ z.im ≤ L) ∨
      (z ∈ ModularGroup.fd ∧ L < z.im) ↔ z ∈ ModularGroup.fd
    constructor
    · rintro (hz | hz) <;> exact hz.1
    · intro hz
      rcases le_or_gt z.im L with h | h
      · exact Or.inl ⟨hz, h⟩
      · exact Or.inr ⟨hz, h⟩
  have hplanar : MeasureTheory.IntegrableOn W ModularGroup.fd ν := by
    rw [← hpartition]
    exact hD.union hE
  -- Multiplication by the hyperbolic density cancels the weight-two factor.
  rw [MeasureTheory.IntegrableOn, UpperHalfPlane.volume_def,
    MeasureTheory.restrict_withDensity ModularGroup.isClosed_fd.measurableSet]
  have hdensity : Measurable (fun z : UpperHalfPlane ↦
      (1 / NNReal.mk z.im z.im_pos.le : NNReal) ^ 2) := by
    fun_prop
  rw [MeasureTheory.integrable_withDensity_iff_integrable_coe_smul hdensity]
  have hcancel : (fun z : UpperHalfPlane ↦
      (((1 / NNReal.mk z.im z.im_pos.le : NNReal) ^ 2 : NNReal) : ℝ) •
        UpperHalfPlane.petersson 2 u v z) = W := by
    funext z
    simp only [UpperHalfPlane.petersson, zpow_ofNat, NNReal.coe_pow,
      NNReal.coe_div, NNReal.coe_one, NNReal.coe_mk, Complex.real_smul,
      Complex.ofReal_pow, Complex.ofReal_div, Complex.ofReal_one, W]
    have hz : (z.im : ℂ) ≠ 0 := by exact_mod_cast z.im_ne_zero
    field_simp
  rw [hcancel]
  exact hplanar

namespace Submission

open UpperHalfPlane MeasureTheory Matrix.SpecialLinearGroup
open scoped MatrixGroups ModularForm Pointwise

open Filter Asymptotics
open scoped Topology ModularForm

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

theorem CuspForm.span_heckeTLin_eigen_eq_top (M : ℕ) [NeZero M] :
    Submodule.span ℂ {v : CuspForm (CongruenceSubgroup.Gamma0 M) 2 |
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M), ∃ c : ℂ,
        CuspForm.heckeTLin 2 hℓ hℓM v = c • v} = ⊤ := by
  sorry
theorem Submission.f036cc6b1f_pic_dd_ae_orbit_zero :
    ∀ (Δ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) (E : Set UpperHalfPlane) (A : UpperHalfPlane → ℝ), MeasurableSet E → Measurable A → (∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane), ∃ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, γ ∈ Δ ∧ γ • z ∈ E) → (∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), γ ∈ Δ → ∀ z : UpperHalfPlane, A (γ • z) = A z) → (∀ᵐ z ∂((MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane).restrict E), A z = 0) → ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane), A z = 0 := by
  intro Δ E A hE _hA hcover hinv hzero
  have : Countable (Matrix (Fin 2) (Fin 2) ℤ) :=
    inferInstanceAs (Countable (Fin 2 → Fin 2 → ℤ))
  have : Countable (Matrix.SpecialLinearGroup (Fin 2) ℤ) :=
    inferInstanceAs (Countable {g : Matrix (Fin 2) (Fin 2) ℤ // g.det = 1})
  have hzero' : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane),
      z ∈ E → A z = 0 :=
    (MeasureTheory.ae_restrict_iff' hE).mp hzero
  have htranslate : ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane),
        γ • z ∈ E → A (γ • z) = 0 := by
    intro γ
    exact (MeasureTheory.measurePreserving_smul (Matrix.SpecialLinearGroup.mapGL ℝ γ)
      (MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane)).quasiMeasurePreserving.ae
        hzero'
  have hall : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane),
      ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, γ • z ∈ E → A (γ • z) = 0 :=
    MeasureTheory.ae_all_iff.mpr htranslate
  filter_upwards [hcover, hall] with z hz hzall
  obtain ⟨γ, hγ, hzE⟩ := hz
  exact (hinv γ hγ z).symm.trans (hzall γ hzE)
theorem Submission.f036cc6b1f_pic_dd_open_pos :
    MeasureTheory.Measure.IsOpenPosMeasure
      (MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane) := by
  let : MeasureTheory.Measure.IsOpenPosMeasure
      ((MeasureTheory.volume : MeasureTheory.Measure ℂ).comap UpperHalfPlane.coe) :=
    MeasureTheory.Measure.IsOpenPosMeasure.comap _ UpperHalfPlane.isOpenEmbedding_coe
  rw [UpperHalfPlane.volume_def]
  apply MeasureTheory.Measure.AbsolutelyContinuous.isOpenPosMeasure
    (μ := (MeasureTheory.volume : MeasureTheory.Measure ℂ).comap UpperHalfPlane.coe)
  apply MeasureTheory.withDensity_absolutelyContinuous'
  · have hw : Continuous (fun z : UpperHalfPlane ↦
        (1 / NNReal.mk z.im z.im_pos.le : NNReal) ^ 2) := by
      refine .pow (.div₀ continuous_const ?_ ?_) _
      · exact UpperHalfPlane.continuous_im.subtype_mk _
      · exact fun z ↦ NNReal.ne_iff.mp z.im_ne_zero
    exact hw.measurable.coe_nnreal_ennreal.aemeasurable
  · exact Filter.Eventually.of_forall fun z ↦
      ENNReal.coe_ne_zero.mpr (pow_ne_zero 2
        (div_ne_zero one_ne_zero (NNReal.ne_iff.mp z.im_ne_zero)))

namespace Submission

open MeasureTheory

theorem f036cc6b1f_pic_diagonal_definite :
    ∀ (Δ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) (E : Set UpperHalfPlane),
      MeasurableSet E →
      (∀ᵐ z ∂(volume : Measure UpperHalfPlane),
        ∃ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, γ ∈ Δ ∧ γ • z ∈ E) →
      ∀ f : CuspForm Δ 2,
        IntegrableOn (UpperHalfPlane.petersson 2 f f) E (volume : Measure UpperHalfPlane) →
        integral ((volume : Measure UpperHalfPlane).restrict E)
          (UpperHalfPlane.petersson 2 f f) = 0 → f = 0 := by
  intro Δ E hE hcover f hf hzero
  let A : UpperHalfPlane → ℝ := fun z => (UpperHalfPlane.petersson 2 f f z).re
  have hA (z : UpperHalfPlane) : A z = Complex.normSq (f z) * z.im ^ 2 := by
    simp [A, UpperHalfPlane.petersson, ← Complex.normSq_eq_conj_mul_self,
      ← Complex.ofReal_pow]
  have hcont : Continuous A :=
    Complex.continuous_re.comp (UpperHalfPlane.petersson_continuous 2
      (CuspFormClass.holo f).continuous (CuspFormClass.holo f).continuous)
  have hnonneg : 0 ≤ A := by
    intro z
    rw [Pi.zero_apply, hA]
    exact mul_nonneg (Complex.normSq_nonneg _) (sq_nonneg _)
  have hint : Integrable A ((volume : Measure UpperHalfPlane).restrict E) := hf.re
  have hint_zero : integral ((volume : Measure UpperHalfPlane).restrict E) A = 0 := by
    calc
      _ = (integral ((volume : Measure UpperHalfPlane).restrict E)
          (UpperHalfPlane.petersson 2 f f)).re := integral_re hf
      _ = 0 := by rw [hzero]; rfl
  have hzero_E : ∀ᵐ z ∂((volume : Measure UpperHalfPlane).restrict E), A z = 0 :=
    (integral_eq_zero_iff_of_nonneg hnonneg hint).mp hint_zero
  have hinv (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (hγ : γ ∈ Δ)
      (z : UpperHalfPlane) : A (γ • z) = A z := by
    have hγ' : (γ : Matrix.GeneralLinearGroup (Fin 2) ℝ) ∈
        (Δ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)) :=
      Subgroup.mem_map.mpr ⟨γ, hγ, rfl⟩
    exact congrArg Complex.re
      (SlashInvariantFormClass.petersson_smul (f := f) (f' := f) (τ := z) hγ')
  have hzero_ae : ∀ᵐ z ∂(volume : Measure UpperHalfPlane), A z = 0 :=
    f036cc6b1f_pic_dd_ae_orbit_zero Δ E A hE hcont.measurable hcover hinv hzero_E
  have : Measure.IsOpenPosMeasure (volume : Measure UpperHalfPlane) :=
    f036cc6b1f_pic_dd_open_pos
  have hzero_all : A = 0 := Measure.eq_of_ae_eq hzero_ae hcont continuous_const
  apply CuspForm.ext
  intro z
  change f z = 0
  apply Complex.normSq_eq_zero.mp
  have hz : Complex.normSq (f z) * z.im ^ 2 = 0 := by
    rw [← hA, hzero_all]
    rfl
  exact (mul_eq_zero.mp hz).resolve_right (pow_ne_zero _ z.im_ne_zero)

end Submission

theorem Submission.f036cc6b1f_tdi_planar_exp_integrable_fd :
    ∀ (a : ℝ), 0 < a → MeasureTheory.IntegrableOn
      (fun z : UpperHalfPlane => Real.exp (-a * z.im)) ModularGroup.fd
      ((MeasureTheory.volume : MeasureTheory.Measure ℂ).comap UpperHalfPlane.coe) := by
  intro a ha
  let b : ℝ := Real.sqrt 3 / 2
  have hy : MeasureTheory.IntegrableOn (fun y : ℝ => Real.exp (-a * y))
      (Set.Ici b) :=
    (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr
      (exp_neg_integrableOn_Ioi b ha)
  have hx : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ))
      (Set.Icc (-(1 / 2 : ℝ)) (1 / 2)) :=
    MeasureTheory.integrableOn_const (by
      rw [Real.volume_Icc]
      exact ENNReal.ofReal_ne_top)
  have hprod : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => Real.exp (-a * p.2))
      (Set.Icc (-(1 / 2 : ℝ)) (1 / 2) ×ˢ Set.Ici b) := by
    change MeasureTheory.Integrable _
      (((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod MeasureTheory.volume).restrict _)
    rw [← MeasureTheory.Measure.prod_restrict]
    simpa only [one_mul] using hx.mul_prod hy
  have hc : MeasureTheory.IntegrableOn (fun z : ℂ => Real.exp (-a * z.im))
      (Complex.measurableEquivRealProd ⁻¹'
        (Set.Icc (-(1 / 2 : ℝ)) (1 / 2) ×ˢ Set.Ici b)) :=
    (Complex.volume_preserving_equiv_real_prod.integrableOn_comp_preimage
      Complex.measurableEquivRealProd.measurableEmbedding).mpr hprod
  have hi : MeasureTheory.IntegrableOn (fun z : ℂ => Real.exp (-a * z.im))
      (UpperHalfPlane.coe '' ModularGroup.fd) := by
    apply hc.mono_set
    rintro _ ⟨z, hz, rfl⟩
    change z.re ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2) ∧ b ≤ z.im
    constructor
    · exact abs_le.mp hz.2
    · dsimp [b]
      have hsq := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hz
      have hpos := z.im_pos
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg (3 : ℝ)]
  have ht := (UpperHalfPlane.measurableEmbedding_coe.integrableOn_iff_comap
    (Set.image_subset_range UpperHalfPlane.coe ModularGroup.fd)).mp hi
  simpa only [Set.preimage_image_eq _ UpperHalfPlane.coe_injective, Function.comp_def,
    UpperHalfPlane.coe_im] using ht

theorem Submission.f036cc6b1f_tdi_petersson_integrable_of_exp_product_bound
    (u v : UpperHalfPlane → ℂ) (a C Y : ℝ)
    (hu : Continuous u) (hv : Continuous v) (ha : 0 < a) (_hC : 0 ≤ C)
    (hbound : ∀ z : UpperHalfPlane, Y ≤ z.im →
      ‖u z * v z‖ ≤ C * Real.exp (-a * z.im)) :
    MeasureTheory.IntegrableOn (UpperHalfPlane.petersson 2 u v) ModularGroup.fd
      (MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane) := by
  let ν : MeasureTheory.Measure UpperHalfPlane :=
    (MeasureTheory.volume : MeasureTheory.Measure ℂ).comap UpperHalfPlane.coe
  let W : UpperHalfPlane → ℂ := fun z ↦ (starRingEnd ℂ) (u z) * v z
  let L : ℝ := max 1 Y
  let D := ModularGroup.truncatedFundamentalDomain L
  let E := ModularGroup.fd ∩ {z : UpperHalfPlane | L < z.im}
  have hW : Continuous W := (Complex.continuous_conj.comp hu).mul hv
  -- The lower truncation is compact and planar measure is finite on compact sets.
  have hD : MeasureTheory.IntegrableOn W D ν :=
    hW.continuousOn.integrableOn_compact
      (ModularGroup.isCompact_truncatedFundamentalDomain L)
  have hEmeas : MeasurableSet E :=
    ModularGroup.isClosed_fd.measurableSet.inter
      (isOpen_lt continuous_const UpperHalfPlane.continuous_im).measurableSet
  -- On the tail, use precisely the supplied planar exponential-integrability interface.
  have hmajor : MeasureTheory.IntegrableOn
      (fun z : UpperHalfPlane ↦ C * Real.exp (-a * z.im)) E ν :=
    ((Submission.f036cc6b1f_tdi_planar_exp_integrable_fd a ha).mono_set
      Set.inter_subset_left).const_mul C
  have hE : MeasureTheory.IntegrableOn W E ν := by
    refine hmajor.mono' hW.aestronglyMeasurable ?_
    filter_upwards [MeasureTheory.ae_restrict_mem hEmeas] with z hz
    have hY : Y ≤ z.im := (le_max_right 1 Y).trans hz.2.le
    simpa only [W, norm_mul, Complex.norm_conj] using hbound z hY
  have hpartition : D ∪ E = ModularGroup.fd := by
    ext z
    change (z ∈ ModularGroup.fd ∧ z.im ≤ L) ∨
      (z ∈ ModularGroup.fd ∧ L < z.im) ↔ z ∈ ModularGroup.fd
    constructor
    · rintro (hz | hz) <;> exact hz.1
    · intro hz
      rcases le_or_gt z.im L with h | h
      · exact Or.inl ⟨hz, h⟩
      · exact Or.inr ⟨hz, h⟩
  have hplanar : MeasureTheory.IntegrableOn W ModularGroup.fd ν := by
    rw [← hpartition]
    exact hD.union hE
  -- Multiplication by the hyperbolic density cancels the weight-two factor.
  rw [MeasureTheory.IntegrableOn, UpperHalfPlane.volume_def,
    MeasureTheory.restrict_withDensity ModularGroup.isClosed_fd.measurableSet]
  have hdensity : Measurable (fun z : UpperHalfPlane ↦
      (1 / NNReal.mk z.im z.im_pos.le : NNReal) ^ 2) := by
    fun_prop
  rw [MeasureTheory.integrable_withDensity_iff_integrable_coe_smul hdensity]
  have hcancel : (fun z : UpperHalfPlane ↦
      (((1 / NNReal.mk z.im z.im_pos.le : NNReal) ^ 2 : NNReal) : ℝ) •
        UpperHalfPlane.petersson 2 u v z) = W := by
    funext z
    simp only [UpperHalfPlane.petersson, zpow_ofNat, NNReal.coe_pow,
      NNReal.coe_div, NNReal.coe_one, NNReal.coe_mk, Complex.real_smul,
      Complex.ofReal_pow, Complex.ofReal_div, Complex.ofReal_one, W]
    have hz : (z.im : ℂ) ≠ 0 := by exact_mod_cast z.im_ne_zero
    field_simp
  rw [hcancel]
  exact hplanar

theorem Submission.f036cc6b1f_pc_hi_rational_slash
    (Γ Δ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
    [Γ.FiniteIndex] [Δ.FiniteIndex]
    (A : Matrix.GeneralLinearGroup (Fin 2) ℝ)
    (_hpos : 0 < (A.det : ℝ))
    (hrat : ∀ i j : Fin 2, ∃ q : ℚ, A i j = (q : ℝ))
    (hconj : ∀ δ : Matrix.SpecialLinearGroup (Fin 2) ℤ, δ ∈ Δ →
      A * Matrix.SpecialLinearGroup.mapGL ℝ δ * A⁻¹ ∈
        (Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ))) :
    ∀ f : CuspForm Γ 2, ∃ g : CuspForm Δ 2,
      (g : UpperHalfPlane → ℂ) =
        SlashAction.map (2 : ℤ) A (f : UpperHalfPlane → ℂ) := by
  classical
  intro f
  choose q hq using hrat
  have rational_cusp (c : OnePoint ℝ)
      (hc : c ∈ Set.range (OnePoint.map (Rat.cast : ℚ → ℝ))) :
      A • c ∈ Set.range (OnePoint.map (Rat.cast : ℚ → ℝ)) := by
    obtain ⟨r, rfl⟩ := hc
    cases r with
    | infty =>
      rw [OnePoint.map_infty, OnePoint.smul_infty_eq_ite]
      split
      · exact ⟨OnePoint.infty, rfl⟩
      · refine ⟨↑(q 0 0 / q 1 0), ?_⟩
        simp [hq]
    | coe r =>
      rw [OnePoint.map_some, OnePoint.smul_some_eq_ite]
      split
      · exact ⟨OnePoint.infty, rfl⟩
      · refine ⟨↑((q 0 0 * r + q 0 1) / (q 1 0 * r + q 1 1)), ?_⟩
        simp [hq]
  refine ⟨{
    toFun := SlashAction.map (2 : ℤ) A (f : UpperHalfPlane → ℂ)
    slash_action_eq' := ?_
    holo' := (CuspFormClass.holo f).slash 2 A
    zero_at_cusps' := ?_
  }, rfl⟩
  · rintro _ ⟨δ, hδ, rfl⟩
    rw [← SlashAction.slash_mul]
    have hmul : A * Matrix.SpecialLinearGroup.mapGL ℝ δ =
        (A * Matrix.SpecialLinearGroup.mapGL ℝ δ * A⁻¹) * A := by
      simp [mul_assoc]
    rw [hmul, SlashAction.slash_mul,
      SlashInvariantFormClass.slash_action_eq f _ (hconj δ hδ)]
  · intro c hc
    apply OnePoint.IsZeroAt.smul_iff.mp
    apply CuspFormClass.zero_at_cusps f
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z, isCusp_SL2Z_iff] at hc ⊢
    exact rational_cusp c hc


theorem Submission.f036cc6b1f_pc_hi_gpt_unique_projective_index :
    ∀ (p : ℕ), p.Prime → ∀ (a b v : ℤ),
      (¬ (p : ℤ) ∣ a ∨ ¬ (p : ℤ) ∣ b) → ¬ (p : ℤ) ∣ v →
      ∃! i : Fin (p + 1), (p : ℤ) ∣
        (if i.val < p then b - a * (i.val : ℤ) else a * v + b * (p : ℤ)) := by
  intro p hp a b v hab hv
  let : Fact p.Prime := ⟨hp⟩
  have hv' : (v : ZMod p) ≠ 0 := by
    exact fun h => hv ((ZMod.intCast_zmod_eq_zero_iff_dvd v p).mp h)
  by_cases ha : (a : ZMod p) = 0
  · have hb : (b : ZMod p) ≠ 0 := by
      rcases hab with ha' | hb'
      · exact (ha' ((ZMod.intCast_zmod_eq_zero_iff_dvd a p).mp ha)).elim
      · exact fun h => hb' ((ZMod.intCast_zmod_eq_zero_iff_dvd b p).mp h)
    refine ⟨Fin.last p, ?_, ?_⟩
    · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
      simp [ha]
    · intro i hi
      by_cases hip : i.val < p
      · have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hi
        simp [hip, ha] at hz
        exact (hb hz).elim
      · apply Fin.ext
        have hil := i.isLt
        simp only [Fin.val_last]
        omega
  · let x : ZMod p := (b : ZMod p) / (a : ZMod p)
    have hxlt : x.val < p := ZMod.val_lt x
    let j : Fin (p + 1) := ⟨x.val, Nat.lt_succ_of_lt hxlt⟩
    have hjlt : j.val < p := hxlt
    have hj : (a : ZMod p) * (j.val : ZMod p) = (b : ZMod p) := by
      change (a : ZMod p) * (x.val : ZMod p) = (b : ZMod p)
      rw [ZMod.natCast_zmod_val]
      exact mul_div_cancel₀ _ ha
    refine ⟨j, ?_, ?_⟩
    · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
      simp only [if_pos hjlt, Int.cast_sub, Int.cast_mul, Int.cast_natCast, hj,
        sub_self]
    · intro i hi
      have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hi
      by_cases hip : i.val < p
      · have hi' : (a : ZMod p) * (i.val : ZMod p) = (b : ZMod p) := by
          symm
          simpa only [if_pos hip, Int.cast_sub, Int.cast_mul, Int.cast_natCast,
            sub_eq_zero] using hz
        have hij : (i.val : ZMod p) = (j.val : ZMod p) :=
          mul_left_cancel₀ ha (hi'.trans hj.symm)
        apply Fin.ext
        have hval := congrArg ZMod.val hij
        simpa only [ZMod.val_natCast_of_lt hip, ZMod.val_natCast_of_lt hjlt] using hval
      · have hzero : (a : ZMod p) * (v : ZMod p) = 0 := by
          simpa [hip] using hz
        exact (mul_ne_zero ha hv' hzero).elim
theorem Submission.f036cc6b1f_pc_hi_gpt_bezout_lift :
    ∀ (M : ℕ) [NeZero M] (p : ℕ), p.Prime → ¬ p ∣ M →
      ∃ (v : ℤ) (σ β : Matrix.SpecialLinearGroup (Fin 2) ℤ),
        (¬ (p : ℤ) ∣ v) ∧ σ ∈ CongruenceSubgroup.Gamma0 M ∧
        β ∈ CongruenceSubgroup.Gamma0 M ∧ σ 0 0 = (p : ℤ) ∧ σ 0 1 = -v ∧
        ModularForm.heckeMatrix p 0 * Matrix.SpecialLinearGroup.mapGL ℝ σ =
          Matrix.SpecialLinearGroup.mapGL ℝ β * ModularForm.heckeDiagMatrix p := by
  intro M _ p hp hpM
  let u : ℤ := Nat.gcdA p M
  let v : ℤ := Nat.gcdB p M
  have hcop : Nat.Coprime p M := hp.coprime_iff_not_dvd.mpr hpM
  have hbez : (p : ℤ) * u + (M : ℤ) * v = 1 := by
    simpa only [hcop.gcd_eq_one, Nat.cast_one] using (Nat.gcd_eq_gcd_ab p M).symm
  have hv : ¬ (p : ℤ) ∣ v := by
    intro hdiv
    have hone : (p : ℤ) ∣ 1 := by
      rw [← hbez]
      exact dvd_add (dvd_mul_right _ _) (dvd_mul_of_dvd_right hdiv _)
    exact hp.not_dvd_one (by exact_mod_cast hone)
  let σ : Matrix.SpecialLinearGroup (Fin 2) ℤ :=
    ⟨!![(p : ℤ), -v; (M : ℤ), u], by
      simpa only [Matrix.det_fin_two_of, neg_mul, sub_neg_eq_add, mul_comm v (M : ℤ)]
        using hbez⟩
  let β : Matrix.SpecialLinearGroup (Fin 2) ℤ :=
    ⟨!![(1 : ℤ), -v; (M : ℤ), (p : ℤ) * u], by
      simpa only [Matrix.det_fin_two_of, one_mul, neg_mul, sub_neg_eq_add,
        mul_comm v (M : ℤ)] using hbez⟩
  refine ⟨v, σ, β, hv, ?_, ?_, rfl, rfl, ?_⟩
  · rw [CongruenceSubgroup.Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact dvd_refl (M : ℤ)
  · rw [CongruenceSubgroup.Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact dvd_refl (M : ℤ)
  · apply Units.ext
    change (ModularForm.heckeMatrix p 0 : Matrix (Fin 2) (Fin 2) ℝ) *
        (Matrix.SpecialLinearGroup.mapGL ℝ σ : Matrix (Fin 2) (Fin 2) ℝ) =
      (Matrix.SpecialLinearGroup.mapGL ℝ β : Matrix (Fin 2) (Fin 2) ℝ) *
        (ModularForm.heckeDiagMatrix p : Matrix (Fin 2) (Fin 2) ℝ)
    rw [ModularForm.val_heckeMatrix hp.ne_zero, ModularForm.val_heckeDiagMatrix hp.ne_zero]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [σ, β, Matrix.mul_apply, Fin.sum_univ_two, Matrix.SpecialLinearGroup.mapGL,
        Matrix.SpecialLinearGroup.map_apply_coe, mul_comm]


namespace Submission

theorem f036cc6b1f_pc_hi_good_prime_transversal
    (M : ℕ) [NeZero M] (p : ℕ) (hp : p.Prime) (hpM : ¬ p ∣ M) :
    ∃ r : Fin (p + 1) → Matrix.SpecialLinearGroup (Fin 2) ℤ,
      (∀ i, r i ∈ CongruenceSubgroup.Gamma0 M) ∧
      (∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
        γ ∈ CongruenceSubgroup.Gamma0 M →
          ∃! i : Fin (p + 1), (p : ℤ) ∣ (γ * (r i)⁻¹) 0 1) ∧
      (∀ i : Fin p, ModularForm.heckeMatrix p 0 *
        Matrix.SpecialLinearGroup.mapGL ℝ (r i.castSucc) =
          ModularForm.heckeMatrix p i.val) ∧
      (∃ β : Matrix.SpecialLinearGroup (Fin 2) ℤ,
        β ∈ CongruenceSubgroup.Gamma0 M ∧
          ModularForm.heckeMatrix p 0 *
            Matrix.SpecialLinearGroup.mapGL ℝ (r (Fin.last p)) =
              Matrix.SpecialLinearGroup.mapGL ℝ β * ModularForm.heckeDiagMatrix p) := by
  obtain ⟨v, σ, β, hv, hσ, hβ, hσ00, hσ01, hσβ⟩ :=
    f036cc6b1f_pc_hi_gpt_bezout_lift M p hp hpM
  let t (j : ℕ) : Matrix.SpecialLinearGroup (Fin 2) ℤ :=
    ⟨!![1, (j : ℤ); 0, 1], by simp [Matrix.det_fin_two]⟩
  let r (i : Fin (p + 1)) : Matrix.SpecialLinearGroup (Fin 2) ℤ :=
    if i.val < p then t i.val else σ
  have hentry (γ δ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
      (γ * δ⁻¹) 0 1 = -(γ 0 0) * δ 0 1 + γ 0 1 * δ 0 0 := by
    change ((γ : Matrix (Fin 2) (Fin 2) ℤ) *
      ((δ⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ)) 0 1 = _
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hrentry (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (i : Fin (p + 1)) :
      (γ * (r i)⁻¹) 0 1 =
        if i.val < p then γ 0 1 - γ 0 0 * (i.val : ℤ)
          else γ 0 0 * v + γ 0 1 * (p : ℤ) := by
    rw [hentry]
    by_cases hi : i.val < p
    · simp [r, hi, t, sub_eq_add_neg, add_comm]
    · simp [r, hi, hσ00, hσ01]
  refine ⟨r, ?_, ?_, ?_, ?_⟩
  · intro i
    dsimp [r]
    split_ifs with hi
    · simp [CongruenceSubgroup.Gamma0_mem, t]
    · exact hσ
  · intro γ _hγ
    have hrow : ¬ (p : ℤ) ∣ γ 0 0 ∨ ¬ (p : ℤ) ∣ γ 0 1 := by
      by_contra! h
      have hdet : (p : ℤ) ∣ 1 := by
        rw [← γ.det_coe, Matrix.det_fin_two]
        exact dvd_sub (dvd_mul_of_dvd_left h.1 _) (dvd_mul_of_dvd_left h.2 _)
      exact hp.not_dvd_one (by exact_mod_cast hdet)
    simpa only [hrentry] using
      (f036cc6b1f_pc_hi_gpt_unique_projective_index p hp (γ 0 0) (γ 0 1) v hrow hv)
  · intro i
    have hri : r i.castSucc = t i.val := by simp [r, i.isLt]
    rw [hri]
    apply Matrix.GeneralLinearGroup.ext
    intro a b
    fin_cases a <;> fin_cases b <;>
      simp [Units.val_mul, ModularForm.val_heckeMatrix hp.ne_zero,
        Matrix.SpecialLinearGroup.mapGL_coe_matrix, t, Matrix.mul_apply,
        Fin.sum_univ_two, Matrix.SpecialLinearGroup.map_apply_coe]
  · refine ⟨β, hβ, ?_⟩
    simpa [r] using hσβ

end Submission


theorem Submission.f036cc6b1f_pc_hi_effective_domain_lift :
    ∀ (Γ Δ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
      (R : Finset (Matrix.SpecialLinearGroup (Fin 2) ℤ)) (F : Set UpperHalfPlane),
      Δ ≤ Γ → (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) ∈ Δ →
      (∀ r ∈ R, r ∈ Γ) →
      (∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, γ ∈ Γ → ∃ r ∈ R, γ * r⁻¹ ∈ Δ) →
      (∀ r ∈ R, ∀ s ∈ R, s * r⁻¹ ∈ Δ → s = r) → MeasurableSet F →
      (∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane),
        ∃ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, γ ∈ Γ ∧ γ • z ∈ F ∧
          ∀ δ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
            δ ∈ Γ → δ • z ∈ F → δ = γ ∨ δ = -γ) →
      let E : Set UpperHalfPlane := ⋃ r ∈ R, (fun z : UpperHalfPlane => r • z) '' F
      MeasurableSet E ∧
        (∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane),
          ∃ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, γ ∈ Δ ∧ γ • z ∈ E ∧
            ∀ δ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
              δ ∈ Δ → δ • z ∈ E → δ = γ ∨ δ = -γ) ∧
        (∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane),
          ∀ r ∈ R, ∀ s ∈ R,
            z ∈ (fun w : UpperHalfPlane => r • w) '' F →
            z ∈ (fun w : UpperHalfPlane => s • w) '' F → r = s) := by
  classical
  intro Γ Δ R F hΔ hneg hR hcover htrans hF hgood
  dsimp only
  have himage (r : Matrix.SpecialLinearGroup (Fin 2) ℤ) (z : UpperHalfPlane) :
      z ∈ (fun w : UpperHalfPlane => r • w) '' F ↔ r⁻¹ • z ∈ F := by
    constructor
    · rintro ⟨w, hw, rfl⟩
      simpa only [inv_smul_smul] using hw
    · intro hz
      exact ⟨r⁻¹ • z, hz, smul_inv_smul r z⟩
  refine ⟨R.measurableSet_biUnion (fun r _ => ?_), ?_, ?_⟩
  · have heq : (fun w : UpperHalfPlane => r • w) '' F =
        (fun z : UpperHalfPlane => r⁻¹ • z) ⁻¹' F := Set.ext (himage r)
    rw [heq]
    apply hF.preimage
    change Measurable (fun z : UpperHalfPlane =>
      ((r⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
        Matrix.GeneralLinearGroup (Fin 2) ℝ) • z)
    exact (continuous_const_smul _).measurable
  · filter_upwards [hgood] with z hz
    obtain ⟨η, hη, hηF, hηuniq⟩ := hz
    have hpair (a b : Matrix.SpecialLinearGroup (Fin 2) ℤ)
        (ha : a ∈ Γ) (hb : b ∈ Γ) (haF : a • z ∈ F) (hbF : b • z ∈ F) :
        b = a ∨ b = -a := by
      rcases hηuniq a ha haF with haη | haη <;>
        rcases hηuniq b hb hbF with hbη | hbη <;> simp [haη, hbη]
    obtain ⟨r, hr, hh⟩ := hcover η⁻¹ (Γ.inv_mem hη)
    have hγ : (η⁻¹ * r⁻¹)⁻¹ ∈ Δ := Δ.inv_mem hh
    have hγE : (η⁻¹ * r⁻¹)⁻¹ • z ∈
        ⋃ t ∈ R, (fun w : UpperHalfPlane => t • w) '' F := by
      apply Set.mem_iUnion_of_mem r
      apply Set.mem_iUnion_of_mem hr
      exact ⟨η • z, hηF, by simp [mul_smul]⟩
    refine ⟨(η⁻¹ * r⁻¹)⁻¹, hγ, hγE, ?_⟩
    intro δ hδ hδE
    obtain ⟨s, hs, hsF⟩ := Set.mem_iUnion₂.mp hδE
    have hrF : (r⁻¹ * (η⁻¹ * r⁻¹)⁻¹) • z ∈ F := by
      simpa only [mul_inv_rev, inv_inv, inv_mul_cancel_left] using hηF
    have hsF' : (s⁻¹ * δ) • z ∈ F := by
      simpa only [mul_smul] using (himage s (δ • z)).mp hsF
    have hsign := hpair (r⁻¹ * (η⁻¹ * r⁻¹)⁻¹) (s⁻¹ * δ)
      (Γ.mul_mem (Γ.inv_mem (hR r hr)) (hΔ hγ))
      (Γ.mul_mem (Γ.inv_mem (hR s hs)) (hΔ hδ)) hrF hsF'
    have hδeq : δ = s * r⁻¹ * (η⁻¹ * r⁻¹)⁻¹ ∨
        δ = -(s * r⁻¹ * (η⁻¹ * r⁻¹)⁻¹) := by
      rcases hsign with heq | heq
      · left
        simpa only [mul_assoc, mul_inv_cancel_left] using congrArg (fun a => s * a) heq
      · right
        simpa only [mul_neg, mul_assoc, mul_inv_cancel_left] using
          congrArg (fun a => s * a) heq
    have hsr : s * r⁻¹ ∈ Δ := by
      rcases hδeq with heq | heq
      · have hm := Δ.mul_mem hδ (Δ.inv_mem hγ)
        simpa [heq, mul_assoc] using hm
      · have hnδ : -δ ∈ Δ := by
          simpa only [neg_one_mul] using Δ.mul_mem hneg hδ
        have hm := Δ.mul_mem hnδ (Δ.inv_mem hγ)
        simpa [heq, mul_assoc] using hm
    have hsr_eq := htrans r hr s hs hsr
    subst s
    simpa only [mul_inv_cancel, one_mul] using hδeq
  · filter_upwards [hgood] with z hz
    obtain ⟨η, hη, hηF, hηuniq⟩ := hz
    intro r hr s hs hrF hsF
    have hrF' := (himage r z).mp hrF
    have hsF' := (himage s z).mp hsF
    have hsign : s⁻¹ = r⁻¹ ∨ s⁻¹ = -r⁻¹ := by
      rcases hηuniq r⁻¹ (Γ.inv_mem (hR r hr)) hrF' with heqr | heqr <;>
        rcases hηuniq s⁻¹ (Γ.inv_mem (hR s hs)) hsF' with heqs | heqs <;>
        simp [heqr, heqs]
    have hsr : s * r⁻¹ ∈ Δ := by
      rcases hsign with heq | heq
      · have hmul : s * r⁻¹ = 1 := by rw [← heq, mul_inv_cancel]
        rw [hmul]
        exact Δ.one_mem
      · have hmul : s * r⁻¹ = -1 := by
          have h := congrArg (fun a => s * a) heq
          simp only [mul_inv_cancel, mul_neg] at h
          simpa only [neg_neg] using (congrArg Neg.neg h).symm
        rw [hmul]
        exact hneg
    exact (htrans r hr s hs hsr).symm


theorem Submission.f036cc6b1f_pc_hi_finite_trace_unfolding
    (Γ Δ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
    (R : Finset (Matrix.SpecialLinearGroup (Fin 2) ℤ)) (F : Set UpperHalfPlane)
    (hΔΓ : Δ ≤ Γ) (hneg : (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) ∈ Δ)
    (hR : ∀ r ∈ R, r ∈ Γ)
    (hcover : ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, γ ∈ Γ →
      ∃ r ∈ R, γ * r⁻¹ ∈ Δ)
    (huniq : ∀ r ∈ R, ∀ s ∈ R, s * r⁻¹ ∈ Δ → s = r)
    (hF : MeasurableSet F)
    (hdom : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane),
      ∃ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
        γ ∈ Γ ∧ γ • z ∈ F ∧ ∀ δ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
          δ ∈ Γ → δ • z ∈ F → δ = γ ∨ δ = -γ)
    (u v : UpperHalfPlane → ℂ)
    (hv : ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, γ ∈ Γ →
      SlashAction.map (2 : ℤ) γ v = v) :
    let E : Set UpperHalfPlane := ⋃ r ∈ R, (fun z : UpperHalfPlane => r • z) '' F
    MeasureTheory.IntegrableOn (UpperHalfPlane.petersson 2 u v) E (MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane) →
      (∀ r ∈ R, MeasureTheory.IntegrableOn
        (UpperHalfPlane.petersson 2 (SlashAction.map (2 : ℤ) r u) v)
        F (MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane)) ∧
      MeasureTheory.integral ((MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane).restrict F)
          (UpperHalfPlane.petersson 2 (R.sum (fun r => SlashAction.map (2 : ℤ) r u)) v) =
        MeasureTheory.integral ((MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane).restrict E)
          (UpperHalfPlane.petersson 2 u v) := by
  classical
  intro E hInt
  have hLift := f036cc6b1f_pc_hi_effective_domain_lift
    Γ Δ R F hΔΓ hneg hR hcover huniq hF hdom
  have hEmb (r : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
      MeasurableEmbedding (fun z : UpperHalfPlane => r • z) :=
    (Homeomorph.smul (Matrix.SpecialLinearGroup.mapGL ℝ r)).measurableEmbedding
  have hPres (r : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
      MeasureTheory.MeasurePreserving (fun z : UpperHalfPlane => r • z) MeasureTheory.volume MeasureTheory.volume :=
    MeasureTheory.measurePreserving_smul (Matrix.SpecialLinearGroup.mapGL ℝ r) MeasureTheory.volume
  have hMeas (r : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
      MeasurableSet ((fun z : UpperHalfPlane => r • z) '' F) :=
    (hEmb r).measurableSet_image.mpr hF
  have hPiece (r : Matrix.SpecialLinearGroup (Fin 2) ℤ) (hr : r ∈ R) :
      MeasureTheory.IntegrableOn (UpperHalfPlane.petersson 2 u v)
        ((fun z : UpperHalfPlane => r • z) '' F) MeasureTheory.volume := by
    apply hInt.mono_set
    intro z hz
    exact Set.mem_iUnion.mpr ⟨r, Set.mem_iUnion.mpr ⟨hr, hz⟩⟩
  have hCov (r : Matrix.SpecialLinearGroup (Fin 2) ℤ) (hr : r ∈ R) :
      UpperHalfPlane.petersson 2 (SlashAction.map (2 : ℤ) r u) v =
        fun z => UpperHalfPlane.petersson 2 u v (r • z) := by
    funext z
    simpa only [hv r (hR r hr)] using UpperHalfPlane.petersson_slash_SL 2 u v r z
  have hTerm (r : Matrix.SpecialLinearGroup (Fin 2) ℤ) (hr : r ∈ R) :
      MeasureTheory.IntegrableOn (UpperHalfPlane.petersson 2 (SlashAction.map (2 : ℤ) r u) v)
        F MeasureTheory.volume := by
    rw [hCov r hr]
    exact ((hPres r).restrict_image_emb (hEmb r) F).integrable_comp_of_integrable
      (hPiece r hr)
  have hIntegral (r : Matrix.SpecialLinearGroup (Fin 2) ℤ) (hr : r ∈ R) :
      MeasureTheory.integral (MeasureTheory.volume.restrict F)
        (UpperHalfPlane.petersson 2 (SlashAction.map (2 : ℤ) r u) v) =
        MeasureTheory.integral
          (MeasureTheory.volume.restrict ((fun w : UpperHalfPlane => r • w) '' F))
          (UpperHalfPlane.petersson 2 u v) := by
    rw [hCov r hr]
    exact ((hPres r).setIntegral_image_emb (hEmb r) (UpperHalfPlane.petersson 2 u v) F).symm
  refine ⟨hTerm, ?_⟩
  have hSum :
      UpperHalfPlane.petersson 2 (R.sum (fun r => SlashAction.map (2 : ℤ) r u)) v =
        fun z => ∑ r ∈ R, UpperHalfPlane.petersson 2 (SlashAction.map (2 : ℤ) r u) v z := by
    funext z
    simp only [UpperHalfPlane.petersson, Finset.sum_apply, map_sum, Finset.sum_mul]
  have hUnion : (⋃ r : ↥R, (fun z : UpperHalfPlane => (r : Matrix.SpecialLinearGroup (Fin 2) ℤ) • z) '' F) = E := by
    simp only [E, Set.iUnion_subtype]
  have hDisj : Pairwise (fun r s : ↥R => MeasureTheory.AEDisjoint (MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane)
      ((fun z : UpperHalfPlane => (r : Matrix.SpecialLinearGroup (Fin 2) ℤ) • z) '' F)
      ((fun z : UpperHalfPlane => (s : Matrix.SpecialLinearGroup (Fin 2) ℤ) • z) '' F)) := by
    intro r s hrs
    apply MeasureTheory.measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hLift.2.2] with z hz
    intro hzs
    exact hrs (Subtype.ext (hz r r.property s s.property hzs.1 hzs.2))
  have hUnfold := MeasureTheory.integral_iUnion_ae (fun r : ↥R => (hMeas r).nullMeasurableSet)
    hDisj (hUnion.symm ▸ hInt)
  rw [hSum, MeasureTheory.integral_finsetSum R (fun r hr => hTerm r hr)]
  trans ∑ r ∈ R, MeasureTheory.integral
    (MeasureTheory.volume.restrict ((fun w : UpperHalfPlane => r • w) '' F))
    (UpperHalfPlane.petersson 2 u v)
  · exact Finset.sum_congr rfl hIntegral
  · rw [← Finset.sum_coe_sort R (fun r =>
      MeasureTheory.integral (MeasureTheory.volume.restrict ((fun w : UpperHalfPlane => r • w) '' F))
        (UpperHalfPlane.petersson 2 u v))]
    simpa only [hUnion, tsum_fintype] using hUnfold.symm

namespace Submission

open UpperHalfPlane MeasureTheory Matrix.SpecialLinearGroup
open scoped MatrixGroups ModularForm Pointwise

/-- The Petersson integrand of two weight-two cusp forms is integrable on each
integral translate of the standard modular fundamental domain. -/
theorem f036cc6b1f_pic_translated_integrable
    (Δ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Δ.FiniteIndex]
    (r : Matrix.SpecialLinearGroup (Fin 2) ℤ) (f g : CuspForm Δ 2) :
    MeasureTheory.IntegrableOn (UpperHalfPlane.petersson 2 f g)
      ((fun z : UpperHalfPlane => r • z) '' ModularGroup.fd)
      (MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane) := by
  -- Translation preserves the arithmetic cusp conditions.
  have : (ConjAct.toConjAct (r : GL (Fin 2) ℝ)⁻¹ •
      (Δ : Subgroup (GL (Fin 2) ℝ))).IsArithmetic := by
    simpa [(show Rat.castHom ℝ = algebraMap ℚ ℝ by rfl), map_inv, map_mapGL]
      using! Subgroup.IsArithmetic.conj (Δ : Subgroup (GL (Fin 2) ℝ)) (mapGL ℚ r)⁻¹
  let u := CuspForm.translate f r
  let v := CuspForm.translate g r
  obtain ⟨a, ha, hu⟩ := CuspFormClass.exp_decay_atImInfty' u
  obtain ⟨b, hb, hv⟩ := CuspFormClass.exp_decay_atImInfty' v
  have huv : (fun z : UpperHalfPlane => u z * v z)
      =O[atImInfty] (fun z => Real.exp (-(a + b) * z.im)) := by
    apply (hu.mul hv).congr_right
    intro z
    rw [← Real.exp_add]
    congr 1
    ring
  obtain ⟨C, hC, hbound⟩ := huv.exists_pos
  obtain ⟨Y, hY⟩ := (atImInfty_mem _).mp hbound.bound
  have hint : IntegrableOn (petersson 2 u v) ModularGroup.fd
      (volume : Measure UpperHalfPlane) := by
    apply f036cc6b1f_tdi_petersson_integrable_of_exp_product_bound
      u v (a + b) C Y (ModularFormClass.continuous u) (ModularFormClass.continuous v)
      (add_pos ha hb) hC.le
    intro z hz
    simpa only [Set.mem_ofPred_eq, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hY z hz
  -- The SL₂ action preserves hyperbolic volume, and Petersson covariance
  -- identifies the pullback with the integrand of the translated forms.
  have hpres : MeasurePreserving (fun z : UpperHalfPlane => r • z)
      (volume : Measure UpperHalfPlane) volume :=
    measurePreserving_smul (r : GL (Fin 2) ℝ) volume
  have hemb : MeasurableEmbedding (fun z : UpperHalfPlane => r • z) :=
    measurableEmbedding_const_smul (r : GL (Fin 2) ℝ)
  apply (hpres.integrableOn_image hemb).mpr
  convert hint using 1
  ext z
  exact (petersson_slash_SL 2 f g r z).symm

end Submission
theorem Submission.f036cc6b1f_pic_mec_invariant_conull_core :
    ∀ (Δ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) (S : Set UpperHalfPlane),
      MeasurableSet S →
      (∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane), z ∈ S) →
      ∃ X : Set UpperHalfPlane, MeasurableSet X ∧
        (∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane), z ∈ X) ∧
        X ⊆ S ∧ (∀ (γ : Δ) (z : UpperHalfPlane),
          (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) • z ∈ X ↔ z ∈ X) := by
  intro Δ S hS hSae
  have : Countable (Matrix.SpecialLinearGroup (Fin 2) ℤ) :=
    Function.Injective.countable (β := Fin 2 → Fin 2 → ℤ)
      (f := fun g : Matrix.SpecialLinearGroup (Fin 2) ℤ => (g.1 : Fin 2 → Fin 2 → ℤ))
      Subtype.val_injective
  have hpres (γ : Δ) : MeasureTheory.MeasurePreserving
      (fun z : UpperHalfPlane => (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) • z)
      MeasureTheory.volume MeasureTheory.volume := by
    change MeasureTheory.MeasurePreserving
      (fun z : UpperHalfPlane =>
        Matrix.SpecialLinearGroup.mapGL ℝ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) • z)
      MeasureTheory.volume MeasureTheory.volume
    exact MeasureTheory.measurePreserving_smul _ _
  let X : Set UpperHalfPlane :=
    ⋂ γ : Δ, (fun z : UpperHalfPlane =>
      (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) • z) ⁻¹' S
  have hstable (γ : Δ) (z : UpperHalfPlane) (hz : z ∈ X) :
      (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) • z ∈ X := by
    refine Set.mem_iInter.mpr fun δ => ?_
    have h := Set.mem_iInter.mp hz (δ * γ)
    simpa only [Set.mem_preimage, Subgroup.coe_mul, mul_smul] using h
  refine ⟨X, MeasurableSet.iInter (fun γ => hS.preimage (hpres γ).measurable),
    ?_, ?_, ?_⟩
  · exact (MeasureTheory.ae_all_iff.mpr fun γ =>
      (hpres γ).quasiMeasurePreserving.ae hSae).mono fun z hz => Set.mem_iInter.mpr hz
  · intro z hz
    have h := Set.mem_iInter.mp hz (1 : Δ)
    simpa only [Set.mem_preimage, Subgroup.coe_one, one_smul] using h
  · intro γ z
    constructor
    · intro hz
      simpa only [Subgroup.coe_inv, inv_smul_smul] using
        hstable γ⁻¹ ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) • z) hz
    · exact hstable γ z
theorem Submission.f036cc6b1f_pic_psp_sign_transversal :
    ∀ (Δ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)),
      (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) ∈ Δ →
      ∃ L : Set Δ,
        (∀ δ : Δ, ∃ γ : Δ, γ ∈ L ∧
          ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) =
              (δ : Matrix.SpecialLinearGroup (Fin 2) ℤ) ∨
            (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) =
              -(δ : Matrix.SpecialLinearGroup (Fin 2) ℤ))) ∧
        (∀ γ : Δ, γ ∈ L → ∀ η : Δ, η ∈ L →
          ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) =
              (η : Matrix.SpecialLinearGroup (Fin 2) ℤ) ∨
            (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) =
              -(η : Matrix.SpecialLinearGroup (Fin 2) ℤ)) → γ = η) := by
  classical
  intro Δ _hΔ
  let s : Setoid Δ :=
    { r := fun γ η =>
        (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) =
            (η : Matrix.SpecialLinearGroup (Fin 2) ℤ) ∨
          (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) =
            -(η : Matrix.SpecialLinearGroup (Fin 2) ℤ)
      iseqv := ⟨fun _ => Or.inl rfl, by
        intro γ η h
        rcases h with h | h
        · exact Or.inl h.symm
        · exact Or.inr (by rw [h, neg_neg]), by
        intro γ η ξ hγη hηξ
        rcases hγη with hγη | hγη <;> rcases hηξ with hηξ | hηξ
        · exact Or.inl (hγη.trans hηξ)
        · exact Or.inr (hγη.trans hηξ)
        · exact Or.inr (by rw [hγη, hηξ])
        · exact Or.inl (by rw [hγη, hηξ, neg_neg])⟩ }
  refine ⟨Set.range (Quotient.out (s := s)), ?_, ?_⟩
  · intro δ
    refine ⟨(Quotient.mk s δ).out, ⟨Quotient.mk s δ, rfl⟩, ?_⟩
    exact Quotient.exact (Quotient.out_eq (Quotient.mk s δ))
  · rintro γ ⟨c, rfl⟩ η ⟨d, rfl⟩ h
    have heq : Quotient.mk s c.out = Quotient.mk s d.out := Quotient.sound h
    have hcd : c = d := by simpa only [Quotient.out_eq] using heq
    exact congrArg (Quotient.out (s := s)) hcd
theorem Submission.f036cc6b1f_pic_psp_measurable_slice_partition :
    ∀ (Δ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) (L : Set Δ) (P S X : Set UpperHalfPlane), MeasurableSet P → MeasurableSet S → MeasurableSet X → (∀ δ : Δ, ∃ γ : Δ, γ ∈ L ∧ ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (δ : Matrix.SpecialLinearGroup (Fin 2) ℤ) ∨ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) = -(δ : Matrix.SpecialLinearGroup (Fin 2) ℤ))) → (∀ γ : Δ, γ ∈ L → ∀ η : Δ, η ∈ L → ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (η : Matrix.SpecialLinearGroup (Fin 2) ℤ) ∨ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) = -(η : Matrix.SpecialLinearGroup (Fin 2) ℤ)) → γ = η) → (∀ z ∈ X, ∃ r : Matrix.SpecialLinearGroup (Fin 2) ℤ, r ∈ Δ ∧ r • z ∈ S ∧ ∀ δ : Matrix.SpecialLinearGroup (Fin 2) ℤ, δ ∈ Δ → δ • z ∈ S → δ = r ∨ δ = -r) → let C : Δ → Set UpperHalfPlane := fun γ => {z | γ ∈ L ∧ z ∈ P ∩ X ∧ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) • z ∈ S}; (∀ γ, MeasurableSet (C γ)) ∧ Pairwise (fun γ η => Disjoint (C γ) (C η)) ∧ (⋃ γ, C γ) = P ∩ X := by
  intro Δ L P S X hP hS hX hcover huniq horbit
  dsimp only
  constructor
  · intro γ
    by_cases hγ : γ ∈ L
    · have hcont : Continuous (fun z : UpperHalfPlane =>
          (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) • z) := by
        change Continuous (fun z : UpperHalfPlane =>
          Matrix.SpecialLinearGroup.mapGL ℝ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) • z)
        exact continuous_const_smul _
      simpa only [hγ, true_and, Set.inter_def, Set.preimage, Set.mem_ofPred_eq] using
        (hP.inter hX).inter (hS.preimage hcont.measurable)
    · simpa only [hγ, false_and, Set.ofPred_false] using
        (MeasurableSet.empty : MeasurableSet (∅ : Set UpperHalfPlane))
  · constructor
    · intro γ η hne
      apply Set.disjoint_left.mpr
      intro z hzγ hzη
      obtain ⟨r, _, _, hr⟩ := horbit z hzγ.2.1.2
      apply hne
      apply huniq γ hzγ.1 η hzη.1
      rcases hr (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) γ.property hzγ.2.2 with hg | hg <;>
        rcases hr (η : Matrix.SpecialLinearGroup (Fin 2) ℤ) η.property hzη.2.2 with he | he
      · exact Or.inl (hg.trans he.symm)
      · exact Or.inr (by rw [hg, he, neg_neg])
      · exact Or.inr (by rw [hg, he])
      · exact Or.inl (hg.trans he.symm)
    · apply Set.Subset.antisymm
      · intro z hz
        obtain ⟨γ, hγ⟩ := Set.mem_iUnion.mp hz
        exact hγ.2.1
      · intro z hz
        obtain ⟨r, hr, hrs, _⟩ := horbit z hz.2
        obtain ⟨γ, hγ, hsgn⟩ := hcover ⟨r, hr⟩
        apply Set.mem_iUnion.mpr
        refine ⟨γ, hγ, hz, ?_⟩
        rcases hsgn with hsgn | hsgn
        · simpa only [hsgn] using hrs
        · simpa only [hsgn, ModularGroup.SL_neg_smul] using hrs

namespace Submission

theorem f036cc6b1f_pic_mec_pointwise_sign_partition
    (Δ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) (E F X : Set UpperHalfPlane)
    (hneg : (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) ∈ Δ)
    (hE : MeasurableSet E) (hF : MeasurableSet F) (hX : MeasurableSet X)
    (hinv : ∀ (γ : Δ) (z : UpperHalfPlane),
      (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) • z ∈ X ↔ z ∈ X)
    (hrep : ∀ S : Set UpperHalfPlane, (S = E ∨ S = F) → ∀ z ∈ X,
      ∃ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, γ ∈ Δ ∧ γ • z ∈ S ∧
        ∀ δ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
          δ ∈ Δ → δ • z ∈ S → δ = γ ∨ δ = -γ) :
    ∃ A B : Δ → Set UpperHalfPlane,
      (∀ γ, MeasurableSet (A γ)) ∧ (∀ γ, MeasurableSet (B γ)) ∧
      Pairwise (fun γ δ => Disjoint (A γ) (A δ)) ∧
      Pairwise (fun γ δ => Disjoint (B γ) (B δ)) ∧
      (⋃ γ, A γ) = E ∩ X ∧ (⋃ γ, B γ) = F ∩ X ∧
      (∀ γ : Δ, (fun z : UpperHalfPlane =>
        (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ)⁻¹ • z) '' (A γ) = B γ) := by
  classical
  obtain ⟨L, hcover, hunique⟩ := f036cc6b1f_pic_psp_sign_transversal Δ hneg
  -- Inversion carries a sign transversal to a sign transversal.
  let Linv : Set Δ := {γ | γ⁻¹ ∈ L}
  have hcoverInv : ∀ δ : Δ, ∃ γ : Δ, γ ∈ Linv ∧
      ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) = δ ∨
        (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) = -(δ : Matrix.SpecialLinearGroup (Fin 2) ℤ)) := by
    intro δ
    obtain ⟨γ, hγ, hsign⟩ := hcover δ⁻¹
    refine ⟨γ⁻¹, ?_, ?_⟩
    · simpa only [Linv, Set.mem_ofPred_eq, inv_inv] using hγ
    · rcases hsign with hsign | hsign
      · left
        simpa only [Subgroup.coe_inv, inv_inv] using congrArg Inv.inv hsign
      · right
        simpa only [Subgroup.coe_inv, inv_neg, inv_inv] using congrArg Inv.inv hsign
  have huniqueInv : ∀ γ : Δ, γ ∈ Linv → ∀ η : Δ, η ∈ Linv →
      ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) = η ∨
        (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) = -(η : Matrix.SpecialLinearGroup (Fin 2) ℤ)) →
      γ = η := by
    intro γ hγ η hη hsign
    apply inv_injective
    apply hunique γ⁻¹ hγ η⁻¹ hη
    rcases hsign with hsign | hsign
    · left
      simpa only [Subgroup.coe_inv] using congrArg Inv.inv hsign
    · right
      simpa only [Subgroup.coe_inv, inv_neg] using congrArg Inv.inv hsign
  let C : Δ → Set UpperHalfPlane := fun γ =>
    {z | γ ∈ Linv ∧ z ∈ E ∩ X ∧ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) • z ∈ F}
  let A : Δ → Set UpperHalfPlane := fun γ => C γ⁻¹
  let B : Δ → Set UpperHalfPlane := fun γ =>
    {z | γ ∈ L ∧ z ∈ F ∩ X ∧ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) • z ∈ E}
  obtain ⟨hCmeas, hCdisj, hCunion⟩ :=
    f036cc6b1f_pic_psp_measurable_slice_partition Δ Linv E F X hE hF hX
      hcoverInv huniqueInv (hrep F (Or.inr rfl))
  obtain ⟨hBmeas, hBdisj, hBunion⟩ :=
    f036cc6b1f_pic_psp_measurable_slice_partition Δ L F E X hF hE hX
      hcover hunique (hrep E (Or.inl rfl))
  refine ⟨A, B, (fun γ => hCmeas γ⁻¹), hBmeas, ?_, hBdisj, ?_, hBunion, ?_⟩
  · intro γ η hne
    exact hCdisj (fun h => hne (inv_injective h))
  · calc
      (⋃ γ, A γ) = ⋃ γ, C γ :=
        Set.iUnion_congr_of_surjective Inv.inv inv_surjective (fun _ => rfl)
      _ = E ∩ X := hCunion
  · intro γ
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      change (γ⁻¹)⁻¹ ∈ L ∧ z ∈ E ∩ X ∧
        ((γ⁻¹ : Δ) : Matrix.SpecialLinearGroup (Fin 2) ℤ) • z ∈ F at hz
      simp only [inv_inv, Subgroup.coe_inv] at hz
      refine ⟨hz.1, ⟨hz.2.2, (hinv γ⁻¹ z).2 hz.2.1.2⟩, ?_⟩
      simpa only [smul_inv_smul] using hz.2.1.1
    · intro hy
      change γ ∈ L ∧ y ∈ F ∩ X ∧
        (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) • y ∈ E at hy
      refine ⟨(γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) • y, ?_, inv_smul_smul _ _⟩
      change (γ⁻¹)⁻¹ ∈ L ∧
        (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) • y ∈ E ∩ X ∧
        ((γ⁻¹ : Δ) : Matrix.SpecialLinearGroup (Fin 2) ℤ) •
          ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) • y) ∈ F
      simp only [inv_inv, Subgroup.coe_inv, inv_smul_smul]
      exact ⟨hy.1, ⟨hy.2.2, (hinv γ y).2 hy.2.1.2⟩, hy.2.1.1⟩

end Submission


namespace Submission

/-- Measurable equidecomposition of two domains with representatives unique up to sign. -/
theorem f036cc6b1f_pic_dt_measurable_equidecomposition
    (Δ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) (E F : Set UpperHalfPlane)
    (hneg : (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) ∈ Δ)
    (hE : MeasurableSet E) (hF : MeasurableSet F)
    (hEae : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane),
      ∃ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
        γ ∈ Δ ∧ γ • z ∈ E ∧ ∀ δ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
          δ ∈ Δ → δ • z ∈ E → δ = γ ∨ δ = -γ)
    (hFae : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane),
      ∃ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
        γ ∈ Δ ∧ γ • z ∈ F ∧ ∀ δ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
          δ ∈ Δ → δ • z ∈ F → δ = γ ∨ δ = -γ) :
    ∃ A B : Δ → Set UpperHalfPlane,
      (∀ γ, MeasurableSet (A γ)) ∧ (∀ γ, MeasurableSet (B γ)) ∧
      Pairwise (fun γ δ => Disjoint (A γ) (A δ)) ∧
      Pairwise (fun γ δ => Disjoint (B γ) (B δ)) ∧
      (∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane),
        z ∈ E ↔ z ∈ ⋃ γ, A γ) ∧
      (∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane),
        z ∈ F ↔ z ∈ ⋃ γ, B γ) ∧
      (∀ γ : Δ,
        (fun z : UpperHalfPlane => (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ)⁻¹ • z) ''
          A γ = B γ) := by
  classical
  -- The representative predicates are measurable by countability of the matrix group.
  have : Countable (Matrix.SpecialLinearGroup (Fin 2) ℤ) := by
    change Countable {g : Fin 2 → Fin 2 → ℤ // Matrix.det g = 1}
    infer_instance
  have hsmul (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
      Measurable (fun z : UpperHalfPlane => γ • z) :=
    (continuous_const_smul (Matrix.SpecialLinearGroup.mapGL ℝ γ)).measurable
  let R : Set UpperHalfPlane → Set UpperHalfPlane := fun S =>
    {z | ∃ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      γ ∈ Δ ∧ γ • z ∈ S ∧ ∀ δ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
        δ ∈ Δ → δ • z ∈ S → δ = γ ∨ δ = -γ}
  have hR (S : Set UpperHalfPlane) (hS : MeasurableSet S) : MeasurableSet (R S) := by
    dsimp only [R]
    rw [Set.ofPred_exists]
    refine MeasurableSet.iUnion fun γ => ?_
    refine (MeasurableSet.const (γ ∈ Δ)).inter ((hS.preimage (hsmul γ)).inter ?_)
    change MeasurableSet {z : UpperHalfPlane |
      ∀ δ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
        δ ∈ Δ → δ • z ∈ S → δ = γ ∨ δ = -γ}
    rw [Set.ofPred_forall]
    refine MeasurableSet.iInter fun δ => ?_
    exact (MeasurableSet.const (δ ∈ Δ)).imp
      ((hS.preimage (hsmul δ)).imp (MeasurableSet.const (δ = γ ∨ δ = -γ)))
  have hRae : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane),
      z ∈ R E ∩ R F := hEae.and hFae
  -- Restrict to the invariant conull core where both predicates hold pointwise.
  obtain ⟨X, hX, hXae, hXR, hXinv⟩ :=
    Submission.f036cc6b1f_pic_mec_invariant_conull_core Δ (R E ∩ R F)
      ((hR E hE).inter (hR F hF)) hRae
  obtain ⟨A, B, hA, hB, hAdisj, hBdisj, hAunion, hBunion, hAB⟩ :=
    Submission.f036cc6b1f_pic_mec_pointwise_sign_partition Δ E F X
      hneg hE hF hX hXinv (by
        rintro S (rfl | rfl) z hz
        · exact (hXR hz).1
        · exact (hXR hz).2)
  -- Conullness upgrades the exact covers of the intersections to almost-everywhere covers.
  refine ⟨A, B, hA, hB, hAdisj, hBdisj, ?_, ?_, hAB⟩
  · filter_upwards [hXae] with z hz
    rw [hAunion]
    exact ⟨fun h => ⟨h, hz⟩, fun h => h.1⟩
  · filter_upwards [hXae] with z hz
    rw [hBunion]
    exact ⟨fun h => ⟨h, hz⟩, fun h => h.1⟩

end Submission

theorem Submission.f036cc6b1f_pic_dt_integral_of_equidecomposition :
    ∀ (α ι : Type) [MeasurableSpace α] [Countable ι]
      (μ : MeasureTheory.Measure α) (E F : Set α) (A B : ι → Set α) (T : ι → α → α),
      MeasurableSet E → MeasurableSet F →
      (∀ i, MeasurableSet (A i)) → (∀ i, MeasurableSet (B i)) →
      Pairwise (fun i j => Disjoint (A i) (A j)) →
      Pairwise (fun i j => Disjoint (B i) (B j)) →
      (∀ᵐ x ∂μ, x ∈ E ↔ x ∈ ⋃ i, A i) →
      (∀ᵐ x ∂μ, x ∈ F ↔ x ∈ ⋃ i, B i) →
      (∀ i, MeasurableEmbedding (T i)) →
      (∀ i, MeasureTheory.MeasurePreserving (T i) μ μ) →
      (∀ i, T i '' A i = B i) → ∀ φ : α → ℂ,
      MeasureTheory.StronglyMeasurable φ →
      (∀ i, ∀ x ∈ A i, φ (T i x) = φ x) →
      MeasureTheory.IntegrableOn φ E μ →
      MeasureTheory.IntegrableOn φ F μ ∧ MeasureTheory.integral (μ.restrict E) φ = MeasureTheory.integral (μ.restrict F) φ := by
  intro α ι _ _ μ E F A B T _hE _hF hA hB hdA hdB hEU hFV hemb hpres himage
    φ hφ hinv hφE
  have hμE : μ.restrict E = μ.restrict (⋃ i, A i) :=
    MeasureTheory.Measure.restrict_congr_set (hEU.mono fun _ hx => propext hx)
  have hμF : μ.restrict F = μ.restrict (⋃ i, B i) :=
    MeasureTheory.Measure.restrict_congr_set (hFV.mono fun _ hx => propext hx)
  rw [MeasureTheory.IntegrableOn, hμE] at hφE
  change MeasureTheory.Integrable φ (μ.restrict F) ∧ _
  rw [hμE, hμF]
  have htransport : ∀ i, MeasureTheory.MeasurePreserving (T i) (μ.restrict (A i))
      (μ.restrict (B i)) := by
    intro i
    simpa only [himage i] using (hpres i).restrict_image_emb (hemb i) (A i)
  have hnorm : ∀ i,
      (∫⁻ x in A i, ENNReal.ofReal ‖φ x‖ ∂μ) =
        ∫⁻ x in B i, ENNReal.ofReal ‖φ x‖ ∂μ := by
    intro i
    calc
      (∫⁻ x in A i, ENNReal.ofReal ‖φ x‖ ∂μ) =
          ∫⁻ x in A i, ENNReal.ofReal ‖φ (T i x)‖ ∂μ :=
        MeasureTheory.setLIntegral_congr_fun (hA i) (fun x hx => by rw [hinv i x hx])
      _ = ∫⁻ x in B i, ENNReal.ofReal ‖φ x‖ ∂μ :=
        (htransport i).lintegral_comp_emb (hemb i) (fun x => ENNReal.ofReal ‖φ x‖)
  have hnormUnion :
      (∫⁻ x in ⋃ i, A i, ENNReal.ofReal ‖φ x‖ ∂μ) =
        ∫⁻ x in ⋃ i, B i, ENNReal.ofReal ‖φ x‖ ∂μ := by
    rw [MeasureTheory.lintegral_iUnion hA hdA, MeasureTheory.lintegral_iUnion hB hdB]
    exact tsum_congr hnorm
  have hφB : MeasureTheory.IntegrableOn φ (⋃ i, B i) μ := by
    refine ⟨hφ.aestronglyMeasurable, (MeasureTheory.hasFiniteIntegral_iff_norm φ).2 ?_⟩
    rw [← hnormUnion]
    exact (MeasureTheory.hasFiniteIntegral_iff_norm φ).1 hφE.2
  refine ⟨hφB, ?_⟩
  rw [MeasureTheory.integral_iUnion hA hdA hφE, MeasureTheory.integral_iUnion hB hdB hφB]
  apply tsum_congr
  intro i
  calc
    (∫ x in A i, φ x ∂μ) = ∫ x in A i, φ (T i x) ∂μ :=
      MeasureTheory.setIntegral_congr_fun (hA i) (fun x hx => (hinv i x hx).symm)
    _ = ∫ x in B i, φ x ∂μ := (htransport i).integral_comp (hemb i) φ


namespace Submission

/-- Transfer integrability and the integral between effective fundamental domains. -/
theorem f036cc6b1f_pic_domain_transfer
    (Δ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) (E F : Set UpperHalfPlane)
    (hneg : (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) ∈ Δ)
    (hE : MeasurableSet E) (hF : MeasurableSet F)
    (hrepE : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane),
      ∃ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
        γ ∈ Δ ∧ γ • z ∈ E ∧ ∀ δ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
          δ ∈ Δ → δ • z ∈ E → δ = γ ∨ δ = -γ)
    (hrepF : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane),
      ∃ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
        γ ∈ Δ ∧ γ • z ∈ F ∧ ∀ δ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
          δ ∈ Δ → δ • z ∈ F → δ = γ ∨ δ = -γ)
    (φ : UpperHalfPlane → ℂ) (hφ : Continuous φ)
    (hφinv : ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, γ ∈ Δ →
      ∀ z : UpperHalfPlane, φ (γ • z) = φ z)
    (hφE : MeasureTheory.IntegrableOn φ E
      (MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane)) :
    MeasureTheory.IntegrableOn φ F
        (MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane) ∧
      MeasureTheory.integral
          ((MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane).restrict E) φ =
        MeasureTheory.integral
          ((MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane).restrict F) φ := by
  have : Countable (Matrix.SpecialLinearGroup (Fin 2) ℤ) :=
    inferInstanceAs (Countable {A : Fin 2 → Fin 2 → ℤ // Matrix.det A = 1})
  obtain ⟨A, B, hA, hB, hdisjA, hdisjB, hcoverE, hcoverF, hAB⟩ :=
    f036cc6b1f_pic_dt_measurable_equidecomposition Δ E F hneg hE hF hrepE hrepF
  refine f036cc6b1f_pic_dt_integral_of_equidecomposition UpperHalfPlane Δ
    MeasureTheory.volume E F A B
    (fun γ z => (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ)⁻¹ • z)
    hE hF hA hB hdisjA hdisjB hcoverE hcoverF ?_ ?_ hAB φ
    hφ.stronglyMeasurable ?_ hφE
  · intro γ
    -- The special linear action is the canonical general linear action via `mapGL`.
    change MeasurableEmbedding (fun z : UpperHalfPlane =>
      Matrix.SpecialLinearGroup.mapGL ℝ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ)⁻¹ • z)
    exact measurableEmbedding_const_smul _
  · intro γ
    change MeasureTheory.MeasurePreserving (fun z : UpperHalfPlane =>
      Matrix.SpecialLinearGroup.mapGL ℝ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ)⁻¹ • z)
      MeasureTheory.volume MeasureTheory.volume
    exact MeasureTheory.measurePreserving_smul _ _
  · intro γ z _
    exact hφinv _ (Δ.inv_mem γ.property) z

end Submission
open MeasureTheory

namespace Submission

/-- The boundary of the standard modular domain is measurable and has hyperbolic volume zero. -/
open MeasureTheory

namespace Submission

/-- The boundary of the standard modular domain is measurable and has hyperbolic volume zero. -/
theorem f036cc6b1f_pc_ed_aoi_boundary_null :
    MeasurableSet (ModularGroup.fd \ ModularGroup.fdo) ∧
      (volume : Measure UpperHalfPlane) (ModularGroup.fd \ ModularGroup.fdo) = 0 := by
  refine ⟨ModularGroup.isClosed_fd.measurableSet.diff
    ModularGroup.isOpen_fdo.measurableSet, ?_⟩
  have hcircle : (volume : Measure (ℝ × ℝ)) {p | p.1 ^ 2 + p.2 ^ 2 = 1} = 0 := by
    apply Measure.measure_prod_null_of_ae_null (μ := (volume : Measure ℝ))
      (ν := (volume : Measure ℝ))
      (isClosed_eq (by fun_prop) continuous_const).measurableSet
    filter_upwards [] with x
    by_cases h : ∃ y : ℝ, x ^ 2 + y ^ 2 = 1
    · obtain ⟨y₀, hy₀⟩ := h
      apply measure_mono_null (t := {y₀, -y₀}) ?_
        ((Set.toFinite {y₀, -y₀}).measure_zero volume)
      intro y hy
      change x ^ 2 + y ^ 2 = 1 at hy
      have hfactor : (y - y₀) * (y + y₀) = 0 := by nlinarith
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rcases mul_eq_zero.mp hfactor with hpos | hneg
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
      rcases mul_eq_zero.mp hfactor with hpos | hneg
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    · have hempty : Prod.mk x ⁻¹' {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 = 1} = ∅ := by
        ext y
        simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        exact fun hy => h ⟨y, hy⟩
      simp [hempty]
  have hline (c : ℝ) : (volume : Measure (ℝ × ℝ)) {p | p.1 = c} = 0 := by
    have hset : {p : ℝ × ℝ | p.1 = c} = ({c} : Set ℝ) ×ˢ Set.univ := by
      ext p
      simp
    rw [hset, Measure.volume_eq_prod, Measure.prod_prod]
    simp
  have hplanar : (volume : Measure ℂ)
      {z | Complex.normSq z = 1 ∨ z.re = 1 / 2 ∨ z.re = -(1 / 2)} = 0 := by
    have hnull : (volume : Measure (ℝ × ℝ))
        ({p | p.1 ^ 2 + p.2 ^ 2 = 1} ∪ {p | p.1 = 1 / 2} ∪
          {p | p.1 = -(1 / 2)}) = 0 :=
      measure_union_null (measure_union_null hcircle (hline _)) (hline _)
    have hpre := Complex.volume_preserving_equiv_real_prod.measure_preimage_equiv
      ({p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 = 1} ∪ {p | p.1 = 1 / 2} ∪
        {p | p.1 = -(1 / 2)})
    rw [hnull] at hpre
    simpa only [Set.preimage_union, Set.preimage_ofPred_eq,
      Complex.measurableEquivRealProd_apply, Complex.normSq_apply, pow_two,
      Set.ofPred_or, Set.union_assoc] using hpre
  have himage : (volume : Measure ℂ)
      (UpperHalfPlane.coe '' (ModularGroup.fd \ ModularGroup.fdo)) = 0 := by
    apply measure_mono_null ?_ hplanar
    rintro z ⟨w, ⟨hw, hwo⟩, rfl⟩
    change 1 ≤ Complex.normSq (w : ℂ) ∧ |w.re| ≤ (1 : ℝ) / 2 at hw
    change ¬ (1 < Complex.normSq (w : ℂ) ∧ |w.re| < (1 : ℝ) / 2) at hwo
    change Complex.normSq (w : ℂ) = 1 ∨ w.re = 1 / 2 ∨ w.re = -(1 / 2)
    by_cases hc : Complex.normSq (w : ℂ) = 1
    · exact Or.inl hc
    · have hr : |w.re| = (1 : ℝ) / 2 := by
        by_contra hn
        exact hwo ⟨lt_of_le_of_ne hw.1 (Ne.symm hc), lt_of_le_of_ne hw.2 hn⟩
      rcases le_or_gt 0 w.re with hp | hn
      · exact Or.inr (Or.inl (by simpa [abs_of_nonneg hp] using hr))
      · exact Or.inr (Or.inr (by rw [abs_of_neg hn] at hr; linarith))
  rw [UpperHalfPlane.volume_eq_lintegral, Measure.restrict_eq_zero.mpr himage]
  simp

end Submission

namespace Submission

/-- Almost every point has a modular orbit disjoint from a prescribed measurable null set. -/
theorem f036cc6b1f_pc_ed_aoi_null_orbit :
    ∀ s : Set UpperHalfPlane, MeasurableSet s →
      (MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane) s = 0 →
      ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane),
        ∀ a : Matrix.SpecialLinearGroup (Fin 2) ℤ, a • z ∉ s := by
  intro s hs hnull
  -- The determinant-one subtype of four integer entries is countable.
  let : Countable (Matrix.SpecialLinearGroup (Fin 2) ℤ) := by
    unfold Matrix.SpecialLinearGroup Matrix
    infer_instance
  apply MeasureTheory.ae_all_iff.mpr
  intro a
  -- The modular action is the restriction of the measure-invariant real GL action.
  change ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane),
    z ∉ (fun z : UpperHalfPlane => Matrix.SpecialLinearGroup.mapGL ℝ a • z) ⁻¹' s
  apply MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
  exact (MeasureTheory.SMulInvariantMeasure.measure_preimage_smul
    (μ := (MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane))
    (Matrix.SpecialLinearGroup.mapGL ℝ a) hs).trans hnull

/-- Almost every modular orbit avoids the boundary of the standard fundamental domain. -/
theorem f036cc6b1f_pc_ed_ae_orbit_interior :
    ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane),
      ∀ a : Matrix.SpecialLinearGroup (Fin 2) ℤ,
        a • z ∈ ModularGroup.fd → a • z ∈ ModularGroup.fdo := by
  exact (f036cc6b1f_pc_ed_aoi_null_orbit (ModularGroup.fd \ ModularGroup.fdo)
    f036cc6b1f_pc_ed_aoi_boundary_null.1 f036cc6b1f_pc_ed_aoi_boundary_null.2).mono
    fun _ hz a hfd => Classical.byContradiction fun hfdo => hz a ⟨hfd, hfdo⟩

end Submission

namespace Submission

/-- Away from the modular boundary, a union of separated coset translates meets each
subgroup orbit in at most one point modulo the central sign. -/
theorem f036cc6b1f_pc_ed_transversal_unique :
    ∀ (Δ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
      (R : Finset (Matrix.SpecialLinearGroup (Fin 2) ℤ)),
      (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) ∈ Δ →
      (∀ r ∈ R, ∀ s ∈ R, s * r⁻¹ ∈ Δ → s = r) →
      ∀ z : UpperHalfPlane,
      (∀ a : Matrix.SpecialLinearGroup (Fin 2) ℤ,
        a • z ∈ ModularGroup.fd → a • z ∈ ModularGroup.fdo) →
      let F : Set UpperHalfPlane :=
        ⋃ r ∈ R, (fun w : UpperHalfPlane => r • w) '' ModularGroup.fd
      ∀ γ δ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
        γ ∈ Δ → δ ∈ Δ → γ • z ∈ F → δ • z ∈ F → δ = γ ∨ δ = -γ := by
  intro Δ R hneg hR z hz F γ δ hγ hδ hγF hδF
  simp only [F, Set.mem_iUnion, Set.mem_image] at hγF hδF
  rcases hγF with ⟨r, hr, w, hw, hrw⟩
  rcases hδF with ⟨s, hs, v, hv, hsv⟩
  have hwz : (r⁻¹ * γ) • z = w := by
    rw [mul_smul, ← hrw, inv_smul_smul]
  have hwo : w ∈ ModularGroup.fdo := by
    rw [← hwz] at hw ⊢
    exact hz _ hw
  have haw : (s⁻¹ * (δ * γ⁻¹) * r) • w = v := by
    simp only [mul_smul, hrw, inv_smul_smul, ← hsv]
  -- Interior uniqueness reduces the transition matrix to the two central signs.
  have ha := ModularGroup.eq_one_or_neg_one_of_mem_fdo_mem_fd hwo
    (show (s⁻¹ * (δ * γ⁻¹) * r) • w ∈ ModularGroup.fd by
      simpa only [haw] using hv)
  have hq : δ * γ⁻¹ ∈ Δ := Δ.mul_mem hδ (Δ.inv_mem hγ)
  have hqeq : δ * γ⁻¹ = s * (s⁻¹ * (δ * γ⁻¹) * r) * r⁻¹ := by
    simp [mul_assoc]
  rcases ha with ha | ha
  · have heq : δ * γ⁻¹ = s * r⁻¹ := by
      simpa only [ha, mul_one] using hqeq
    have hsr : s = r := hR r hr s hs (heq ▸ hq)
    left
    have hcancel : δ * γ⁻¹ = 1 := by simpa only [hsr, mul_inv_cancel] using heq
    exact mul_inv_eq_one.mp hcancel
  · have heq : δ * γ⁻¹ = -(s * r⁻¹) := by
      simpa only [ha, mul_neg, mul_one, neg_mul] using hqeq
    -- The negative sign can be removed because -1 belongs to the subgroup.
    have hsrmem : s * r⁻¹ ∈ Δ := by
      have h := Δ.mul_mem hneg hq
      simpa only [heq, neg_mul, one_mul, neg_neg] using h
    have hsr : s = r := hR r hr s hs hsrmem
    right
    have hcancel : δ * γ⁻¹ = -1 := by
      simpa only [hsr, mul_inv_cancel] using heq
    have h := congrArg (fun a => a * γ) hcancel
    simpa only [inv_mul_cancel_right, neg_mul, one_mul] using h

end Submission

namespace Submission

/-- Almost every point has a modular orbit disjoint from a prescribed measurable null set. -/
theorem f036cc6b1f_pc_ed_aoi_null_orbit :
    ∀ s : Set UpperHalfPlane, MeasurableSet s →
      (MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane) s = 0 →
      ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane),
        ∀ a : Matrix.SpecialLinearGroup (Fin 2) ℤ, a • z ∉ s := by
  intro s hs hnull
  -- The determinant-one subtype of four integer entries is countable.
  let : Countable (Matrix.SpecialLinearGroup (Fin 2) ℤ) := by
    unfold Matrix.SpecialLinearGroup Matrix
    infer_instance
  apply MeasureTheory.ae_all_iff.mpr
  intro a
  -- The modular action is the restriction of the measure-invariant real GL action.
  change ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane),
    z ∉ (fun z : UpperHalfPlane => Matrix.SpecialLinearGroup.mapGL ℝ a • z) ⁻¹' s
  apply MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
  exact (MeasureTheory.SMulInvariantMeasure.measure_preimage_smul
    (μ := (MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane))
    (Matrix.SpecialLinearGroup.mapGL ℝ a) hs).trans hnull

/-- Almost every modular orbit avoids the boundary of the standard fundamental domain. -/
theorem f036cc6b1f_pc_ed_ae_orbit_interior :
    ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane),
      ∀ a : Matrix.SpecialLinearGroup (Fin 2) ℤ,
        a • z ∈ ModularGroup.fd → a • z ∈ ModularGroup.fdo := by
  exact (f036cc6b1f_pc_ed_aoi_null_orbit (ModularGroup.fd \ ModularGroup.fdo)
    f036cc6b1f_pc_ed_aoi_boundary_null.1 f036cc6b1f_pc_ed_aoi_boundary_null.2).mono
    fun _ hz a hfd => Classical.byContradiction fun hfdo => hz a ⟨hfd, hfdo⟩

end Submission

namespace Submission

/-- Away from the modular boundary, a union of separated coset translates meets each
subgroup orbit in at most one point modulo the central sign. -/
theorem f036cc6b1f_pc_ed_transversal_unique :
    ∀ (Δ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
      (R : Finset (Matrix.SpecialLinearGroup (Fin 2) ℤ)),
      (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) ∈ Δ →
      (∀ r ∈ R, ∀ s ∈ R, s * r⁻¹ ∈ Δ → s = r) →
      ∀ z : UpperHalfPlane,
      (∀ a : Matrix.SpecialLinearGroup (Fin 2) ℤ,
        a • z ∈ ModularGroup.fd → a • z ∈ ModularGroup.fdo) →
      let F : Set UpperHalfPlane :=
        ⋃ r ∈ R, (fun w : UpperHalfPlane => r • w) '' ModularGroup.fd
      ∀ γ δ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
        γ ∈ Δ → δ ∈ Δ → γ • z ∈ F → δ • z ∈ F → δ = γ ∨ δ = -γ := by
  intro Δ R hneg hR z hz F γ δ hγ hδ hγF hδF
  simp only [F, Set.mem_iUnion, Set.mem_image] at hγF hδF
  rcases hγF with ⟨r, hr, w, hw, hrw⟩
  rcases hδF with ⟨s, hs, v, hv, hsv⟩
  have hwz : (r⁻¹ * γ) • z = w := by
    rw [mul_smul, ← hrw, inv_smul_smul]
  have hwo : w ∈ ModularGroup.fdo := by
    rw [← hwz] at hw ⊢
    exact hz _ hw
  have haw : (s⁻¹ * (δ * γ⁻¹) * r) • w = v := by
    simp only [mul_smul, hrw, inv_smul_smul, ← hsv]
  -- Interior uniqueness reduces the transition matrix to the two central signs.
  have ha := ModularGroup.eq_one_or_neg_one_of_mem_fdo_mem_fd hwo
    (show (s⁻¹ * (δ * γ⁻¹) * r) • w ∈ ModularGroup.fd by
      simpa only [haw] using hv)
  have hq : δ * γ⁻¹ ∈ Δ := Δ.mul_mem hδ (Δ.inv_mem hγ)
  have hqeq : δ * γ⁻¹ = s * (s⁻¹ * (δ * γ⁻¹) * r) * r⁻¹ := by
    simp [mul_assoc]
  rcases ha with ha | ha
  · have heq : δ * γ⁻¹ = s * r⁻¹ := by
      simpa only [ha, mul_one] using hqeq
    have hsr : s = r := hR r hr s hs (heq ▸ hq)
    left
    have hcancel : δ * γ⁻¹ = 1 := by simpa only [hsr, mul_inv_cancel] using heq
    exact mul_inv_eq_one.mp hcancel
  · have heq : δ * γ⁻¹ = -(s * r⁻¹) := by
      simpa only [ha, mul_neg, mul_one, neg_mul] using hqeq
    -- The negative sign can be removed because -1 belongs to the subgroup.
    have hsrmem : s * r⁻¹ ∈ Δ := by
      have h := Δ.mul_mem hneg hq
      simpa only [heq, neg_mul, one_mul, neg_neg] using h
    have hsr : s = r := hR r hr s hs hsrmem
    right
    have hcancel : δ * γ⁻¹ = -1 := by
      simpa only [hsr, mul_inv_cancel] using heq
    have h := congrArg (fun a => a * γ) hcancel
    simpa only [inv_mul_cancel_right, neg_mul, one_mul] using h

end Submission

namespace Submission

theorem f036cc6b1f_pc_effective_domain
    (Δ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Δ.FiniteIndex]
    (hneg : (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) ∈ Δ) :
    ∃ R : Finset (Matrix.SpecialLinearGroup (Fin 2) ℤ),
      let F : Set UpperHalfPlane :=
        ⋃ r ∈ R, (fun z : UpperHalfPlane => r • z) '' ModularGroup.fd
      MeasurableSet F ∧
        (∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane),
          ∃ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
            γ ∈ Δ ∧ γ • z ∈ F ∧
              ∀ δ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
                δ ∈ Δ → δ • z ∈ F → δ = γ ∨ δ = -γ) := by
  classical
  -- Choose one representative of each right coset Δr.
  let : Fintype (Matrix.SpecialLinearGroup (Fin 2) ℤ ⧸ Δ) :=
    Subgroup.fintypeQuotientOfFiniteIndex
  let R : Finset (Matrix.SpecialLinearGroup (Fin 2) ℤ) :=
    Finset.univ.image (fun q : Quotient (QuotientGroup.rightRel Δ) => q.out)
  have hR : ∀ r ∈ R, ∀ s ∈ R, s * r⁻¹ ∈ Δ → s = r := by
    intro r hr s hs hsr
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hr
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hs
    have hqp : q = p :=
      Quotient.out_equiv_out.mp (QuotientGroup.rightRel_apply.mpr hsr)
    exact congrArg Quotient.out hqp.symm
  refine ⟨R, ?_, ?_⟩
  · apply R.measurableSet_biUnion
    intro r _
    -- The SL action is the restriction of the continuous GL action.
    change MeasurableSet
      ((fun z : UpperHalfPlane => Matrix.SpecialLinearGroup.mapGL ℝ r • z) ''
        ModularGroup.fd)
    exact (isClosedMap_smul (Matrix.SpecialLinearGroup.mapGL ℝ r)
      ModularGroup.fd ModularGroup.isClosed_fd).measurableSet
  · filter_upwards [Submission.f036cc6b1f_pc_ed_ae_orbit_interior] with z hz
    obtain ⟨g, hg⟩ := ModularGroup.exists_smul_mem_fd z
    let q : Quotient (QuotientGroup.rightRel Δ) := Quotient.mk _ g⁻¹
    let r : Matrix.SpecialLinearGroup (Fin 2) ℤ := q.out
    have hr : r ∈ R := Finset.mem_image.mpr ⟨q, Finset.mem_univ _, rfl⟩
    have hmem : g⁻¹ * r⁻¹ ∈ Δ :=
      QuotientGroup.rightRel_apply.mp (Quotient.mk_out g⁻¹)
    -- If g⁻¹ = ηr, then η⁻¹z = r(gz) lies in the finite union.
    have hγ : (g⁻¹ * r⁻¹)⁻¹ ∈ Δ := Δ.inv_mem hmem
    have hγF : (g⁻¹ * r⁻¹)⁻¹ • z ∈
        ⋃ s ∈ R, (fun w : UpperHalfPlane => s • w) '' ModularGroup.fd := by
      refine Set.mem_iUnion.mpr ⟨r, Set.mem_iUnion.mpr ⟨hr, ?_⟩⟩
      exact ⟨g • z, hg, by simp only [mul_inv_rev, inv_inv, mul_smul]⟩
    refine ⟨(g⁻¹ * r⁻¹)⁻¹, hγ, hγF, ?_⟩
    intro δ hδ hδF
    exact Submission.f036cc6b1f_pc_ed_transversal_unique Δ R hneg hR z hz
      (g⁻¹ * r⁻¹)⁻¹ δ hγ hδ hγF hδF

end Submission

namespace Submission

open MeasureTheory
open scoped ComplexConjugate

theorem f036cc6b1f_pc_integral_core
    (Δ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Δ.FiniteIndex]
    (hneg : (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) ∈ Δ) :
    ∃ B : InnerProductSpace.Core ℂ (CuspForm Δ 2),
      ∀ (F : Set UpperHalfPlane), MeasurableSet F →
        (∀ᵐ z ∂(volume : Measure UpperHalfPlane),
          ∃ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
            γ ∈ Δ ∧ γ • z ∈ F ∧
              ∀ δ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
                δ ∈ Δ → δ • z ∈ F → δ = γ ∨ δ = -γ) →
        ∀ f g : CuspForm Δ 2,
          IntegrableOn (UpperHalfPlane.petersson 2 f g) F
              (volume : Measure UpperHalfPlane) ∧
            B.inner f g = integral ((volume : Measure UpperHalfPlane).restrict F)
              (UpperHalfPlane.petersson 2 f g) := by
  classical
  obtain ⟨R, hEmeas, hErep⟩ := f036cc6b1f_pc_effective_domain Δ hneg
  let E : Set UpperHalfPlane :=
    ⋃ r ∈ R, (fun z : UpperHalfPlane => r • z) '' ModularGroup.fd
  have hEint (f g : CuspForm Δ 2) :
      IntegrableOn (UpperHalfPlane.petersson 2 f g) E
        (volume : Measure UpperHalfPlane) := by
    exact integrableOn_finset_iUnion.mpr
      (fun r _ => f036cc6b1f_pic_translated_integrable Δ r f g)
  have hEcover : ∀ᵐ z ∂(volume : Measure UpperHalfPlane),
      ∃ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, γ ∈ Δ ∧ γ • z ∈ E := by
    filter_upwards [hErep] with z hz
    obtain ⟨γ, hγ, hz, _⟩ := hz
    exact ⟨γ, hγ, hz⟩
  let B : InnerProductSpace.Core ℂ (CuspForm Δ 2) :=
    { inner := fun f g => integral ((volume : Measure UpperHalfPlane).restrict E)
        (UpperHalfPlane.petersson 2 f g)
      conj_inner_symm := by
        intro f g
        rw [← integral_conj]
        exact integral_congr_ae (Filter.Eventually.of_forall fun z =>
          (UpperHalfPlane.petersson_symm 2 g f z).symm)
      re_inner_nonneg := by
        intro f
        rw [← integral_re (hEint f f)]
        apply integral_nonneg
        intro z
        simp only [UpperHalfPlane.petersson, ← Complex.normSq_eq_conj_mul_self,
          zpow_ofNat, ← Complex.ofReal_pow, ← Complex.ofReal_mul]
        exact mul_nonneg (Complex.normSq_nonneg (f z)) (sq_nonneg z.im)
      add_left := by
        intro f g h
        calc
          _ = integral ((volume : Measure UpperHalfPlane).restrict E)
              (fun z => UpperHalfPlane.petersson 2 f h z +
                UpperHalfPlane.petersson 2 g h z) := by
            apply integral_congr_ae
            filter_upwards [] with z
            simp [UpperHalfPlane.petersson, map_add, add_mul]
          _ = _ := integral_add (hEint f h) (hEint g h)
      smul_left := by
        intro f g c
        calc
          _ = integral ((volume : Measure UpperHalfPlane).restrict E)
              (fun z => conj c * UpperHalfPlane.petersson 2 f g z) := by
            apply integral_congr_ae
            filter_upwards [] with z
            simp [UpperHalfPlane.petersson, map_mul, mul_assoc]
          _ = _ := integral_const_mul _ _
      definite := fun f hf =>
        f036cc6b1f_pic_diagonal_definite Δ E hEmeas hEcover f (hEint f f) hf }
  refine ⟨B, ?_⟩
  intro F hFmeas hFrep f g
  apply f036cc6b1f_pic_domain_transfer Δ E F hneg hEmeas hFmeas hErep hFrep
    (UpperHalfPlane.petersson 2 f g)
  · exact UpperHalfPlane.petersson_continuous 2
      (CuspFormClass.holo f).continuous (CuspFormClass.holo g).continuous
  · intro γ hγ z
    exact SlashInvariantFormClass.petersson_smul
      (f := f) (f' := g) (τ := z) (Subgroup.mem_map.mpr ⟨γ, hγ, rfl⟩)
  · exact hEint f g

end Submission

namespace Submission

open MeasureTheory Matrix.SpecialLinearGroup
open scoped MatrixGroups ModularForm ComplexConjugate

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
set_option autoImplicit false in
set_option backward.isDefEq.respectTransparency.types false in
theorem f036cc6b1f_pc_hecke_integral :
    ∀ (M : ℕ) [NeZero M] (F : Set UpperHalfPlane), MeasurableSet F →
      (∀ᵐ z ∂(volume : Measure UpperHalfPlane),
        ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M ∧ γ • z ∈ F ∧
          ∀ δ : SL(2, ℤ), δ ∈ CongruenceSubgroup.Gamma0 M → δ • z ∈ F →
            δ = γ ∨ δ = -γ) →
      ∀ (p : ℕ) (hp : p.Prime) (hpM : ¬ p ∣ M)
        (f g : CuspForm (CongruenceSubgroup.Gamma0 M) 2),
      integral ((volume : Measure UpperHalfPlane).restrict F)
          (UpperHalfPlane.petersson 2 (CuspForm.heckeTLin 2 hp hpM f) g) =
        integral ((volume : Measure UpperHalfPlane).restrict F)
          (UpperHalfPlane.petersson 2 f (CuspForm.heckeTLin 2 hp hpM g)) := by
  classical
  intro M instM F hF hFdom p hp hpM f g
  have : NeZero p := ⟨hp.ne_zero⟩
  -- The subgroup cuts out the right cosets of the good-prime double coset.
  let Γ := CongruenceSubgroup.Gamma0 M
  let A := ModularForm.heckeMatrix p 0
  let C := ModularForm.heckeDiagMatrix p
  let ι : SL(2, ℤ) →* GL (Fin 2) ℝ := mapGL ℝ
  let U : Subgroup SL(2, ℤ) :=
    { carrier := {γ | (p : ℤ) ∣ γ 0 1}
      one_mem' := by simp
      mul_mem' := by
        intro a b ha hb
        change (p : ℤ) ∣ (a.1 * b.1) 0 1
        rw [(Matrix.two_mul_expl a.1 b.1).2.1]
        exact dvd_add (hb.mul_left _) (ha.mul_right _)
      inv_mem' := by
        intro a ha
        change (p : ℤ) ∣ a⁻¹ 0 1
        rw [SL2_inv_expl a]
        simpa using ha }
  have hGU : CongruenceSubgroup.Gamma p ≤ U := by
    intro γ hγ
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
      ((CongruenceSubgroup.Gamma_mem.mp hγ).2.1)
  have : U.FiniteIndex := Subgroup.finiteIndex_of_le hGU
  let H := Γ ⊓ U
  have hHΓ : H ≤ Γ := inf_le_left
  have hneg : (-1 : SL(2, ℤ)) ∈ H := by
    constructor
    · simp [Γ, CongruenceSubgroup.Gamma0_mem]
    · change (p : ℤ) ∣ (-1 : SL(2, ℤ)) 0 1
      simp
  have hconj (γ : SL(2, ℤ)) (hγ : γ ∈ Γ) :
      γ ∈ H ↔ A * ι γ * A⁻¹ ∈ (Γ : Subgroup (GL (Fin 2) ℝ)) := by
    constructor
    · intro h
      obtain ⟨e, he⟩ := h.2
      obtain ⟨δ, hδ10, hδ⟩ :=
        P2MW.S_ModularForm_heckeT_slash_eq_self_of_mem_Gamma0.ModularForm.HeckeSlashInvariance.heckeMatrix_mul_of_eq
          hp.ne_zero γ 0 0 e (by simpa using he)
      have hδΓ : δ ∈ Γ := by
        rw [CongruenceSubgroup.Gamma0_mem] at hγ ⊢
        simp [hδ10, hγ]
      exact Subgroup.mem_map.mpr ⟨δ, hδΓ, by
        change ι δ = A * ι γ * A⁻¹
        rw [show A * ι γ = ι δ * A from hδ]
        simp [mul_assoc]⟩
    · rintro ⟨δ, hδΓ, hδ⟩
      refine ⟨hγ, ?_⟩
      have hm : A * ι γ = ι δ * A := by rw [hδ]; group
      have he := congrArg (fun B : GL (Fin 2) ℝ => B 0 1) hm
      have he' : (γ 0 1 : ℝ) = (δ 0 1 : ℝ) * (p : ℝ) := by
        simpa [A, ι, Units.val_mul, ModularForm.val_heckeMatrix hp.ne_zero,
          Matrix.mul_apply, Fin.sum_univ_two, mapGL_coe_matrix] using he
      exact ⟨δ 0 1, by exact_mod_cast he'.trans (mul_comm _ _)⟩
  obtain ⟨r, hrΓ, hruniq, hrA, β, hβΓ, hβ⟩ :=
    f036cc6b1f_pc_hi_good_prime_transversal M p hp hpM
  have hrinj : Function.Injective r := by
    intro i j hij
    obtain ⟨k, hk, huk⟩ := hruniq (r i) (hrΓ i)
    have hi : (p : ℤ) ∣ (r i * (r i)⁻¹) 0 1 := by simp
    have hj : (p : ℤ) ∣ (r i * (r j)⁻¹) 0 1 := by simp [← hij]
    exact (huk i hi).trans (huk j hj).symm
  let R := Finset.univ.image r
  have hRΓ : ∀ γ ∈ R, γ ∈ Γ := by
    intro γ hγ
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hγ
    exact hrΓ i
  have hcover : ∀ γ ∈ Γ, ∃ δ ∈ R, γ * δ⁻¹ ∈ H := by
    intro γ hγ
    obtain ⟨i, hi, _⟩ := hruniq γ hγ
    exact ⟨r i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩,
      Γ.mul_mem hγ (Γ.inv_mem (hrΓ i)), hi⟩
  have huniq : ∀ γ ∈ R, ∀ δ ∈ R, δ * γ⁻¹ ∈ H → δ = γ := by
    intro γ hγ δ hδ h
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hγ
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hδ
    obtain ⟨k, hk, huk⟩ := hruniq (r j) (hrΓ j)
    have hj : (p : ℤ) ∣ (r j * (r j)⁻¹) 0 1 := by simp
    exact congrArg r ((huk j hj).trans (huk i h.2).symm)
  let E : Set UpperHalfPlane := ⋃ γ ∈ R, (fun z : UpperHalfPlane => γ • z) '' F
  obtain ⟨hE, hEdom, _⟩ := f036cc6b1f_pc_hi_effective_domain_lift
    Γ H R F hHΓ hneg hRΓ hcover huniq hF hFdom
  have hArat : ∀ i j : Fin 2, ∃ q : ℚ, A i j = (q : ℝ) := by
    intro i j
    refine ⟨!![(1 : ℚ), 0; 0, (p : ℚ)] i j, ?_⟩
    fin_cases i <;> fin_cases j <;> simp [A, ModularForm.val_heckeMatrix hp.ne_zero]
  have hApos : 0 < (A.det : ℝ) := ModularForm.det_heckeMatrix_pos p 0
  have hslash (v : CuspForm Γ 2) :
      ∃ w : CuspForm H 2, (w : UpperHalfPlane → ℂ) = (v : UpperHalfPlane → ℂ) ∣[(2 : ℤ)] A :=
    f036cc6b1f_pc_hi_rational_slash Γ H A hApos hArat
      (fun γ hγ => (hconj γ hγ.1).mp hγ) v
  have hrestrict (v : CuspForm Γ 2) :
      ∃ w : CuspForm H 2, (w : UpperHalfPlane → ℂ) = (v : UpperHalfPlane → ℂ) := by
    obtain ⟨w, hw⟩ := f036cc6b1f_pc_hi_rational_slash Γ H 1 (by simp)
      (by intro i j; exact ⟨(1 : Matrix (Fin 2) (Fin 2) ℚ) i j, by fin_cases i <;> fin_cases j <;> simp⟩)
      (by intro γ hγ; simpa using hγ.1) v
    exact ⟨w, by simpa using hw⟩
  obtain ⟨fA, hfA⟩ := hslash f
  obtain ⟨gA, hgA⟩ := hslash g
  obtain ⟨fH, hfH⟩ := hrestrict f
  obtain ⟨gH, hgH⟩ := hrestrict g
  obtain ⟨B, hB⟩ := f036cc6b1f_pc_integral_core H hneg
  have hintegrable (v w : CuspForm H 2) :
      IntegrableOn (UpperHalfPlane.petersson 2 v w) E (volume : Measure UpperHalfPlane) :=
    (hB E hE hEdom v w).1
  have hinv (v : CuspForm Γ 2) (γ : SL(2, ℤ)) (hγ : γ ∈ Γ) :
      (v : UpperHalfPlane → ℂ) ∣[(2 : ℤ)] γ = v :=
    SlashInvariantFormClass.slash_action_eq v (ι γ) (Subgroup.mem_map.mpr ⟨γ, hγ, rfl⟩)
  -- The approved transversal recovers the exact normalization of heckeTLin.
  have htrace (v : CuspForm Γ 2) :
      R.sum (fun γ => ((v : UpperHalfPlane → ℂ) ∣[(2 : ℤ)] A) ∣[(2 : ℤ)] γ) =
        (CuspForm.heckeTLin 2 hp hpM v : UpperHalfPlane → ℂ) := by
    rw [Finset.sum_image (fun i _ j _ hij => hrinj hij)]
    have hterm (γ : SL(2, ℤ)) :
        ((v : UpperHalfPlane → ℂ) ∣[(2 : ℤ)] A) ∣[(2 : ℤ)] γ =
          (v : UpperHalfPlane → ℂ) ∣[(2 : ℤ)] (A * ι γ) :=
      (SlashAction.slash_mul (2 : ℤ) A (ι γ) (v : UpperHalfPlane → ℂ)).symm
    simp_rw [hterm]
    rw [Fin.sum_univ_castSucc]
    simp only [A, ι, hrA, hβ]
    rw [SlashAction.slash_mul]
    rw [show (v : UpperHalfPlane → ℂ) ∣[(2 : ℤ)] mapGL ℝ β = v from hinv v β hβΓ]
    rw [CuspForm.coe_heckeTLin_apply, ModularForm.heckeT_def,
      Fin.sum_univ_eq_sum_range (fun j => (v : UpperHalfPlane → ℂ) ∣[(2 : ℤ)] ModularForm.heckeMatrix p j) p]
  have hunfold (v w : CuspForm Γ 2) (vA wH : CuspForm H 2)
      (hvA : (vA : UpperHalfPlane → ℂ) = (v : UpperHalfPlane → ℂ) ∣[(2 : ℤ)] A)
      (hwH : (wH : UpperHalfPlane → ℂ) = (w : UpperHalfPlane → ℂ)) :
      integral (volume.restrict F) (UpperHalfPlane.petersson 2 (CuspForm.heckeTLin 2 hp hpM v) w) =
        integral (volume.restrict E) (UpperHalfPlane.petersson 2 vA wH) := by
    have hi := hintegrable vA wH
    rw [hvA, hwH] at hi ⊢
    have hu := (f036cc6b1f_pc_hi_finite_trace_unfolding Γ H R F hHΓ hneg
      hRΓ hcover huniq hF hFdom ((v : UpperHalfPlane → ℂ) ∣[(2 : ℤ)] A) w
      (hinv w) hi).2
    rwa [htrace v] at hu
  -- W normalizes H and interchanges the two slash terms in the pairing.
  let t := r (Fin.last p)
  let s : ℝˣ := Units.mk0 (p : ℝ) (by exact_mod_cast hp.ne_zero)
  let S : GL (Fin 2) ℝ := Matrix.GeneralLinearGroup.scalar (Fin 2) s
  have hAC : A * C = S := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [A, C, S, s, Units.val_mul, ModularForm.val_heckeMatrix hp.ne_zero,
        ModularForm.val_heckeDiagMatrix hp.ne_zero, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.natCast_apply]
  have hScomm (X : GL (Fin 2) ℝ) : S * X = X * S :=
    Matrix.GeneralLinearGroup.scalar_commute s X
  have hSconj (X Y : GL (Fin 2) ℝ) :
      (S * X) * Y * (S * X)⁻¹ = X * Y * X⁻¹ := by
    calc
      _ = S * (X * Y * X⁻¹) * S⁻¹ := by group
      _ = _ := by rw [hScomm]; group
  have hSslash (v : UpperHalfPlane → ℂ) : v ∣[(2 : ℤ)] S = v := by
    funext z
    have hsp : 0 < (s : ℝ) := by change 0 < (p : ℝ); exact_mod_cast hp.pos
    have hsne : (s : ℂ) ≠ 0 := by exact_mod_cast s.ne_zero
    simp [ModularForm.slash_apply, S, UpperHalfPlane.σ, Matrix.GeneralLinearGroup.det_scalar,
      pow_pos hsp, abs_of_pos (pow_pos hsp 2), zpow_neg, hsne]
  let W : GL (Fin 2) ℝ := (ι β)⁻¹ * A
  have hW : W = C * (ι t)⁻¹ := by
    change A * ι t = ι β * C at hβ
    have h := congrArg (fun X : GL (Fin 2) ℝ => (ι β)⁻¹ * X * (ι t)⁻¹) hβ
    simpa [W, mul_assoc] using h
  have hAW : A * W = S * (ι t)⁻¹ := by rw [hW, ← mul_assoc, hAC]
  have hWi : W⁻¹ = A⁻¹ * ι β := by simp [W]
  have hnorm (γ : SL(2, ℤ)) (hγ : γ ∈ H) :
      ∃ δ ∈ H, ι δ = W * ι γ * W⁻¹ := by
    obtain ⟨δ, hδΓ, hδ⟩ := (hconj γ hγ.1).mp hγ
    change ι δ = A * ι γ * A⁻¹ at hδ
    let κ := β⁻¹ * δ * β
    have hκΓ : κ ∈ Γ := Γ.mul_mem (Γ.mul_mem (Γ.inv_mem hβΓ) hδΓ) hβΓ
    have hκ : ι κ = W * ι γ * W⁻¹ := by
      simp only [κ, map_mul, map_inv, hδ, W]
      group
    refine ⟨κ, (hconj κ hκΓ).mpr ?_, hκ⟩
    have he : A * ι κ * A⁻¹ = ι (t⁻¹ * γ * t) := by
      calc
        _ = (A * W) * ι γ * (A * W)⁻¹ := by rw [hκ]; group
        _ = (S * (ι t)⁻¹) * ι γ * (S * (ι t)⁻¹)⁻¹ := by rw [hAW]
        _ = _ := by rw [hSconj]; simp only [map_mul, map_inv, inv_inv]
    rw [he]
    exact Subgroup.mem_map.mpr ⟨t⁻¹ * γ * t,
      Γ.mul_mem (Γ.mul_mem (Γ.inv_mem (hrΓ _)) hγ.1) (hrΓ _), rfl⟩
  have hnorminv (γ : SL(2, ℤ)) (hγ : γ ∈ H) :
      ∃ δ ∈ H, ι δ = W⁻¹ * ι γ * W := by
    obtain ⟨δ, hδΓ, hδ⟩ := (hconj γ hγ.1).mp hγ
    change ι δ = A * ι γ * A⁻¹ at hδ
    let κ := t * δ * t⁻¹
    have hκΓ : κ ∈ Γ := Γ.mul_mem (Γ.mul_mem (hrΓ _) hδΓ) (Γ.inv_mem (hrΓ _))
    have hκ : ι κ = W⁻¹ * ι γ * W := by
      have he : S * (ι t)⁻¹ = A * W := hAW.symm
      have hc := hSconj (ι t)⁻¹ (ι κ)
      rw [he] at hc
      have hc' : (ι t)⁻¹ * ι κ * ((ι t)⁻¹)⁻¹ = A * ι γ * A⁻¹ := by
        simp [κ, map_mul, map_inv, hδ, mul_assoc]
      rw [hc'] at hc
      have hh := congrArg (fun X : GL (Fin 2) ℝ => W⁻¹ * A⁻¹ * X * A * W) hc
      simpa [mul_assoc] using hh
    refine ⟨κ, (hconj κ hκΓ).mpr ?_, hκ⟩
    have he : A * ι κ * A⁻¹ = ι (β * γ * β⁻¹) := by
      rw [hκ, hWi]
      simp [W, map_mul, map_inv, mul_assoc]
    rw [he]
    exact Subgroup.mem_map.mpr ⟨β * γ * β⁻¹,
      Γ.mul_mem (Γ.mul_mem hβΓ hγ.1) (Γ.inv_mem hβΓ), rfl⟩
  have hWpos : 0 < (W.det : ℝ) := by
    simpa [W, ι, map_mul, map_inv] using hApos
  have hWf (v : CuspForm Γ 2) :
      ((v : UpperHalfPlane → ℂ) ∣[(2 : ℤ)] A) ∣[(2 : ℤ)] W⁻¹ = v := by
    rw [← SlashAction.slash_mul, hWi]
    simpa only [mul_inv_cancel_left] using
      (show (v : UpperHalfPlane → ℂ) ∣[(2 : ℤ)] ι β = v from hinv v β hβΓ)
  have hWg (v : CuspForm Γ 2) :
      (v : UpperHalfPlane → ℂ) ∣[(2 : ℤ)] W⁻¹ = (v : UpperHalfPlane → ℂ) ∣[(2 : ℤ)] A := by
    have hv : (v : UpperHalfPlane → ℂ) ∣[(2 : ℤ)] S⁻¹ = v := by
      have hh := congrArg (fun u : UpperHalfPlane → ℂ => u ∣[(2 : ℤ)] S⁻¹) (hSslash v)
      simpa only [← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one] using hh.symm
    have he : W⁻¹ = ι t * S⁻¹ * A := by
      have hh := congrArg (fun X : GL (Fin 2) ℝ => ι t * S⁻¹ * X * W⁻¹) hAW
      simpa [mul_assoc] using hh.symm
    rw [he, SlashAction.slash_mul, SlashAction.slash_mul]
    rw [show (v : UpperHalfPlane → ℂ) ∣[(2 : ℤ)] ι t = v from hinv v t (hrΓ _), hv]
  -- Transport the effective domain, retaining uniqueness modulo the central sign.
  let E' : Set UpperHalfPlane := (fun z : UpperHalfPlane => W • z) '' E
  have hE' : MeasurableSet E' :=
    (Homeomorph.smul W).measurableEmbedding.measurableSet_image.mpr hE
  have hE'dom : ∀ᵐ z ∂(volume : Measure UpperHalfPlane),
      ∃ γ : SL(2, ℤ), γ ∈ H ∧ γ • z ∈ E' ∧
        ∀ δ : SL(2, ℤ), δ ∈ H → δ • z ∈ E' → δ = γ ∨ δ = -γ := by
    have hpre := (measurePreserving_smul W⁻¹ (volume : Measure UpperHalfPlane)).quasiMeasurePreserving.ae hEdom
    filter_upwards [hpre] with z hz
    obtain ⟨γ, hγ, hzγ, huniqγ⟩ := hz
    obtain ⟨δ, hδ, hδeq⟩ := hnorm γ hγ
    have hact : δ • z = W • (γ • (W⁻¹ • z)) := by
      change ι δ • z = _
      rw [hδeq, mul_smul, mul_smul]
      rfl
    refine ⟨δ, hδ, ?_, ?_⟩
    · exact ⟨γ • (W⁻¹ • z), hzγ, hact.symm⟩
    · intro δ' hδ' hzδ'
      obtain ⟨γ', hγ', hγ'eq⟩ := hnorminv δ' hδ'
      have hzγ' : γ' • (W⁻¹ • z) ∈ E := by
        obtain ⟨w, hw, he⟩ := hzδ'
        have ha : γ' • (W⁻¹ • z) = w := by
          change ι γ' • (W⁻¹ • z) = w
          rw [hγ'eq]
          simpa [mul_smul, ι, mapGL] using congrArg (fun x : UpperHalfPlane => W⁻¹ • x) he.symm
        rwa [ha]
      have hδ'eq : ι δ' = W * ι γ' * W⁻¹ := by rw [hγ'eq]; group
      rcases huniqγ γ' hγ' hzγ' with he | he
      · left
        apply mapGL_injective (R := ℤ) (S := ℝ)
        change ι δ' = _
        rw [hδ'eq, he, ← hδeq]
      · right
        apply mapGL_injective (R := ℤ) (S := ℝ)
        change ι δ' = _
        rw [hδ'eq, he]
        change W * mapGL ℝ (-γ) * W⁻¹ = mapGL ℝ (-δ)
        have hnegmap (a : SL(2, ℤ)) : mapGL ℝ (-a) = -(mapGL ℝ a) := by
          apply Units.ext
          simp
        rw [hnegmap, hnegmap, mul_neg, neg_mul]
        exact congrArg Neg.neg hδeq.symm
  have hcov : (fun z : UpperHalfPlane => UpperHalfPlane.petersson 2 fH gA (W • z)) =
      UpperHalfPlane.petersson 2 fA gH := by
    funext z
    have hh := UpperHalfPlane.petersson_slash 2 (fA : UpperHalfPlane → ℂ)
      (gH : UpperHalfPlane → ℂ) W⁻¹ (W • z)
    rw [hfA, hgH, hWf f, hWg g] at hh
    have hsigma : UpperHalfPlane.σ W⁻¹ = ContinuousAlgEquiv.refl ℝ ℂ := by
      apply if_pos
      simpa only [map_inv, Units.val_inv_eq_inv_val] using inv_pos.mpr hWpos
    simpa [hfA, hfH, hgA, hgH, hsigma] using hh
  -- Domain independence and covariance exchange the two terms; conjugation refolds.
  have hexchange : integral (volume.restrict E) (UpperHalfPlane.petersson 2 fA gH) =
      integral (volume.restrict E) (UpperHalfPlane.petersson 2 fH gA) := by
    rw [← hcov]
    rw [← (measurePreserving_smul W (volume : Measure UpperHalfPlane)).setIntegral_image_emb
      (Homeomorph.smul W).measurableEmbedding (UpperHalfPlane.petersson 2 fH gA) E]
    exact ((hB E' hE' hE'dom fH gA).2).symm.trans (hB E hE hEdom fH gA).2
  have hreverse := congrArg (starRingEnd ℂ) (hunfold g f gA fH hgA hfH)
  have hsymm (D : Set UpperHalfPlane) (u v : UpperHalfPlane → ℂ) :
      conj (integral (volume.restrict D) (UpperHalfPlane.petersson 2 u v)) =
        integral (volume.restrict D) (UpperHalfPlane.petersson 2 v u) := by
    rw [← integral_conj]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun z => (UpperHalfPlane.petersson_symm 2 u v z).symm)
  rw [hsymm, hsymm] at hreverse
  calc
    _ = integral (volume.restrict E) (UpperHalfPlane.petersson 2 fA gH) := hunfold f g fA gH hfA hgH
    _ = integral (volume.restrict E) (UpperHalfPlane.petersson 2 fH gA) := hexchange
    _ = _ := hreverse.symm

end Submission


theorem Submission.f036cc6b1f_petersson_core (M : ℕ) [NeZero M] :
    ∃ B : InnerProductSpace.Core ℂ (CuspForm (CongruenceSubgroup.Gamma0 M) 2),
      ∀ (p : ℕ) (hp : p.Prime) (hpM : ¬ p ∣ M)
        (f g : CuspForm (CongruenceSubgroup.Gamma0 M) 2),
        B.inner (CuspForm.heckeTLin 2 hp hpM f) g =
          B.inner f (CuspForm.heckeTLin 2 hp hpM g) := by
  have hneg : (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) ∈
      CongruenceSubgroup.Gamma0 M := by
    simp [CongruenceSubgroup.Gamma0_mem]
  obtain ⟨R, hFmeas, hFdom⟩ :=
    Submission.f036cc6b1f_pc_effective_domain (CongruenceSubgroup.Gamma0 M) hneg
  obtain ⟨B, hB⟩ :=
    Submission.f036cc6b1f_pc_integral_core (CongruenceSubgroup.Gamma0 M) hneg
  refine ⟨B, ?_⟩
  intro p hp hpM f g
  exact ((hB _ hFmeas hFdom (CuspForm.heckeTLin 2 hp hpM f) g).2).trans
    ((Submission.f036cc6b1f_pc_hecke_integral M _ hFmeas hFdom p hp hpM f g).trans
      ((hB _ hFmeas hFdom f (CuspForm.heckeTLin 2 hp hpM g)).2).symm)

section

open UpperHalfPlane MeasureTheory Matrix.SpecialLinearGroup
open scoped MatrixGroups Pointwise

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

section

open ModularForm ModularFormClass
open P2MW.S_ModularForm_mdifferentiable_heckeT.M4cP1W2

namespace Submission

/-- Good-prime weight-two Hecke operators commute on cusp forms of level `M`. -/
theorem f036cc6b1f_hecke_commute :
    ∀ (M : ℕ) [NeZero M] (p r : ℕ) (hp : p.Prime) (hr : r.Prime)
      (hpM : ¬ p ∣ M) (hrM : ¬ r ∣ M),
      (CuspForm.heckeTLin 2 hp hpM).comp (CuspForm.heckeTLin 2 hr hrM) =
        (CuspForm.heckeTLin 2 hr hrM).comp (CuspForm.heckeTLin 2 hp hpM) := by
  intro M _ p r hp hr hpM hrM
  by_cases hpr : p = r
  · subst r
    rfl
  have hcop : p.Coprime r := (Nat.coprime_primes hp hr).mpr hpr
  have hpr' : ¬ p ∣ r := hp.coprime_iff_not_dvd.mp hcop
  have hrp' : ¬ r ∣ p := hr.coprime_iff_not_dvd.mp hcop.symm
  have hΓ : (1 : ℝ) ∈
      (CongruenceSubgroup.Gamma0 M : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
    simp
  -- P2M/Sol/S_ModularForm_mdifferentiable_heckeT.lean, already present at
  -- proof base 674e47109a2c121849b48a3754cad6d3c648d80e, proves this coefficient
  -- formula for the exact bundled Hecke normalization and qCoeff uniqueness below.
  have hcoeff (s : ℕ) (hs : s.Prime) (hsM : ¬ s ∣ M)
      (g : CuspForm (CongruenceSubgroup.Gamma0 M) 2) :
      qCoeff (CuspForm.heckeTLin 2 hs hsM g) = coeffHeckeT 2 s (qCoeff g) := by
    funext n
    exact qCoeff_heckeT_class hs.ne_zero g hΓ n
  refine LinearMap.ext fun f => eq_of_forall_qCoeff_eq hΓ fun n => ?_
  change qCoeff (CuspForm.heckeTLin 2 hp hpM (CuspForm.heckeTLin 2 hr hrM f)) n =
    qCoeff (CuspForm.heckeTLin 2 hr hrM (CuspForm.heckeTLin 2 hp hpM f)) n
  rw [hcoeff p hp hpM, hcoeff r hr hrM, hcoeff r hr hrM, hcoeff p hp hpM]
  simp only [coeffHeckeT_apply, show (2 : ℤ) - 1 = 1 from rfl, zpow_one,
    hp.dvd_mul, hr.dvd_mul, hpr', hrp', or_false]
  -- These four divisibility cases also include the constant coefficient `n = 0`.
  by_cases hpn : p ∣ n <;> by_cases hrn : r ∣ n
  · have hrnp : r ∣ n / p :=
      (Nat.dvd_div_iff_mul_dvd hpn).mpr (hcop.mul_dvd_of_dvd_of_dvd hpn hrn)
    have hpnr : p ∣ n / r :=
      (Nat.dvd_div_iff_mul_dvd hrn).mpr (hcop.symm.mul_dvd_of_dvd_of_dvd hrn hpn)
    simp only [if_pos hpn, if_pos hrn, if_pos hrnp, if_pos hpnr]
    rw [Nat.mul_comm n p, Nat.mul_comm n r, Nat.mul_div_assoc p hrn,
      Nat.mul_div_assoc r hpn]
    simp only [Nat.div_div_eq_div_mul, Nat.mul_comm, Nat.mul_left_comm]
    ring
  · have hrnp : ¬ r ∣ n / p := fun h => hrn (dvd_trans h (Nat.div_dvd_of_dvd hpn))
    simp only [if_pos hpn, if_neg hrn, if_neg hrnp, add_zero]
    rw [Nat.mul_comm n r, Nat.mul_div_assoc r hpn]
    simp only [Nat.mul_comm, Nat.mul_left_comm]
  · have hpnr : ¬ p ∣ n / r := fun h => hpn (dvd_trans h (Nat.div_dvd_of_dvd hrn))
    simp only [if_neg hpn, if_pos hrn, if_neg hpnr, add_zero]
    rw [Nat.mul_comm n p, Nat.mul_div_assoc p hrn]
    simp only [Nat.mul_comm, Nat.mul_left_comm]
  · simp only [if_neg hpn, if_neg hrn, add_zero]
    congr 1
    exact Nat.mul_right_comm n p r

end Submission
end

namespace Submission

open scoped ModularForm

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

namespace Submission

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

end Submission

namespace Submission

/-- The coefficients from zero through the approved Sturm bound embed weight-two cusp forms
in a finite product; the bound is inclusive, so the codomain has `b + 1` coordinates. -/
theorem f036cc6b1f_finite_dimensional :
    ∀ (M : ℕ) [NeZero M],
      FiniteDimensional ℂ (CuspForm (CongruenceSubgroup.Gamma0 M) 2) := by
  intro M _
  let b := (2 * (CongruenceSubgroup.Gamma0 M).index) / 12
  have hperiod : (1 : ℝ) ∈
      (CongruenceSubgroup.Gamma0 M :
        Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)).strictPeriods := by
    simp
  let L : CuspForm (CongruenceSubgroup.Gamma0 M) 2 →ₗ[ℂ] (Fin (b + 1) → ℂ) :=
    { toFun := fun f n => (UpperHalfPlane.qExpansion 1 f).coeff n
      map_add' := by
        intro f g
        funext n
        simp only [FunLike.coe_add, ModularForm.qExpansion_add one_pos hperiod,
          map_add, Pi.add_apply]
      map_smul' := by
        intro c f
        funext n
        simp only [FunLike.coe_smul,
          ModularForm.qExpansion_smul one_pos hperiod, PowerSeries.coeff_smul,
          Pi.smul_apply, RingHom.id_apply] }
  apply FiniteDimensional.of_injective L
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro f hf
  apply f036cc6b1f_fd_sturm M f
  intro n hn
  exact congr_fun hf (⟨n, Nat.lt_succ_of_le hn⟩ : Fin (b + 1))

end Submission

end
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

/-- The coefficients from zero through the approved Sturm bound embed weight-two cusp forms
in a finite product; the bound is inclusive, so the codomain has `b + 1` coordinates. -/
theorem f036cc6b1f_finite_dimensional :
    ∀ (M : ℕ) [NeZero M],
      FiniteDimensional ℂ (CuspForm (CongruenceSubgroup.Gamma0 M) 2) := by
  intro M _
  let b := (2 * (CongruenceSubgroup.Gamma0 M).index) / 12
  have hperiod : (1 : ℝ) ∈
      (CongruenceSubgroup.Gamma0 M :
        Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)).strictPeriods := by
    simp
  let L : CuspForm (CongruenceSubgroup.Gamma0 M) 2 →ₗ[ℂ] (Fin (b + 1) → ℂ) :=
    { toFun := fun f n => (UpperHalfPlane.qExpansion 1 f).coeff n
      map_add' := by
        intro f g
        funext n
        simp only [FunLike.coe_add, ModularForm.qExpansion_add one_pos hperiod,
          map_add, Pi.add_apply]
      map_smul' := by
        intro c f
        funext n
        simp only [FunLike.coe_smul,
          ModularForm.qExpansion_smul one_pos hperiod, PowerSeries.coeff_smul,
          Pi.smul_apply, RingHom.id_apply] }
  apply FiniteDimensional.of_injective L
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro f hf
  apply f036cc6b1f_fd_sturm M f
  intro n hn
  exact congr_fun hf (⟨n, Nat.lt_succ_of_le hn⟩ : Fin (b + 1))
namespace Submission

theorem f036cc6b1f_pc_effective_domain
    (Δ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Δ.FiniteIndex]
    (hneg : (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) ∈ Δ) :
    ∃ R : Finset (Matrix.SpecialLinearGroup (Fin 2) ℤ),
      let F : Set UpperHalfPlane :=
        ⋃ r ∈ R, (fun z : UpperHalfPlane => r • z) '' ModularGroup.fd
      MeasurableSet F ∧
        (∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane),
          ∃ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
            γ ∈ Δ ∧ γ • z ∈ F ∧
              ∀ δ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
                δ ∈ Δ → δ • z ∈ F → δ = γ ∨ δ = -γ) := by
  classical
  -- Choose one representative of each right coset Δr.
  let : Fintype (Matrix.SpecialLinearGroup (Fin 2) ℤ ⧸ Δ) :=
    Subgroup.fintypeQuotientOfFiniteIndex
  let R : Finset (Matrix.SpecialLinearGroup (Fin 2) ℤ) :=
    Finset.univ.image (fun q : Quotient (QuotientGroup.rightRel Δ) => q.out)
  have hR : ∀ r ∈ R, ∀ s ∈ R, s * r⁻¹ ∈ Δ → s = r := by
    intro r hr s hs hsr
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hr
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hs
    have hqp : q = p :=
      Quotient.out_equiv_out.mp (QuotientGroup.rightRel_apply.mpr hsr)
    exact congrArg Quotient.out hqp.symm
  refine ⟨R, ?_, ?_⟩
  · apply R.measurableSet_biUnion
    intro r _
    -- The SL action is the restriction of the continuous GL action.
    change MeasurableSet
      ((fun z : UpperHalfPlane => Matrix.SpecialLinearGroup.mapGL ℝ r • z) ''
        ModularGroup.fd)
    exact (isClosedMap_smul (Matrix.SpecialLinearGroup.mapGL ℝ r)
      ModularGroup.fd ModularGroup.isClosed_fd).measurableSet
  · filter_upwards [Submission.f036cc6b1f_pc_ed_ae_orbit_interior] with z hz
    obtain ⟨g, hg⟩ := ModularGroup.exists_smul_mem_fd z
    let q : Quotient (QuotientGroup.rightRel Δ) := Quotient.mk _ g⁻¹
    let r : Matrix.SpecialLinearGroup (Fin 2) ℤ := q.out
    have hr : r ∈ R := Finset.mem_image.mpr ⟨q, Finset.mem_univ _, rfl⟩
    have hmem : g⁻¹ * r⁻¹ ∈ Δ :=
      QuotientGroup.rightRel_apply.mp (Quotient.mk_out g⁻¹)
    -- If g⁻¹ = ηr, then η⁻¹z = r(gz) lies in the finite union.
    have hγ : (g⁻¹ * r⁻¹)⁻¹ ∈ Δ := Δ.inv_mem hmem
    have hγF : (g⁻¹ * r⁻¹)⁻¹ • z ∈
        ⋃ s ∈ R, (fun w : UpperHalfPlane => s • w) '' ModularGroup.fd := by
      refine Set.mem_iUnion.mpr ⟨r, Set.mem_iUnion.mpr ⟨hr, ?_⟩⟩
      exact ⟨g • z, hg, by simp only [mul_inv_rev, inv_inv, mul_smul]⟩
    refine ⟨(g⁻¹ * r⁻¹)⁻¹, hγ, hγF, ?_⟩
    intro δ hδ hδF
    exact Submission.f036cc6b1f_pc_ed_transversal_unique Δ R hneg hR z hz
      (g⁻¹ * r⁻¹)⁻¹ δ hγ hδ hγF hδF

end Submission
theorem Submission.f036cc6b1f_tdi_planar_exp_integrable_fd :
    ∀ (a : ℝ), 0 < a → MeasureTheory.IntegrableOn
      (fun z : UpperHalfPlane => Real.exp (-a * z.im)) ModularGroup.fd
      ((MeasureTheory.volume : MeasureTheory.Measure ℂ).comap UpperHalfPlane.coe) := by
  intro a ha
  let b : ℝ := Real.sqrt 3 / 2
  have hy : MeasureTheory.IntegrableOn (fun y : ℝ => Real.exp (-a * y))
      (Set.Ici b) :=
    (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr
      (exp_neg_integrableOn_Ioi b ha)
  have hx : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ))
      (Set.Icc (-(1 / 2 : ℝ)) (1 / 2)) :=
    MeasureTheory.integrableOn_const (by
      rw [Real.volume_Icc]
      exact ENNReal.ofReal_ne_top)
  have hprod : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => Real.exp (-a * p.2))
      (Set.Icc (-(1 / 2 : ℝ)) (1 / 2) ×ˢ Set.Ici b) := by
    MeasureTheory.integrableOn_Ici_iff_integrableOn_Ioi.mpr (exp_neg_integrableOn_Ioi b ha)
    (MeasureTheory.integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr
      (exp_neg_integrableOn_Ioi b ha)
  have hx : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ))
      (Set.Icc (-(1 / 2 : ℝ)) (1 / 2)) :=
    MeasureTheory.integrableOn_const (by simp only [Real.volume_Icc, ENNReal.ofReal_ne_top])
  have hprod : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => Real.exp (-a * p.2))
      (Set.Icc (-(1 / 2 : ℝ)) (1 / 2) ×ˢ Set.Ici b) := by
    change MeasureTheory.Integrable _
      (((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod MeasureTheory.volume).restrict _)
    rw [← MeasureTheory.Measure.prod_restrict]
    simpa only [one_mul] using hx.mul_prod hy
  have hc : MeasureTheory.IntegrableOn (fun z : ℂ => Real.exp (-a * z.im))
      (Complex.measurableEquivRealProd ⁻¹'
        (Set.Icc (-(1 / 2 : ℝ)) (1 / 2) ×ˢ Set.Ici b)) :=
        (Set.Icc (-(1 : ℝ) / 2) (1 / 2) ×ˢ Set.Ici b)) :=
    (Complex.volume_preserving_equiv_real_prod.integrableOn_comp_preimage
      Complex.measurableEquivRealProd.measurableEmbedding).mpr hprod
  have hi : MeasureTheory.IntegrableOn (fun z : ℂ => Real.exp (-a * z.im))
      (UpperHalfPlane.coe '' ModularGroup.fd) := by
    apply hc.mono_set
    rintro _ ⟨z, hz, rfl⟩
    change z.re ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2) ∧ b ≤ z.im
    change z.re ∈ Set.Icc (-(1 : ℝ) / 2) (1 / 2) ∧ b ≤ z.im
    constructor
    · exact abs_le.mp hz.2
    · dsimp [b]
      have hsq := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hz
      have hpos := z.im_pos
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg (3 : ℝ)]
  have ht := (UpperHalfPlane.measurableEmbedding_coe.integrableOn_iff_comap
    (Set.image_subset_range UpperHalfPlane.coe ModularGroup.fd)).mp hi
  simpa only [Set.preimage_image_eq _ UpperHalfPlane.coe_injective, Function.comp_def,
    UpperHalfPlane.coe_im] using ht
  simpa only [Set.preimage_image_eq _ UpperHalfPlane.coe_injective, Function.comp_def] using ht
/-- The Petersson integrand of two weight-two cusp forms is integrable on each
integral translate of the standard modular fundamental domain. -/
theorem f036cc6b1f_pic_translated_integrable
    (Δ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Δ.FiniteIndex]
    (r : Matrix.SpecialLinearGroup (Fin 2) ℤ) (f g : CuspForm Δ 2) :
    MeasureTheory.IntegrableOn (UpperHalfPlane.petersson 2 f g)
      ((fun z : UpperHalfPlane => r • z) '' ModularGroup.fd)
      (MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane) := by
  -- Translation preserves the arithmetic cusp conditions.
  have : (ConjAct.toConjAct (r : GL (Fin 2) ℝ)⁻¹ •
      (Δ : Subgroup (GL (Fin 2) ℝ))).IsArithmetic := by
    simpa [(show Rat.castHom ℝ = algebraMap ℚ ℝ by rfl), map_inv, map_mapGL]
      using! Subgroup.IsArithmetic.conj (Δ : Subgroup (GL (Fin 2) ℝ)) (mapGL ℚ r)⁻¹
  let u := CuspForm.translate f r
  let v := CuspForm.translate g r
  obtain ⟨a, ha, hu⟩ := CuspFormClass.exp_decay_atImInfty' u
  obtain ⟨b, hb, hv⟩ := CuspFormClass.exp_decay_atImInfty' v
  have huv : (fun z : UpperHalfPlane => u z * v z)
      =O[atImInfty] (fun z => Real.exp (-(a + b) * z.im)) := by
    apply (hu.mul hv).congr_right
    intro z
    rw [← Real.exp_add]
    congr 1
    ring
  obtain ⟨C, hC, hbound⟩ := huv.exists_pos
  obtain ⟨Y, hY⟩ := (atImInfty_mem _).mp hbound.bound
  have hint : IntegrableOn (petersson 2 u v) ModularGroup.fd
      (volume : Measure UpperHalfPlane) := by
    apply f036cc6b1f_tdi_petersson_integrable_of_exp_product_bound
      u v (a + b) C Y (ModularFormClass.continuous u) (ModularFormClass.continuous v)
      (add_pos ha hb) hC.le
    intro z hz
    simpa only [Set.mem_ofPred_eq, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hY z hz
  -- The SL₂ action preserves hyperbolic volume, and Petersson covariance
  -- identifies the pullback with the integrand of the translated forms.
  have hpres : MeasurePreserving (fun z : UpperHalfPlane => r • z)
      (volume : Measure UpperHalfPlane) volume :=
    measurePreserving_smul (r : GL (Fin 2) ℝ) volume
  have hemb : MeasurableEmbedding (fun z : UpperHalfPlane => r • z) :=
    measurableEmbedding_const_smul (r : GL (Fin 2) ℝ)
  apply (hpres.integrableOn_image hemb).mpr
  convert hint using 1
  ext z
  exact (petersson_slash_SL 2 f g r z).symm

end Submission
theorem Submission.f036cc6b1f_pic_mec_invariant_conull_core :
    ∀ (Δ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) (S : Set UpperHalfPlane),
      MeasurableSet S →
      (∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane), z ∈ S) →
      ∃ X : Set UpperHalfPlane, MeasurableSet X ∧
        (∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane), z ∈ X) ∧
        X ⊆ S ∧ (∀ (γ : Δ) (z : UpperHalfPlane),
          (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) • z ∈ X ↔ z ∈ X) := by
  intro Δ S hS hSae
  have : Countable (Matrix.SpecialLinearGroup (Fin 2) ℤ) :=
    Function.Injective.countable (β := Fin 2 → Fin 2 → ℤ)
      (f := fun g : Matrix.SpecialLinearGroup (Fin 2) ℤ => (g.1 : Fin 2 → Fin 2 → ℤ))
      Subtype.val_injective
  have hpres (γ : Δ) : MeasureTheory.MeasurePreserving
      (fun z : UpperHalfPlane => (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) • z)
      MeasureTheory.volume MeasureTheory.volume := by
    change MeasureTheory.MeasurePreserving
      (fun z : UpperHalfPlane =>
        Matrix.SpecialLinearGroup.mapGL ℝ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) • z)
      MeasureTheory.volume MeasureTheory.volume
    exact MeasureTheory.measurePreserving_smul _ _
  let X : Set UpperHalfPlane :=
    ⋂ γ : Δ, (fun z : UpperHalfPlane =>
      (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) • z) ⁻¹' S
  have hstable (γ : Δ) (z : UpperHalfPlane) (hz : z ∈ X) :
      (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) • z ∈ X := by
    refine Set.mem_iInter.mpr fun δ => ?_
    have h := Set.mem_iInter.mp hz (δ * γ)
    simpa only [Set.mem_preimage, Subgroup.coe_mul, mul_smul] using h
  refine ⟨X, MeasurableSet.iInter (fun γ => hS.preimage (hpres γ).measurable),
    ?_, ?_, ?_⟩
  · exact (MeasureTheory.ae_all_iff.mpr fun γ =>
      (hpres γ).quasiMeasurePreserving.ae hSae).mono fun z hz => Set.mem_iInter.mpr hz
  · intro z hz
    have h := Set.mem_iInter.mp hz (1 : Δ)
    simpa only [Set.mem_preimage, Subgroup.coe_one, one_smul] using h
  · intro γ z
    constructor
    · intro hz
      simpa only [Subgroup.coe_inv, inv_smul_smul] using
        hstable γ⁻¹ ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) • z) hz
    · exact hstable γ z
theorem Submission.f036cc6b1f_pic_psp_sign_transversal :
    ∀ (Δ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)),
      (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) ∈ Δ →
      ∃ L : Set Δ,
        (∀ δ : Δ, ∃ γ : Δ, γ ∈ L ∧
          ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) =
              (δ : Matrix.SpecialLinearGroup (Fin 2) ℤ) ∨
            (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) =
              -(δ : Matrix.SpecialLinearGroup (Fin 2) ℤ))) ∧
        (∀ γ : Δ, γ ∈ L → ∀ η : Δ, η ∈ L →
          ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) =
              (η : Matrix.SpecialLinearGroup (Fin 2) ℤ) ∨
            (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) =
              -(η : Matrix.SpecialLinearGroup (Fin 2) ℤ)) → γ = η) := by
  classical
  intro Δ _hΔ
  let s : Setoid Δ :=
    { r := fun γ η =>
        (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) =
            (η : Matrix.SpecialLinearGroup (Fin 2) ℤ) ∨
          (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) =
            -(η : Matrix.SpecialLinearGroup (Fin 2) ℤ)
      iseqv := ⟨fun _ => Or.inl rfl, by
        intro γ η h
        rcases h with h | h
        · exact Or.inl h.symm
        · exact Or.inr (by rw [h, neg_neg]), by
        intro γ η ξ hγη hηξ
        rcases hγη with hγη | hγη <;> rcases hηξ with hηξ | hηξ
        · exact Or.inl (hγη.trans hηξ)
        · exact Or.inr (hγη.trans hηξ)
        · exact Or.inr (by rw [hγη, hηξ])
        · exact Or.inl (by rw [hγη, hηξ, neg_neg])⟩ }
  refine ⟨Set.range (Quotient.out (s := s)), ?_, ?_⟩
  · intro δ
    refine ⟨(Quotient.mk s δ).out, ⟨Quotient.mk s δ, rfl⟩, ?_⟩
    exact Quotient.exact (Quotient.out_eq (Quotient.mk s δ))
  · rintro γ ⟨c, rfl⟩ η ⟨d, rfl⟩ h
    have heq : Quotient.mk s c.out = Quotient.mk s d.out := Quotient.sound h
    have hcd : c = d := by simpa only [Quotient.out_eq] using heq
    exact congrArg (Quotient.out (s := s)) hcd
theorem Submission.f036cc6b1f_pic_psp_measurable_slice_partition :
    ∀ (Δ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) (L : Set Δ) (P S X : Set UpperHalfPlane), MeasurableSet P → MeasurableSet S → MeasurableSet X → (∀ δ : Δ, ∃ γ : Δ, γ ∈ L ∧ ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (δ : Matrix.SpecialLinearGroup (Fin 2) ℤ) ∨ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) = -(δ : Matrix.SpecialLinearGroup (Fin 2) ℤ))) → (∀ γ : Δ, γ ∈ L → ∀ η : Δ, η ∈ L → ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (η : Matrix.SpecialLinearGroup (Fin 2) ℤ) ∨ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) = -(η : Matrix.SpecialLinearGroup (Fin 2) ℤ)) → γ = η) → (∀ z ∈ X, ∃ r : Matrix.SpecialLinearGroup (Fin 2) ℤ, r ∈ Δ ∧ r • z ∈ S ∧ ∀ δ : Matrix.SpecialLinearGroup (Fin 2) ℤ, δ ∈ Δ → δ • z ∈ S → δ = r ∨ δ = -r) → let C : Δ → Set UpperHalfPlane := fun γ => {z | γ ∈ L ∧ z ∈ P ∩ X ∧ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) • z ∈ S}; (∀ γ, MeasurableSet (C γ)) ∧ Pairwise (fun γ η => Disjoint (C γ) (C η)) ∧ (⋃ γ, C γ) = P ∩ X := by
  intro Δ L P S X hP hS hX hcover huniq horbit
  dsimp only
  constructor
  · intro γ
    by_cases hγ : γ ∈ L
    · have hcont : Continuous (fun z : UpperHalfPlane =>
          (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) • z) := by
        change Continuous (fun z : UpperHalfPlane =>
          Matrix.SpecialLinearGroup.mapGL ℝ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) • z)
        exact continuous_const_smul _
      simpa only [hγ, true_and, Set.inter_def, Set.preimage, Set.mem_ofPred_eq] using
        (hP.inter hX).inter (hS.preimage hcont.measurable)
    · simpa only [hγ, false_and, Set.ofPred_false] using
        (MeasurableSet.empty : MeasurableSet (∅ : Set UpperHalfPlane))
  · constructor
    · intro γ η hne
      apply Set.disjoint_left.mpr
      intro z hzγ hzη
      obtain ⟨r, _, _, hr⟩ := horbit z hzγ.2.1.2
      apply hne
      apply huniq γ hzγ.1 η hzη.1
      rcases hr (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) γ.property hzγ.2.2 with hg | hg <;>
        rcases hr (η : Matrix.SpecialLinearGroup (Fin 2) ℤ) η.property hzη.2.2 with he | he
      · exact Or.inl (hg.trans he.symm)
      · exact Or.inr (by rw [hg, he, neg_neg])
      · exact Or.inr (by rw [hg, he])
      · exact Or.inl (hg.trans he.symm)
    · apply Set.Subset.antisymm
      · intro z hz
        obtain ⟨γ, hγ⟩ := Set.mem_iUnion.mp hz
        exact hγ.2.1
      · intro z hz
        obtain ⟨r, hr, hrs, _⟩ := horbit z hz.2
        obtain ⟨γ, hγ, hsgn⟩ := hcover ⟨r, hr⟩
        apply Set.mem_iUnion.mpr
        refine ⟨γ, hγ, hz, ?_⟩
        rcases hsgn with hsgn | hsgn
        · simpa only [hsgn] using hrs
        · simpa only [hsgn, ModularGroup.SL_neg_smul] using hrs

namespace Submission

theorem f036cc6b1f_pic_mec_pointwise_sign_partition
    (Δ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) (E F X : Set UpperHalfPlane)
    (hneg : (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) ∈ Δ)
    (hE : MeasurableSet E) (hF : MeasurableSet F) (hX : MeasurableSet X)
    (hinv : ∀ (γ : Δ) (z : UpperHalfPlane),
      (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) • z ∈ X ↔ z ∈ X)
    (hrep : ∀ S : Set UpperHalfPlane, (S = E ∨ S = F) → ∀ z ∈ X,
      ∃ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, γ ∈ Δ ∧ γ • z ∈ S ∧
        ∀ δ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
          δ ∈ Δ → δ • z ∈ S → δ = γ ∨ δ = -γ) :
    ∃ A B : Δ → Set UpperHalfPlane,
      (∀ γ, MeasurableSet (A γ)) ∧ (∀ γ, MeasurableSet (B γ)) ∧
      Pairwise (fun γ δ => Disjoint (A γ) (A δ)) ∧
      Pairwise (fun γ δ => Disjoint (B γ) (B δ)) ∧
      (⋃ γ, A γ) = E ∩ X ∧ (⋃ γ, B γ) = F ∩ X ∧
      (∀ γ : Δ, (fun z : UpperHalfPlane =>
        (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ)⁻¹ • z) '' (A γ) = B γ) := by
  classical
  obtain ⟨L, hcover, hunique⟩ := f036cc6b1f_pic_psp_sign_transversal Δ hneg
  -- Inversion carries a sign transversal to a sign transversal.
  let Linv : Set Δ := {γ | γ⁻¹ ∈ L}
  have hcoverInv : ∀ δ : Δ, ∃ γ : Δ, γ ∈ Linv ∧
      ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) = δ ∨
        (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) = -(δ : Matrix.SpecialLinearGroup (Fin 2) ℤ)) := by
    intro δ
    obtain ⟨γ, hγ, hsign⟩ := hcover δ⁻¹
    refine ⟨γ⁻¹, ?_, ?_⟩
    · simpa only [Linv, Set.mem_ofPred_eq, inv_inv] using hγ
    · rcases hsign with hsign | hsign
      · left
        simpa only [Subgroup.coe_inv, inv_inv] using congrArg Inv.inv hsign
      · right
        simpa only [Subgroup.coe_inv, inv_neg, inv_inv] using congrArg Inv.inv hsign
  have huniqueInv : ∀ γ : Δ, γ ∈ Linv → ∀ η : Δ, η ∈ Linv →
      ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) = η ∨
        (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) = -(η : Matrix.SpecialLinearGroup (Fin 2) ℤ)) →
      γ = η := by
    intro γ hγ η hη hsign
    apply inv_injective
    apply hunique γ⁻¹ hγ η⁻¹ hη
    rcases hsign with hsign | hsign
    · left
      simpa only [Subgroup.coe_inv] using congrArg Inv.inv hsign
    · right
      simpa only [Subgroup.coe_inv, inv_neg] using congrArg Inv.inv hsign
  let C : Δ → Set UpperHalfPlane := fun γ =>
    {z | γ ∈ Linv ∧ z ∈ E ∩ X ∧ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) • z ∈ F}
  let A : Δ → Set UpperHalfPlane := fun γ => C γ⁻¹
  let B : Δ → Set UpperHalfPlane := fun γ =>
    {z | γ ∈ L ∧ z ∈ F ∩ X ∧ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) • z ∈ E}
  obtain ⟨hCmeas, hCdisj, hCunion⟩ :=
    f036cc6b1f_pic_psp_measurable_slice_partition Δ Linv E F X hE hF hX
      hcoverInv huniqueInv (hrep F (Or.inr rfl))
  obtain ⟨hBmeas, hBdisj, hBunion⟩ :=
    f036cc6b1f_pic_psp_measurable_slice_partition Δ L F E X hF hE hX
      hcover hunique (hrep E (Or.inl rfl))
  refine ⟨A, B, (fun γ => hCmeas γ⁻¹), hBmeas, ?_, hBdisj, ?_, hBunion, ?_⟩
  · intro γ η hne
    exact hCdisj (fun h => hne (inv_injective h))
  · calc
      (⋃ γ, A γ) = ⋃ γ, C γ :=
        Set.iUnion_congr_of_surjective Inv.inv inv_surjective (fun _ => rfl)
      _ = E ∩ X := hCunion
  · intro γ
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      change (γ⁻¹)⁻¹ ∈ L ∧ z ∈ E ∩ X ∧
        ((γ⁻¹ : Δ) : Matrix.SpecialLinearGroup (Fin 2) ℤ) • z ∈ F at hz
      simp only [inv_inv, Subgroup.coe_inv] at hz
      refine ⟨hz.1, ⟨hz.2.2, (hinv γ⁻¹ z).2 hz.2.1.2⟩, ?_⟩
      simpa only [smul_inv_smul] using hz.2.1.1
    · intro hy
      change γ ∈ L ∧ y ∈ F ∩ X ∧
        (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) • y ∈ E at hy
      refine ⟨(γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) • y, ?_, inv_smul_smul _ _⟩
      change (γ⁻¹)⁻¹ ∈ L ∧
        (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) • y ∈ E ∩ X ∧
        ((γ⁻¹ : Δ) : Matrix.SpecialLinearGroup (Fin 2) ℤ) •
          ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) • y) ∈ F
      simp only [inv_inv, Subgroup.coe_inv, inv_smul_smul]
      exact ⟨hy.1, ⟨hy.2.2, (hinv γ y).2 hy.2.1.2⟩, hy.2.1.1⟩

end Submission


namespace Submission

/-- Measurable equidecomposition of two domains with representatives unique up to sign. -/
theorem f036cc6b1f_pic_dt_measurable_equidecomposition
    (Δ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) (E F : Set UpperHalfPlane)
    (hneg : (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) ∈ Δ)
    (hE : MeasurableSet E) (hF : MeasurableSet F)
    (hEae : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane),
      ∃ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
        γ ∈ Δ ∧ γ • z ∈ E ∧ ∀ δ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
          δ ∈ Δ → δ • z ∈ E → δ = γ ∨ δ = -γ)
    (hFae : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane),
      ∃ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
        γ ∈ Δ ∧ γ • z ∈ F ∧ ∀ δ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
          δ ∈ Δ → δ • z ∈ F → δ = γ ∨ δ = -γ) :
    ∃ A B : Δ → Set UpperHalfPlane,
      (∀ γ, MeasurableSet (A γ)) ∧ (∀ γ, MeasurableSet (B γ)) ∧
      Pairwise (fun γ δ => Disjoint (A γ) (A δ)) ∧
      Pairwise (fun γ δ => Disjoint (B γ) (B δ)) ∧
      (∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane),
        z ∈ E ↔ z ∈ ⋃ γ, A γ) ∧
      (∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane),
        z ∈ F ↔ z ∈ ⋃ γ, B γ) ∧
      (∀ γ : Δ,
        (fun z : UpperHalfPlane => (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ)⁻¹ • z) ''
          A γ = B γ) := by
  classical
  -- The representative predicates are measurable by countability of the matrix group.
  have : Countable (Matrix.SpecialLinearGroup (Fin 2) ℤ) := by
    change Countable {g : Fin 2 → Fin 2 → ℤ // Matrix.det g = 1}
    infer_instance
  have hsmul (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
      Measurable (fun z : UpperHalfPlane => γ • z) :=
    (continuous_const_smul (Matrix.SpecialLinearGroup.mapGL ℝ γ)).measurable
  let R : Set UpperHalfPlane → Set UpperHalfPlane := fun S =>
    {z | ∃ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      γ ∈ Δ ∧ γ • z ∈ S ∧ ∀ δ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
        δ ∈ Δ → δ • z ∈ S → δ = γ ∨ δ = -γ}
  have hR (S : Set UpperHalfPlane) (hS : MeasurableSet S) : MeasurableSet (R S) := by
    dsimp only [R]
    rw [Set.ofPred_exists]
    refine MeasurableSet.iUnion fun γ => ?_
    refine (MeasurableSet.const (γ ∈ Δ)).inter ((hS.preimage (hsmul γ)).inter ?_)
    change MeasurableSet {z : UpperHalfPlane |
      ∀ δ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
        δ ∈ Δ → δ • z ∈ S → δ = γ ∨ δ = -γ}
    rw [Set.ofPred_forall]
    refine MeasurableSet.iInter fun δ => ?_
    exact (MeasurableSet.const (δ ∈ Δ)).imp
      ((hS.preimage (hsmul δ)).imp (MeasurableSet.const (δ = γ ∨ δ = -γ)))
  have hRae : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane),
      z ∈ R E ∩ R F := hEae.and hFae
  -- Restrict to the invariant conull core where both predicates hold pointwise.
  obtain ⟨X, hX, hXae, hXR, hXinv⟩ :=
    Submission.f036cc6b1f_pic_mec_invariant_conull_core Δ (R E ∩ R F)
      ((hR E hE).inter (hR F hF)) hRae
  obtain ⟨A, B, hA, hB, hAdisj, hBdisj, hAunion, hBunion, hAB⟩ :=
    Submission.f036cc6b1f_pic_mec_pointwise_sign_partition Δ E F X
      hneg hE hF hX hXinv (by
        rintro S (rfl | rfl) z hz
        · exact (hXR hz).1
        · exact (hXR hz).2)
  -- Conullness upgrades the exact covers of the intersections to almost-everywhere covers.
  refine ⟨A, B, hA, hB, hAdisj, hBdisj, ?_, ?_, hAB⟩
  · filter_upwards [hXae] with z hz
    rw [hAunion]
    exact ⟨fun h => ⟨h, hz⟩, fun h => h.1⟩
  · filter_upwards [hXae] with z hz
    rw [hBunion]
    exact ⟨fun h => ⟨h, hz⟩, fun h => h.1⟩

end Submission

theorem Submission.f036cc6b1f_pic_dt_integral_of_equidecomposition :
    ∀ (α ι : Type) [MeasurableSpace α] [Countable ι]
      (μ : MeasureTheory.Measure α) (E F : Set α) (A B : ι → Set α) (T : ι → α → α),
      MeasurableSet E → MeasurableSet F →
      (∀ i, MeasurableSet (A i)) → (∀ i, MeasurableSet (B i)) →
      Pairwise (fun i j => Disjoint (A i) (A j)) →
      Pairwise (fun i j => Disjoint (B i) (B j)) →
      (∀ᵐ x ∂μ, x ∈ E ↔ x ∈ ⋃ i, A i) →
      (∀ᵐ x ∂μ, x ∈ F ↔ x ∈ ⋃ i, B i) →
      (∀ i, MeasurableEmbedding (T i)) →
      (∀ i, MeasureTheory.MeasurePreserving (T i) μ μ) →
      (∀ i, T i '' A i = B i) → ∀ φ : α → ℂ,
      MeasureTheory.StronglyMeasurable φ →
      (∀ i, ∀ x ∈ A i, φ (T i x) = φ x) →
      MeasureTheory.IntegrableOn φ E μ →
      MeasureTheory.IntegrableOn φ F μ ∧ MeasureTheory.integral (μ.restrict E) φ = MeasureTheory.integral (μ.restrict F) φ := by
  intro α ι _ _ μ E F A B T _hE _hF hA hB hdA hdB hEU hFV hemb hpres himage
    φ hφ hinv hφE
  have hμE : μ.restrict E = μ.restrict (⋃ i, A i) :=
    MeasureTheory.Measure.restrict_congr_set (hEU.mono fun _ hx => propext hx)
  have hμF : μ.restrict F = μ.restrict (⋃ i, B i) :=
    MeasureTheory.Measure.restrict_congr_set (hFV.mono fun _ hx => propext hx)
  rw [MeasureTheory.IntegrableOn, hμE] at hφE
  change MeasureTheory.Integrable φ (μ.restrict F) ∧ _
  rw [hμE, hμF]
  have htransport : ∀ i, MeasureTheory.MeasurePreserving (T i) (μ.restrict (A i))
      (μ.restrict (B i)) := by
    intro i
    simpa only [himage i] using (hpres i).restrict_image_emb (hemb i) (A i)
  have hnorm : ∀ i,
      (∫⁻ x in A i, ENNReal.ofReal ‖φ x‖ ∂μ) =
        ∫⁻ x in B i, ENNReal.ofReal ‖φ x‖ ∂μ := by
    intro i
    calc
      (∫⁻ x in A i, ENNReal.ofReal ‖φ x‖ ∂μ) =
          ∫⁻ x in A i, ENNReal.ofReal ‖φ (T i x)‖ ∂μ :=
        MeasureTheory.setLIntegral_congr_fun (hA i) (fun x hx => by rw [hinv i x hx])
      _ = ∫⁻ x in B i, ENNReal.ofReal ‖φ x‖ ∂μ :=
        (htransport i).lintegral_comp_emb (hemb i) (fun x => ENNReal.ofReal ‖φ x‖)
  have hnormUnion :
      (∫⁻ x in ⋃ i, A i, ENNReal.ofReal ‖φ x‖ ∂μ) =
        ∫⁻ x in ⋃ i, B i, ENNReal.ofReal ‖φ x‖ ∂μ := by
    rw [MeasureTheory.lintegral_iUnion hA hdA, MeasureTheory.lintegral_iUnion hB hdB]
    exact tsum_congr hnorm
  have hφB : MeasureTheory.IntegrableOn φ (⋃ i, B i) μ := by
    refine ⟨hφ.aestronglyMeasurable, (MeasureTheory.hasFiniteIntegral_iff_norm φ).2 ?_⟩
    rw [← hnormUnion]
    exact (MeasureTheory.hasFiniteIntegral_iff_norm φ).1 hφE.2
  refine ⟨hφB, ?_⟩
  rw [MeasureTheory.integral_iUnion hA hdA hφE, MeasureTheory.integral_iUnion hB hdB hφB]
  apply tsum_congr
  intro i
  calc
    (∫ x in A i, φ x ∂μ) = ∫ x in A i, φ (T i x) ∂μ :=
      MeasureTheory.setIntegral_congr_fun (hA i) (fun x hx => (hinv i x hx).symm)
    _ = ∫ x in B i, φ x ∂μ := (htransport i).integral_comp (hemb i) φ


namespace Submission

/-- Transfer integrability and the integral between effective fundamental domains. -/
theorem f036cc6b1f_pic_domain_transfer
    (Δ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) (E F : Set UpperHalfPlane)
    (hneg : (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) ∈ Δ)
    (hE : MeasurableSet E) (hF : MeasurableSet F)
    (hrepE : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane),
      ∃ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
        γ ∈ Δ ∧ γ • z ∈ E ∧ ∀ δ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
          δ ∈ Δ → δ • z ∈ E → δ = γ ∨ δ = -γ)
    (hrepF : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane),
      ∃ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
        γ ∈ Δ ∧ γ • z ∈ F ∧ ∀ δ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
          δ ∈ Δ → δ • z ∈ F → δ = γ ∨ δ = -γ)
    (φ : UpperHalfPlane → ℂ) (hφ : Continuous φ)
    (hφinv : ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, γ ∈ Δ →
      ∀ z : UpperHalfPlane, φ (γ • z) = φ z)
    (hφE : MeasureTheory.IntegrableOn φ E
      (MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane)) :
    MeasureTheory.IntegrableOn φ F
        (MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane) ∧
      MeasureTheory.integral
          ((MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane).restrict E) φ =
        MeasureTheory.integral
          ((MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane).restrict F) φ := by
  have : Countable (Matrix.SpecialLinearGroup (Fin 2) ℤ) :=
    inferInstanceAs (Countable {A : Fin 2 → Fin 2 → ℤ // Matrix.det A = 1})
  obtain ⟨A, B, hA, hB, hdisjA, hdisjB, hcoverE, hcoverF, hAB⟩ :=
    f036cc6b1f_pic_dt_measurable_equidecomposition Δ E F hneg hE hF hrepE hrepF
  refine f036cc6b1f_pic_dt_integral_of_equidecomposition UpperHalfPlane Δ
    MeasureTheory.volume E F A B
    (fun γ z => (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ)⁻¹ • z)
    hE hF hA hB hdisjA hdisjB hcoverE hcoverF ?_ ?_ hAB φ
    hφ.stronglyMeasurable ?_ hφE
  · intro γ
    -- The special linear action is the canonical general linear action via `mapGL`.
    change MeasurableEmbedding (fun z : UpperHalfPlane =>
      Matrix.SpecialLinearGroup.mapGL ℝ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ)⁻¹ • z)
    exact measurableEmbedding_const_smul _
  · intro γ
    change MeasureTheory.MeasurePreserving (fun z : UpperHalfPlane =>
      Matrix.SpecialLinearGroup.mapGL ℝ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ)⁻¹ • z)
      MeasureTheory.volume MeasureTheory.volume
    exact MeasureTheory.measurePreserving_smul _ _
  · intro γ z _
    exact hφinv _ (Δ.inv_mem γ.property) z

end Submission
theorem Submission.f036cc6b1f_pic_dd_ae_orbit_zero :
    ∀ (Δ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) (E : Set UpperHalfPlane) (A : UpperHalfPlane → ℝ), MeasurableSet E → Measurable A → (∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane), ∃ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, γ ∈ Δ ∧ γ • z ∈ E) → (∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), γ ∈ Δ → ∀ z : UpperHalfPlane, A (γ • z) = A z) → (∀ᵐ z ∂((MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane).restrict E), A z = 0) → ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane), A z = 0 := by
  intro Δ E A hE _hA hcover hinv hzero
  have : Countable (Matrix (Fin 2) (Fin 2) ℤ) :=
    inferInstanceAs (Countable (Fin 2 → Fin 2 → ℤ))
  have : Countable (Matrix.SpecialLinearGroup (Fin 2) ℤ) :=
    inferInstanceAs (Countable {g : Matrix (Fin 2) (Fin 2) ℤ // g.det = 1})
  have hzero' : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane),
      z ∈ E → A z = 0 :=
    (MeasureTheory.ae_restrict_iff' hE).mp hzero
  have htranslate : ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane),
        γ • z ∈ E → A (γ • z) = 0 := by
    intro γ
    exact (MeasureTheory.measurePreserving_smul (Matrix.SpecialLinearGroup.mapGL ℝ γ)
      (MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane)).quasiMeasurePreserving.ae
        hzero'
  have hall : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane),
      ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, γ • z ∈ E → A (γ • z) = 0 :=
    MeasureTheory.ae_all_iff.mpr htranslate
  filter_upwards [hcover, hall] with z hz hzall
  obtain ⟨γ, hγ, hzE⟩ := hz
  exact (hinv γ hγ z).symm.trans (hzall γ hzE)
theorem Submission.f036cc6b1f_pic_dd_open_pos :
    MeasureTheory.Measure.IsOpenPosMeasure
      (MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane) := by
  let : MeasureTheory.Measure.IsOpenPosMeasure
      ((MeasureTheory.volume : MeasureTheory.Measure ℂ).comap UpperHalfPlane.coe) :=
    MeasureTheory.Measure.IsOpenPosMeasure.comap _ UpperHalfPlane.isOpenEmbedding_coe
  rw [UpperHalfPlane.volume_def]
  apply MeasureTheory.Measure.AbsolutelyContinuous.isOpenPosMeasure
    (μ := (MeasureTheory.volume : MeasureTheory.Measure ℂ).comap UpperHalfPlane.coe)
  apply MeasureTheory.withDensity_absolutelyContinuous'
  · have hw : Continuous (fun z : UpperHalfPlane ↦
        (1 / NNReal.mk z.im z.im_pos.le : NNReal) ^ 2) := by
      refine .pow (.div₀ continuous_const ?_ ?_) _
      · exact UpperHalfPlane.continuous_im.subtype_mk _
      · exact fun z ↦ NNReal.ne_iff.mp z.im_ne_zero
    exact hw.measurable.coe_nnreal_ennreal.aemeasurable
  · exact Filter.Eventually.of_forall fun z ↦
      ENNReal.coe_ne_zero.mpr (pow_ne_zero 2
        (div_ne_zero one_ne_zero (NNReal.ne_iff.mp z.im_ne_zero)))
open MeasureTheory

namespace Submission

/-- The boundary of the standard modular domain is measurable and has hyperbolic volume zero. -/
theorem f036cc6b1f_pc_ed_aoi_boundary_null :
    MeasurableSet (ModularGroup.fd \ ModularGroup.fdo) ∧
      (volume : Measure UpperHalfPlane) (ModularGroup.fd \ ModularGroup.fdo) = 0 := by
  refine ⟨ModularGroup.isClosed_fd.measurableSet.diff
    ModularGroup.isOpen_fdo.measurableSet, ?_⟩
  have hcircle : (volume : Measure (ℝ × ℝ)) {p | p.1 ^ 2 + p.2 ^ 2 = 1} = 0 := by
    apply Measure.measure_prod_null_of_ae_null (μ := (volume : Measure ℝ))
      (ν := (volume : Measure ℝ))
      (isClosed_eq (by fun_prop) continuous_const).measurableSet
    filter_upwards [] with x
    by_cases h : ∃ y : ℝ, x ^ 2 + y ^ 2 = 1
    · obtain ⟨y₀, hy₀⟩ := h
      apply measure_mono_null (t := {y₀, -y₀}) ?_
        ((Set.toFinite {y₀, -y₀}).measure_zero volume)
      intro y hy
      change x ^ 2 + y ^ 2 = 1 at hy
      have hfactor : (y - y₀) * (y + y₀) = 0 := by nlinarith
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rcases mul_eq_zero.mp hfactor with hpos | hneg
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    · have hempty : Prod.mk x ⁻¹' {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 = 1} = ∅ := by
        ext y
        simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        exact fun hy => h ⟨y, hy⟩
      simp [hempty]
  have hline (c : ℝ) : (volume : Measure (ℝ × ℝ)) {p | p.1 = c} = 0 := by
    have hset : {p : ℝ × ℝ | p.1 = c} = ({c} : Set ℝ) ×ˢ Set.univ := by
      ext p
      simp
    rw [hset, Measure.volume_eq_prod, Measure.prod_prod]
    simp
  have hplanar : (volume : Measure ℂ)
      {z | Complex.normSq z = 1 ∨ z.re = 1 / 2 ∨ z.re = -(1 / 2)} = 0 := by
    have hnull : (volume : Measure (ℝ × ℝ))
        ({p | p.1 ^ 2 + p.2 ^ 2 = 1} ∪ {p | p.1 = 1 / 2} ∪
          {p | p.1 = -(1 / 2)}) = 0 :=
      measure_union_null (measure_union_null hcircle (hline _)) (hline _)
    have hpre := Complex.volume_preserving_equiv_real_prod.measure_preimage_equiv
      ({p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 = 1} ∪ {p | p.1 = 1 / 2} ∪
        {p | p.1 = -(1 / 2)})
    rw [hnull] at hpre
    simpa only [Set.preimage_union, Set.preimage_ofPred_eq,
      Complex.measurableEquivRealProd_apply, Complex.normSq_apply, pow_two,
      Set.ofPred_or, Set.union_assoc] using hpre
  have himage : (volume : Measure ℂ)
      (UpperHalfPlane.coe '' (ModularGroup.fd \ ModularGroup.fdo)) = 0 := by
    apply measure_mono_null ?_ hplanar
    rintro z ⟨w, ⟨hw, hwo⟩, rfl⟩
    change 1 ≤ Complex.normSq (w : ℂ) ∧ |w.re| ≤ (1 : ℝ) / 2 at hw
    change ¬ (1 < Complex.normSq (w : ℂ) ∧ |w.re| < (1 : ℝ) / 2) at hwo
    change Complex.normSq (w : ℂ) = 1 ∨ w.re = 1 / 2 ∨ w.re = -(1 / 2)
    by_cases hc : Complex.normSq (w : ℂ) = 1
    · exact Or.inl hc
    · have hr : |w.re| = (1 : ℝ) / 2 := by
        by_contra hn
        exact hwo ⟨lt_of_le_of_ne hw.1 (Ne.symm hc), lt_of_le_of_ne hw.2 hn⟩
      rcases le_or_gt 0 w.re with hp | hn
      · exact Or.inr (Or.inl (by simpa [abs_of_nonneg hp] using hr))
      · exact Or.inr (Or.inr (by rw [abs_of_neg hn] at hr; linarith))
  rw [UpperHalfPlane.volume_eq_lintegral, Measure.restrict_eq_zero.mpr himage]
  simp

end Submission

namespace Submission

/-- Almost every point has a modular orbit disjoint from a prescribed measurable null set. -/
theorem f036cc6b1f_pc_ed_aoi_null_orbit :
    ∀ s : Set UpperHalfPlane, MeasurableSet s →
      (MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane) s = 0 →
      ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane),
        ∀ a : Matrix.SpecialLinearGroup (Fin 2) ℤ, a • z ∉ s := by
  intro s hs hnull
  -- The determinant-one subtype of four integer entries is countable.
  let : Countable (Matrix.SpecialLinearGroup (Fin 2) ℤ) := by
    unfold Matrix.SpecialLinearGroup Matrix
    infer_instance
  apply MeasureTheory.ae_all_iff.mpr
  intro a
  -- The modular action is the restriction of the measure-invariant real GL action.
  change ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane),
    z ∉ (fun z : UpperHalfPlane => Matrix.SpecialLinearGroup.mapGL ℝ a • z) ⁻¹' s
  apply MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
  exact (MeasureTheory.SMulInvariantMeasure.measure_preimage_smul
    (μ := (MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane))
    (Matrix.SpecialLinearGroup.mapGL ℝ a) hs).trans hnull

/-- Almost every modular orbit avoids the boundary of the standard fundamental domain. -/
theorem f036cc6b1f_pc_ed_ae_orbit_interior :
    ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane),
      ∀ a : Matrix.SpecialLinearGroup (Fin 2) ℤ,
        a • z ∈ ModularGroup.fd → a • z ∈ ModularGroup.fdo := by
  exact (f036cc6b1f_pc_ed_aoi_null_orbit (ModularGroup.fd \ ModularGroup.fdo)
    f036cc6b1f_pc_ed_aoi_boundary_null.1 f036cc6b1f_pc_ed_aoi_boundary_null.2).mono
    fun _ hz a hfd => Classical.byContradiction fun hfdo => hz a ⟨hfd, hfdo⟩
namespace Submission

theorem f036cc6b1f_pc_ed_transversal_unique :
    ∀ (Δ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
      (R : Finset (Matrix.SpecialLinearGroup (Fin 2) ℤ)),
      (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) ∈ Δ →
      (∀ r ∈ R, ∀ s ∈ R, s * r⁻¹ ∈ Δ → s = r) →
      ∀ z : UpperHalfPlane,
      (∀ a : Matrix.SpecialLinearGroup (Fin 2) ℤ,
        a • z ∈ ModularGroup.fd → a • z ∈ ModularGroup.fdo) →
      let F : Set UpperHalfPlane :=
        ⋃ r ∈ R, (fun w : UpperHalfPlane => r • w) '' ModularGroup.fd
      ∀ γ δ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
        γ ∈ Δ → δ ∈ Δ → γ • z ∈ F → δ • z ∈ F → δ = γ ∨ δ = -γ := by
  intro Δ R hneg hR z hz F γ δ hγ hδ hγF hδF
  simp only [F, Set.mem_iUnion, Set.mem_image] at hγF hδF
  rcases hγF with ⟨r, hr, w, hw, hrw⟩
  rcases hδF with ⟨s, hs, v, hv, hsv⟩
  have hwz : (r⁻¹ * γ) • z = w := by
    rw [mul_smul, ← hrw, inv_smul_smul]
  have hwo : w ∈ ModularGroup.fdo := by
    have h := hz (r⁻¹ * γ) (by simpa only [hwz] using hw)
    simpa only [hwz] using h
  have haw : (s⁻¹ * (δ * γ⁻¹) * r) • w = v := by
    simp only [mul_smul, hrw, inv_smul_smul, ← hsv]
  have ha := ModularGroup.eq_one_or_neg_one_of_mem_fdo_mem_fd hwo
    (show (s⁻¹ * (δ * γ⁻¹) * r) • w ∈ ModularGroup.fd by
      simpa only [haw] using hv)
  have hq : δ * γ⁻¹ ∈ Δ := Δ.mul_mem hδ (Δ.inv_mem hγ)
  have hqeq : δ * γ⁻¹ = s * (s⁻¹ * (δ * γ⁻¹) * r) * r⁻¹ := by
    simp [mul_assoc]
  rcases ha with ha | ha
  · have heq : δ * γ⁻¹ = s * r⁻¹ := by
      simpa only [ha, mul_one] using hqeq
    have hsr : s = r := hR r hr s hs (heq ▸ hq)
    left
    have hcancel : δ * γ⁻¹ = 1 := by simpa only [hsr, mul_inv_cancel] using heq
    exact mul_inv_eq_one.mp hcancel
  · have heq : δ * γ⁻¹ = -(s * r⁻¹) := by
      simpa only [ha, mul_neg, mul_one, neg_mul] using hqeq
    have hsrmem : s * r⁻¹ ∈ Δ := by
      have h := Δ.mul_mem hneg hq
      simpa only [heq, neg_mul, one_mul, neg_neg] using h
    have hsr : s = r := hR r hr s hs hsrmem
    right
    have hcancel : δ * γ⁻¹ = -1 := by
      simpa only [hsr, mul_inv_cancel] using heq
    have h := congrArg (fun a => a * γ) hcancel
    simpa only [inv_mul_cancel_right, neg_mul, one_mul] using h

end Submission
