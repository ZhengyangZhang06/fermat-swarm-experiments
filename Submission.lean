/-
Copyright 2026 Anthropic, PBC. Licensed under Apache-2.0; see LICENSE.
Source: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_CuspForm_span_heckeTLin_eigen_eq_top.lean
Modified: replaced the proof with sorry and removed P2M proof imports.
Requires the upstream Definitions modules and their dependencies.
-/

import Definitions.Def_ModularForm_HeckeOperatorForms
attribute [-instance] FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2
attribute [-simp] FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero

namespace Submission

open MeasureTheory
open scoped ComplexConjugate

theorem f036cc6b1f_tdi_petersson_integrable_of_exp_product_bound
    (u v : UpperHalfPlane → ℂ) (a C Y : ℝ)
    (hu : Continuous u) (hv : Continuous v) (ha : 0 < a) (_hC : 0 ≤ C)
    (hbound : ∀ z : UpperHalfPlane, Y ≤ z.im →
      ‖u z * v z‖ ≤ C * Real.exp (-a * z.im)) :
    IntegrableOn (UpperHalfPlane.petersson 2 u v) ModularGroup.fd
      (volume : Measure UpperHalfPlane) := by
  let ν : Measure UpperHalfPlane := (volume : Measure ℂ).comap UpperHalfPlane.coe
  let W : UpperHalfPlane → ℂ := fun z ↦ conj (u z) * v z
  let L : ℝ := max 1 Y
  let D := ModularGroup.truncatedFundamentalDomain L
  let E := ModularGroup.fd ∩ {z : UpperHalfPlane | L < z.im}
  have hW : Continuous W := (Complex.continuous_conj.comp hu).mul hv
  -- The lower truncation is compact and planar measure is finite on compact sets.
  have hD : IntegrableOn W D ν :=
    hW.continuousOn.integrableOn_compact
      (ModularGroup.isCompact_truncatedFundamentalDomain L)
  have hEmeas : MeasurableSet E :=
    ModularGroup.isClosed_fd.measurableSet.inter
      (isOpen_lt continuous_const UpperHalfPlane.continuous_im).measurableSet
  -- On the tail, use precisely the supplied planar exponential-integrability interface.
  have hmajor : IntegrableOn (fun z : UpperHalfPlane ↦ C * Real.exp (-a * z.im)) E ν :=
    ((Submission.f036cc6b1f_tdi_planar_exp_integrable_fd a ha).mono_set
      Set.inter_subset_left).const_mul C
  have hE : IntegrableOn W E ν := by
    refine hmajor.mono' hW.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem hEmeas] with z hz
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
  have hplanar : IntegrableOn W ModularGroup.fd ν := by
    rw [← hpartition]
    exact hD.union hE
  -- Multiplication by the hyperbolic density cancels the weight-two factor.
  rw [IntegrableOn, UpperHalfPlane.volume_def,
    restrict_withDensity ModularGroup.isClosed_fd.measurableSet]
  have hdensity : Measurable (fun z : UpperHalfPlane ↦
      (1 / NNReal.mk z.im z.im_pos.le : NNReal) ^ 2) := by
    fun_prop
  rw [integrable_withDensity_iff_integrable_coe_smul hdensity]
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
