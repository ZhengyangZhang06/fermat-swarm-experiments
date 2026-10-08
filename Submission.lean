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
      (Set.Icc (-(1 / 2 : ℝ)) (1 / 2)) := MeasureTheory.integrableOn_const
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
