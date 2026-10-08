/-
Copyright 2026 Anthropic, PBC. Licensed under Apache-2.0; see LICENSE.
Source: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_CuspForm_span_heckeTLin_eigen_eq_top.lean
Modified: replaced the proof with sorry and removed P2M proof imports.
Requires the upstream Definitions modules and their dependencies.
-/

import Definitions.Def_ModularForm_HeckeOperatorForms
attribute [-instance] FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2
attribute [-simp] FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero

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
