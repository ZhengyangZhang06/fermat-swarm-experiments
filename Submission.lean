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

namespace Submission

theorem f036cc6b1f_pc_ed_aoi_null_orbit :
    ∀ s : Set UpperHalfPlane, MeasurableSet s →
      (MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane) s = 0 →
      ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane),
        ∀ a : Matrix.SpecialLinearGroup (Fin 2) ℤ, a • z ∉ s := by
  intro s hs hnull
  let : Countable (Matrix.SpecialLinearGroup (Fin 2) ℤ) := by
    unfold Matrix.SpecialLinearGroup Matrix
    infer_instance
  apply MeasureTheory.ae_all_iff.mpr
  intro a
  change ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane),
    z ∉ (fun z : UpperHalfPlane => Matrix.SpecialLinearGroup.mapGL ℝ a • z) ⁻¹' s
  apply MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
  exact (MeasureTheory.SMulInvariantMeasure.measure_preimage_smul
    (μ := (MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane))
    (Matrix.SpecialLinearGroup.mapGL ℝ a) hs).trans hnull

end Submission
