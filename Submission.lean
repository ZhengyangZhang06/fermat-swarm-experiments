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


open MeasureTheory in
theorem Submission.f036cc6b1f_pic_dt_integral_of_equidecomposition :
    ∀ (α ι : Type) [MeasurableSpace α] [Countable ι]
      (μ : Measure α) (E F : Set α) (A B : ι → Set α) (T : ι → α → α),
      MeasurableSet E → MeasurableSet F →
      (∀ i, MeasurableSet (A i)) → (∀ i, MeasurableSet (B i)) →
      Pairwise (fun i j => Disjoint (A i) (A j)) →
      Pairwise (fun i j => Disjoint (B i) (B j)) →
      (∀ᵐ x ∂μ, x ∈ E ↔ x ∈ ⋃ i, A i) →
      (∀ᵐ x ∂μ, x ∈ F ↔ x ∈ ⋃ i, B i) →
      (∀ i, MeasurableEmbedding (T i)) →
      (∀ i, MeasurePreserving (T i) μ μ) →
      (∀ i, T i '' A i = B i) → ∀ φ : α → ℂ,
      StronglyMeasurable φ →
      (∀ i, ∀ x ∈ A i, φ (T i x) = φ x) →
      IntegrableOn φ E μ →
      IntegrableOn φ F μ ∧ integral (μ.restrict E) φ = integral (μ.restrict F) φ := by
  intro α ι _ _ μ E F A B T _hE _hF hA hB hdA hdB hEU hFV hemb hpres himage
    φ hφ hinv hφE
  have hμE : μ.restrict E = μ.restrict (⋃ i, A i) :=
    Measure.restrict_congr_set (hEU.mono fun _ hx => propext hx)
  have hμF : μ.restrict F = μ.restrict (⋃ i, B i) :=
    Measure.restrict_congr_set (hFV.mono fun _ hx => propext hx)
  rw [IntegrableOn, hμE] at hφE
  change Integrable φ (μ.restrict F) ∧ _
  rw [hμE, hμF]
  have htransport : ∀ i, MeasurePreserving (T i) (μ.restrict (A i))
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
        setLIntegral_congr_fun (hA i) (fun x hx => by rw [hinv i x hx])
      _ = ∫⁻ x in B i, ENNReal.ofReal ‖φ x‖ ∂μ :=
        (htransport i).lintegral_comp_emb (hemb i) (fun x => ENNReal.ofReal ‖φ x‖)
  have hnormUnion :
      (∫⁻ x in ⋃ i, A i, ENNReal.ofReal ‖φ x‖ ∂μ) =
        ∫⁻ x in ⋃ i, B i, ENNReal.ofReal ‖φ x‖ ∂μ := by
    rw [lintegral_iUnion hA hdA, lintegral_iUnion hB hdB]
    exact tsum_congr hnorm
  have hφB : IntegrableOn φ (⋃ i, B i) μ := by
    refine ⟨hφ.aestronglyMeasurable, (hasFiniteIntegral_iff_norm φ).2 ?_⟩
    rw [← hnormUnion]
    exact (hasFiniteIntegral_iff_norm φ).1 hφE.2
  refine ⟨hφB, ?_⟩
  rw [integral_iUnion hA hdA hφE, integral_iUnion hB hdB hφB]
  apply tsum_congr
  intro i
  calc
    (∫ x in A i, φ x ∂μ) = ∫ x in A i, φ (T i x) ∂μ :=
      setIntegral_congr_fun (hA i) (fun x hx => (hinv i x hx).symm)
    _ = ∫ x in B i, φ x ∂μ := (htransport i).integral_comp (hemb i) φ
