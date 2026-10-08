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
