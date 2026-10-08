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
