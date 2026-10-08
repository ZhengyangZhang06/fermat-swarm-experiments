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

namespace Submission

open MeasureTheory
open scoped MatrixGroups

/-- Unfold the finite slash trace over the almost-everywhere disjoint translated domains. -/
theorem f036cc6b1f_pc_hi_finite_trace_unfolding
    (Γ Δ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
    (R : Finset (Matrix.SpecialLinearGroup (Fin 2) ℤ)) (F : Set UpperHalfPlane)
    (hΔΓ : Δ ≤ Γ) (hneg : (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) ∈ Δ)
    (hR : ∀ r ∈ R, r ∈ Γ)
    (hcover : ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, γ ∈ Γ →
      ∃ r ∈ R, γ * r⁻¹ ∈ Δ)
    (huniq : ∀ r ∈ R, ∀ s ∈ R, s * r⁻¹ ∈ Δ → s = r)
    (hF : MeasurableSet F)
    (hdom : ∀ᵐ z ∂(volume : Measure UpperHalfPlane),
      ∃ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
        γ ∈ Γ ∧ γ • z ∈ F ∧ ∀ δ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
          δ ∈ Γ → δ • z ∈ F → δ = γ ∨ δ = -γ)
    (u v : UpperHalfPlane → ℂ)
    (hv : ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, γ ∈ Γ →
      SlashAction.map (2 : ℤ) γ v = v) :
    let E : Set UpperHalfPlane := ⋃ r ∈ R, (fun z : UpperHalfPlane => r • z) '' F
    IntegrableOn (UpperHalfPlane.petersson 2 u v) E (volume : Measure UpperHalfPlane) →
      (∀ r ∈ R, IntegrableOn
        (UpperHalfPlane.petersson 2 (SlashAction.map (2 : ℤ) r u) v)
        F (volume : Measure UpperHalfPlane)) ∧
      integral ((volume : Measure UpperHalfPlane).restrict F)
          (UpperHalfPlane.petersson 2 (R.sum (fun r => SlashAction.map (2 : ℤ) r u)) v) =
        integral ((volume : Measure UpperHalfPlane).restrict E)
          (UpperHalfPlane.petersson 2 u v) := by
  classical
  intro E hInt
  have hLift := f036cc6b1f_pc_hi_effective_domain_lift
    Γ Δ R F hΔΓ hneg hR hcover huniq hF hdom
  have hEmb (r : SL(2, ℤ)) :
      MeasurableEmbedding (fun z : UpperHalfPlane => r • z) :=
    (Homeomorph.smul (Matrix.SpecialLinearGroup.mapGL ℝ r)).measurableEmbedding
  have hPres (r : SL(2, ℤ)) :
      MeasurePreserving (fun z : UpperHalfPlane => r • z) volume volume :=
    measurePreserving_smul (Matrix.SpecialLinearGroup.mapGL ℝ r) volume
  have hMeas (r : SL(2, ℤ)) :
      MeasurableSet ((fun z : UpperHalfPlane => r • z) '' F) :=
    (hEmb r).measurableSet_image.mpr hF
  have hPiece (r : SL(2, ℤ)) (hr : r ∈ R) :
      IntegrableOn (UpperHalfPlane.petersson 2 u v)
        ((fun z : UpperHalfPlane => r • z) '' F) volume := by
    apply hInt.mono_set
    intro z hz
    exact Set.mem_iUnion.mpr ⟨r, Set.mem_iUnion.mpr ⟨hr, hz⟩⟩
  have hCov (r : SL(2, ℤ)) (hr : r ∈ R) :
      UpperHalfPlane.petersson 2 (SlashAction.map (2 : ℤ) r u) v =
        fun z => UpperHalfPlane.petersson 2 u v (r • z) := by
    funext z
    simpa only [hv r (hR r hr)] using UpperHalfPlane.petersson_slash_SL 2 u v r z
  have hTerm (r : SL(2, ℤ)) (hr : r ∈ R) :
      IntegrableOn (UpperHalfPlane.petersson 2 (SlashAction.map (2 : ℤ) r u) v)
        F volume := by
    rw [hCov r hr]
    exact ((hPres r).restrict_image_emb (hEmb r) F).integrable_comp_of_integrable
      (hPiece r hr)
  have hIntegral (r : SL(2, ℤ)) (hr : r ∈ R) :
      (∫ z in F, UpperHalfPlane.petersson 2 (SlashAction.map (2 : ℤ) r u) v z) =
        ∫ z in (fun w : UpperHalfPlane => r • w) '' F,
          UpperHalfPlane.petersson 2 u v z := by
    rw [hCov r hr]
    exact ((hPres r).setIntegral_image_emb (hEmb r) (UpperHalfPlane.petersson 2 u v) F).symm
  refine ⟨hTerm, ?_⟩
  have hSum :
      UpperHalfPlane.petersson 2 (R.sum (fun r => SlashAction.map (2 : ℤ) r u)) v =
        fun z => ∑ r ∈ R, UpperHalfPlane.petersson 2 (SlashAction.map (2 : ℤ) r u) v z := by
    funext z
    simp only [UpperHalfPlane.petersson, Finset.sum_apply, map_sum, Finset.sum_mul]
  have hUnion : (⋃ r : ↥R, (fun z : UpperHalfPlane => (r : SL(2, ℤ)) • z) '' F) = E := by
    simp only [E, Set.iUnion_subtype]
  have hDisj : Pairwise (fun r s : ↥R => AEDisjoint (volume : Measure UpperHalfPlane)
      ((fun z : UpperHalfPlane => (r : SL(2, ℤ)) • z) '' F)
      ((fun z : UpperHalfPlane => (s : SL(2, ℤ)) • z) '' F)) := by
    intro r s hrs
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hLift.2.2] with z hz
    intro hzs
    exact hrs (Subtype.ext (hz r r.property s s.property hzs.1 hzs.2))
  have hUnfold := integral_iUnion_ae (fun r : ↥R => (hMeas r).nullMeasurableSet)
    hDisj (hUnion.symm ▸ hInt)
  rw [hSum, integral_finsetSum R (fun r hr => hTerm r hr)]
  trans ∑ r ∈ R, ∫ z in (fun w : UpperHalfPlane => r • w) '' F,
    UpperHalfPlane.petersson 2 u v z
  · exact Finset.sum_congr rfl hIntegral
  · rw [← Finset.sum_coe_sort R (fun r =>
      ∫ z in (fun w : UpperHalfPlane => r • w) '' F, UpperHalfPlane.petersson 2 u v z)]
    simpa only [hUnion, tsum_fintype] using hUnfold.symm

end Submission
