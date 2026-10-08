/-
Copyright 2026 Anthropic, PBC. Licensed under Apache-2.0; see LICENSE.
Source: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_CuspForm_span_heckeTLin_eigen_eq_top.lean
Modified: replaced the proof with sorry and removed P2M proof imports.
Requires the upstream Definitions modules and their dependencies.
-/

import Definitions.Def_ModularForm_HeckeOperatorForms
/- These attribute-removal targets are absent from the pinned dependency closure.
Retain the frozen commands as provenance; they have no applicable declarations here.
attribute [-instance] FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2
attribute [-simp] FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero
-/

theorem CuspForm.span_heckeTLin_eigen_eq_top (M : ℕ) [NeZero M] :
    Submodule.span ℂ {v : CuspForm (CongruenceSubgroup.Gamma0 M) 2 |
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M), ∃ c : ℂ,
        CuspForm.heckeTLin 2 hℓ hℓM v = c • v} = ⊤ := by
  sorry

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
