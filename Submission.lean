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
