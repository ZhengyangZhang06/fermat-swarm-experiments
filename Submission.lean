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

theorem Submission.f036cc6b1f_pc_hi_rational_slash
    (Γ Δ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
    [Γ.FiniteIndex] [Δ.FiniteIndex]
    (A : Matrix.GeneralLinearGroup (Fin 2) ℝ)
    (_hpos : 0 < (A.det : ℝ))
    (hrat : ∀ i j : Fin 2, ∃ q : ℚ, A i j = (q : ℝ))
    (hconj : ∀ δ : Matrix.SpecialLinearGroup (Fin 2) ℤ, δ ∈ Δ →
      A * Matrix.SpecialLinearGroup.mapGL ℝ δ * A⁻¹ ∈
        (Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ))) :
    ∀ f : CuspForm Γ 2, ∃ g : CuspForm Δ 2,
      (g : UpperHalfPlane → ℂ) =
        SlashAction.map (2 : ℤ) A (f : UpperHalfPlane → ℂ) := by
  classical
  intro f
  choose q hq using hrat
  have rational_cusp (c : OnePoint ℝ)
      (hc : c ∈ Set.range (OnePoint.map (Rat.cast : ℚ → ℝ))) :
      A • c ∈ Set.range (OnePoint.map (Rat.cast : ℚ → ℝ)) := by
    obtain ⟨r, rfl⟩ := hc
    cases r with
    | infty =>
      rw [OnePoint.map_infty, OnePoint.smul_infty_eq_ite]
      split
      · exact ⟨OnePoint.infty, rfl⟩
      · refine ⟨↑(q 0 0 / q 1 0), ?_⟩
        simp [hq]
    | coe r =>
      rw [OnePoint.map_some, OnePoint.smul_some_eq_ite]
      split
      · exact ⟨OnePoint.infty, rfl⟩
      · refine ⟨↑((q 0 0 * r + q 0 1) / (q 1 0 * r + q 1 1)), ?_⟩
        simp [hq]
  refine ⟨{
    toFun := SlashAction.map (2 : ℤ) A (f : UpperHalfPlane → ℂ)
    slash_action_eq' := ?_
    holo' := (CuspFormClass.holo f).slash 2 A
    zero_at_cusps' := ?_
  }, rfl⟩
  · rintro _ ⟨δ, hδ, rfl⟩
    rw [← SlashAction.slash_mul]
    have hmul : A * Matrix.SpecialLinearGroup.mapGL ℝ δ =
        (A * Matrix.SpecialLinearGroup.mapGL ℝ δ * A⁻¹) * A := by
      simp [mul_assoc]
    rw [hmul, SlashAction.slash_mul,
      SlashInvariantFormClass.slash_action_eq f _ (hconj δ hδ)]
  · intro c hc
    apply OnePoint.IsZeroAt.smul_iff.mp
    apply CuspFormClass.zero_at_cusps f
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z, isCusp_SL2Z_iff] at hc ⊢
    exact rational_cusp c hc
