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

open scoped ModularForm

namespace Submission

/-- Above a common height, every coset factor other than the identity has norm at most one,
so the modular-form norm is bounded by the identity factor with constant `C = 1`. -/
theorem f036cc6b1f_fd_norm_bound :
    ∀ (M : ℕ) [NeZero M] (f : CuspForm (CongruenceSubgroup.Gamma0 M) 2),
      ∃ C Y : ℝ, 0 ≤ C ∧ ∀ z : UpperHalfPlane, Y ≤ z.im →
        ‖ModularForm.norm (MonoidHom.range (Matrix.SpecialLinearGroup.mapGL ℝ :
          Matrix.SpecialLinearGroup (Fin 2) ℤ →*
            Matrix.GeneralLinearGroup (Fin 2) ℝ)) f z‖ ≤ C * ‖f z‖ := by
  intro M _ f
  classical
  let H := MonoidHom.range (Matrix.SpecialLinearGroup.mapGL ℝ :
    Matrix.SpecialLinearGroup (Fin 2) ℤ →* Matrix.GeneralLinearGroup (Fin 2) ℝ)
  let Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ) := CongruenceSubgroup.Gamma0 M
  let Q := H ⧸ Γ.subgroupOf H
  let : Fintype Q := Fintype.ofFinite Q
  -- Arithmeticity packages the cusp condition for every integral slash translate.
  have hzero (q : Q) : UpperHalfPlane.IsZeroAtImInfty (SlashInvariantForm.quotientFunc f q) := by
    induction q using Quotient.inductionOn with
    | h r =>
      obtain ⟨g, hg⟩ := r.property
      change UpperHalfPlane.IsZeroAtImInfty ((f : UpperHalfPlane → ℂ) ∣[2] r.val⁻¹)
      rw [← hg, ← map_inv]
      simpa only [ModularForm.SL_slash, Matrix.SpecialLinearGroup.mapGL,
        MonoidHom.comp_apply, algebraMap_int_eq] using
          CuspFormClass.zero_at_infty_slash f g⁻¹
  have hbound (q : Q) : ∀ᶠ z in UpperHalfPlane.atImInfty,
      ‖SlashInvariantForm.quotientFunc f q z‖ ≤ 1 := by
    obtain ⟨Y, hY⟩ := UpperHalfPlane.isZeroAtImInfty_iff.mp (hzero q) 1 zero_lt_one
    exact (UpperHalfPlane.atImInfty_mem _).mpr ⟨Y, hY⟩
  -- Finiteness of Q makes the eventual bounds hold at one common height.
  obtain ⟨Y, hY⟩ := (UpperHalfPlane.atImInfty_mem _).mp (Filter.eventually_all.mpr hbound)
  refine ⟨1, Y, zero_le_one, ?_⟩
  intro z hz
  let q₀ : Q := ⟦(1 : H)⟧
  have hid : SlashInvariantForm.quotientFunc f q₀ z = f z := by
    simp [q₀]
  have hprod : ∏ q ∈ Finset.univ.erase q₀, ‖SlashInvariantForm.quotientFunc f q z‖ ≤ 1 :=
    Finset.prod_le_one (fun q _ ↦ norm_nonneg _) (fun q _ ↦ hY z hz q)
  calc
    ‖ModularForm.norm H f z‖ = ∏ q : Q, ‖SlashInvariantForm.quotientFunc f q z‖ := by
      simp only [ModularForm.coe_norm, Finset.prod_apply, norm_prod]
      rfl
    _ = ‖f z‖ * ∏ q ∈ Finset.univ.erase q₀, ‖SlashInvariantForm.quotientFunc f q z‖ := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ q₀), hid]
    _ ≤ 1 * ‖f z‖ := by
      simpa using mul_le_mul_of_nonneg_left hprod (norm_nonneg (f z))

end Submission
