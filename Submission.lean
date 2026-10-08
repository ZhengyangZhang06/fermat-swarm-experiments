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

theorem Submission.f036cc6b1f_pc_hi_gpt_unique_projective_index :
    ∀ (p : ℕ), p.Prime → ∀ (a b v : ℤ),
      (¬ (p : ℤ) ∣ a ∨ ¬ (p : ℤ) ∣ b) → ¬ (p : ℤ) ∣ v →
      ∃! i : Fin (p + 1), (p : ℤ) ∣
        (if i.val < p then b - a * (i.val : ℤ) else a * v + b * (p : ℤ)) := by
  intro p hp a b v hab hv
  let : Fact p.Prime := ⟨hp⟩
  have hv' : (v : ZMod p) ≠ 0 := by
    exact fun h => hv ((ZMod.intCast_zmod_eq_zero_iff_dvd v p).mp h)
  by_cases ha : (a : ZMod p) = 0
  · have hb : (b : ZMod p) ≠ 0 := by
      rcases hab with ha' | hb'
      · exact (ha' ((ZMod.intCast_zmod_eq_zero_iff_dvd a p).mp ha)).elim
      · exact fun h => hb' ((ZMod.intCast_zmod_eq_zero_iff_dvd b p).mp h)
    refine ⟨Fin.last p, ?_, ?_⟩
    · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
      simp [ha]
    · intro i hi
      by_cases hip : i.val < p
      · have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hi
        simp [hip, ha] at hz
        exact (hb hz).elim
      · apply Fin.ext
        have hil := i.isLt
        simp only [Fin.val_last]
        omega
  · let x : ZMod p := (b : ZMod p) / (a : ZMod p)
    have hxlt : x.val < p := ZMod.val_lt x
    let j : Fin (p + 1) := ⟨x.val, Nat.lt_succ_of_lt hxlt⟩
    have hjlt : j.val < p := hxlt
    have hj : (a : ZMod p) * (j.val : ZMod p) = (b : ZMod p) := by
      change (a : ZMod p) * (x.val : ZMod p) = (b : ZMod p)
      rw [ZMod.natCast_zmod_val]
      exact mul_div_cancel₀ _ ha
    refine ⟨j, ?_, ?_⟩
    · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
      simp only [if_pos hjlt, Int.cast_sub, Int.cast_mul, Int.cast_natCast, hj,
        sub_self]
    · intro i hi
      have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hi
      by_cases hip : i.val < p
      · have hi' : (a : ZMod p) * (i.val : ZMod p) = (b : ZMod p) := by
          symm
          simpa only [if_pos hip, Int.cast_sub, Int.cast_mul, Int.cast_natCast,
            sub_eq_zero] using hz
        have hij : (i.val : ZMod p) = (j.val : ZMod p) :=
          mul_left_cancel₀ ha (hi'.trans hj.symm)
        apply Fin.ext
        have hval := congrArg ZMod.val hij
        simpa only [ZMod.val_natCast_of_lt hip, ZMod.val_natCast_of_lt hjlt] using hval
      · have hzero : (a : ZMod p) * (v : ZMod p) = 0 := by
          simpa [hip] using hz
        exact (mul_ne_zero ha hv' hzero).elim
theorem Submission.f036cc6b1f_pc_hi_gpt_bezout_lift :
    ∀ (M : ℕ) [NeZero M] (p : ℕ), p.Prime → ¬ p ∣ M →
      ∃ (v : ℤ) (σ β : Matrix.SpecialLinearGroup (Fin 2) ℤ),
        (¬ (p : ℤ) ∣ v) ∧ σ ∈ CongruenceSubgroup.Gamma0 M ∧
        β ∈ CongruenceSubgroup.Gamma0 M ∧ σ 0 0 = (p : ℤ) ∧ σ 0 1 = -v ∧
        ModularForm.heckeMatrix p 0 * Matrix.SpecialLinearGroup.mapGL ℝ σ =
          Matrix.SpecialLinearGroup.mapGL ℝ β * ModularForm.heckeDiagMatrix p := by
  intro M _ p hp hpM
  let u : ℤ := Nat.gcdA p M
  let v : ℤ := Nat.gcdB p M
  have hcop : Nat.Coprime p M := hp.coprime_iff_not_dvd.mpr hpM
  have hbez : (p : ℤ) * u + (M : ℤ) * v = 1 := by
    simpa only [hcop.gcd_eq_one, Nat.cast_one] using (Nat.gcd_eq_gcd_ab p M).symm
  have hv : ¬ (p : ℤ) ∣ v := by
    intro hdiv
    have hone : (p : ℤ) ∣ 1 := by
      rw [← hbez]
      exact dvd_add (dvd_mul_right _ _) (dvd_mul_of_dvd_right hdiv _)
    exact hp.not_dvd_one (by exact_mod_cast hone)
  let σ : Matrix.SpecialLinearGroup (Fin 2) ℤ :=
    ⟨!![(p : ℤ), -v; (M : ℤ), u], by
      simpa only [Matrix.det_fin_two_of, neg_mul, sub_neg_eq_add, mul_comm v (M : ℤ)]
        using hbez⟩
  let β : Matrix.SpecialLinearGroup (Fin 2) ℤ :=
    ⟨!![(1 : ℤ), -v; (M : ℤ), (p : ℤ) * u], by
      simpa only [Matrix.det_fin_two_of, one_mul, neg_mul, sub_neg_eq_add,
        mul_comm v (M : ℤ)] using hbez⟩
  refine ⟨v, σ, β, hv, ?_, ?_, rfl, rfl, ?_⟩
  · rw [CongruenceSubgroup.Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact dvd_refl (M : ℤ)
  · rw [CongruenceSubgroup.Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact dvd_refl (M : ℤ)
  · apply Units.ext
    change (ModularForm.heckeMatrix p 0 : Matrix (Fin 2) (Fin 2) ℝ) *
        (Matrix.SpecialLinearGroup.mapGL ℝ σ : Matrix (Fin 2) (Fin 2) ℝ) =
      (Matrix.SpecialLinearGroup.mapGL ℝ β : Matrix (Fin 2) (Fin 2) ℝ) *
        (ModularForm.heckeDiagMatrix p : Matrix (Fin 2) (Fin 2) ℝ)
    rw [ModularForm.val_heckeMatrix hp.ne_zero, ModularForm.val_heckeDiagMatrix hp.ne_zero]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [σ, β, Matrix.mul_apply, Fin.sum_univ_two, Matrix.SpecialLinearGroup.mapGL,
        Matrix.SpecialLinearGroup.map_apply_coe, mul_comm]


namespace Submission

theorem f036cc6b1f_pc_hi_good_prime_transversal
    (M : ℕ) [NeZero M] (p : ℕ) (hp : p.Prime) (hpM : ¬ p ∣ M) :
    ∃ r : Fin (p + 1) → Matrix.SpecialLinearGroup (Fin 2) ℤ,
      (∀ i, r i ∈ CongruenceSubgroup.Gamma0 M) ∧
      (∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
        γ ∈ CongruenceSubgroup.Gamma0 M →
          ∃! i : Fin (p + 1), (p : ℤ) ∣ (γ * (r i)⁻¹) 0 1) ∧
      (∀ i : Fin p, ModularForm.heckeMatrix p 0 *
        Matrix.SpecialLinearGroup.mapGL ℝ (r i.castSucc) =
          ModularForm.heckeMatrix p i.val) ∧
      (∃ β : Matrix.SpecialLinearGroup (Fin 2) ℤ,
        β ∈ CongruenceSubgroup.Gamma0 M ∧
          ModularForm.heckeMatrix p 0 *
            Matrix.SpecialLinearGroup.mapGL ℝ (r (Fin.last p)) =
              Matrix.SpecialLinearGroup.mapGL ℝ β * ModularForm.heckeDiagMatrix p) := by
  obtain ⟨v, σ, β, hv, hσ, hβ, hσ00, hσ01, hσβ⟩ :=
    f036cc6b1f_pc_hi_gpt_bezout_lift M p hp hpM
  let t (j : ℕ) : Matrix.SpecialLinearGroup (Fin 2) ℤ :=
    ⟨!![1, (j : ℤ); 0, 1], by simp [Matrix.det_fin_two]⟩
  let r (i : Fin (p + 1)) : Matrix.SpecialLinearGroup (Fin 2) ℤ :=
    if i.val < p then t i.val else σ
  have hentry (γ δ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
      (γ * δ⁻¹) 0 1 = -(γ 0 0) * δ 0 1 + γ 0 1 * δ 0 0 := by
    change ((γ : Matrix (Fin 2) (Fin 2) ℤ) *
      ((δ⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ)) 0 1 = _
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hrentry (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (i : Fin (p + 1)) :
      (γ * (r i)⁻¹) 0 1 =
        if i.val < p then γ 0 1 - γ 0 0 * (i.val : ℤ)
          else γ 0 0 * v + γ 0 1 * (p : ℤ) := by
    rw [hentry]
    by_cases hi : i.val < p
    · simp [r, hi, t, sub_eq_add_neg, add_comm]
    · simp [r, hi, hσ00, hσ01]
  refine ⟨r, ?_, ?_, ?_, ?_⟩
  · intro i
    dsimp [r]
    split_ifs with hi
    · simp [CongruenceSubgroup.Gamma0_mem, t]
    · exact hσ
  · intro γ _hγ
    have hrow : ¬ (p : ℤ) ∣ γ 0 0 ∨ ¬ (p : ℤ) ∣ γ 0 1 := by
      by_contra! h
      have hdet : (p : ℤ) ∣ 1 := by
        rw [← γ.det_coe, Matrix.det_fin_two]
        exact dvd_sub (dvd_mul_of_dvd_left h.1 _) (dvd_mul_of_dvd_left h.2 _)
      exact hp.not_dvd_one (by exact_mod_cast hdet)
    simpa only [hrentry] using
      (f036cc6b1f_pc_hi_gpt_unique_projective_index p hp (γ 0 0) (γ 0 1) v hrow hv)
  · intro i
    have hri : r i.castSucc = t i.val := by simp [r, i.isLt]
    rw [hri]
    apply Matrix.GeneralLinearGroup.ext
    intro a b
    fin_cases a <;> fin_cases b <;>
      simp [Units.val_mul, ModularForm.val_heckeMatrix hp.ne_zero,
        Matrix.SpecialLinearGroup.mapGL_coe_matrix, t, Matrix.mul_apply,
        Fin.sum_univ_two, Matrix.SpecialLinearGroup.map_apply_coe]
  · refine ⟨β, hβ, ?_⟩
    simpa [r] using hσβ

end Submission
