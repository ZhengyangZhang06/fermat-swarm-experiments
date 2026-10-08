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

theorem Submission.f036cc6b1f_tdi_planar_exp_integrable_fd :
    ∀ (a : ℝ), 0 < a → MeasureTheory.IntegrableOn
      (fun z : UpperHalfPlane => Real.exp (-a * z.im)) ModularGroup.fd
      ((MeasureTheory.volume : MeasureTheory.Measure ℂ).comap UpperHalfPlane.coe) := by
  intro a ha
  let b : ℝ := Real.sqrt 3 / 2
  have hy : MeasureTheory.IntegrableOn (fun y : ℝ => Real.exp (-a * y))
      (Set.Ici b) :=
    (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr
      (exp_neg_integrableOn_Ioi b ha)
  have hx : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ))
      (Set.Icc (-(1 / 2 : ℝ)) (1 / 2)) :=
    MeasureTheory.integrableOn_const (by
      rw [Real.volume_Icc]
      exact ENNReal.ofReal_ne_top)
  have hprod : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => Real.exp (-a * p.2))
      (Set.Icc (-(1 / 2 : ℝ)) (1 / 2) ×ˢ Set.Ici b) := by
    change MeasureTheory.Integrable _
      (((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod MeasureTheory.volume).restrict _)
    rw [← MeasureTheory.Measure.prod_restrict]
    simpa only [one_mul] using hx.mul_prod hy
  have hc : MeasureTheory.IntegrableOn (fun z : ℂ => Real.exp (-a * z.im))
      (Complex.measurableEquivRealProd ⁻¹'
        (Set.Icc (-(1 / 2 : ℝ)) (1 / 2) ×ˢ Set.Ici b)) :=
    (Complex.volume_preserving_equiv_real_prod.integrableOn_comp_preimage
      Complex.measurableEquivRealProd.measurableEmbedding).mpr hprod
  have hi : MeasureTheory.IntegrableOn (fun z : ℂ => Real.exp (-a * z.im))
      (UpperHalfPlane.coe '' ModularGroup.fd) := by
    apply hc.mono_set
    rintro _ ⟨z, hz, rfl⟩
    change z.re ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2) ∧ b ≤ z.im
    constructor
    · exact abs_le.mp hz.2
    · dsimp [b]
      have hsq := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hz
      have hpos := z.im_pos
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg (3 : ℝ)]
  have ht := (UpperHalfPlane.measurableEmbedding_coe.integrableOn_iff_comap
    (Set.image_subset_range UpperHalfPlane.coe ModularGroup.fd)).mp hi
  simpa only [Set.preimage_image_eq _ UpperHalfPlane.coe_injective, Function.comp_def,
    UpperHalfPlane.coe_im] using ht

theorem Submission.f036cc6b1f_tdi_petersson_integrable_of_exp_product_bound
    (u v : UpperHalfPlane → ℂ) (a C Y : ℝ)
    (hu : Continuous u) (hv : Continuous v) (ha : 0 < a) (_hC : 0 ≤ C)
    (hbound : ∀ z : UpperHalfPlane, Y ≤ z.im →
      ‖u z * v z‖ ≤ C * Real.exp (-a * z.im)) :
    MeasureTheory.IntegrableOn (UpperHalfPlane.petersson 2 u v) ModularGroup.fd
      (MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane) := by
  let ν : MeasureTheory.Measure UpperHalfPlane :=
    (MeasureTheory.volume : MeasureTheory.Measure ℂ).comap UpperHalfPlane.coe
  let W : UpperHalfPlane → ℂ := fun z ↦ (starRingEnd ℂ) (u z) * v z
  let L : ℝ := max 1 Y
  let D := ModularGroup.truncatedFundamentalDomain L
  let E := ModularGroup.fd ∩ {z : UpperHalfPlane | L < z.im}
  have hW : Continuous W := (Complex.continuous_conj.comp hu).mul hv
  -- The lower truncation is compact and planar measure is finite on compact sets.
  have hD : MeasureTheory.IntegrableOn W D ν :=
    hW.continuousOn.integrableOn_compact
      (ModularGroup.isCompact_truncatedFundamentalDomain L)
  have hEmeas : MeasurableSet E :=
    ModularGroup.isClosed_fd.measurableSet.inter
      (isOpen_lt continuous_const UpperHalfPlane.continuous_im).measurableSet
  -- On the tail, use precisely the supplied planar exponential-integrability interface.
  have hmajor : MeasureTheory.IntegrableOn
      (fun z : UpperHalfPlane ↦ C * Real.exp (-a * z.im)) E ν :=
    ((Submission.f036cc6b1f_tdi_planar_exp_integrable_fd a ha).mono_set
      Set.inter_subset_left).const_mul C
  have hE : MeasureTheory.IntegrableOn W E ν := by
    refine hmajor.mono' hW.aestronglyMeasurable ?_
    filter_upwards [MeasureTheory.ae_restrict_mem hEmeas] with z hz
    have hY : Y ≤ z.im := (le_max_right 1 Y).trans hz.2.le
    simpa only [W, norm_mul, Complex.norm_conj] using hbound z hY
  have hpartition : D ∪ E = ModularGroup.fd := by
    ext z
    change (z ∈ ModularGroup.fd ∧ z.im ≤ L) ∨
      (z ∈ ModularGroup.fd ∧ L < z.im) ↔ z ∈ ModularGroup.fd
    constructor
    · rintro (hz | hz) <;> exact hz.1
    · intro hz
      rcases le_or_gt z.im L with h | h
      · exact Or.inl ⟨hz, h⟩
      · exact Or.inr ⟨hz, h⟩
  have hplanar : MeasureTheory.IntegrableOn W ModularGroup.fd ν := by
    rw [← hpartition]
    exact hD.union hE
  -- Multiplication by the hyperbolic density cancels the weight-two factor.
  rw [MeasureTheory.IntegrableOn, UpperHalfPlane.volume_def,
    MeasureTheory.restrict_withDensity ModularGroup.isClosed_fd.measurableSet]
  have hdensity : Measurable (fun z : UpperHalfPlane ↦
      (1 / NNReal.mk z.im z.im_pos.le : NNReal) ^ 2) := by
    fun_prop
  rw [MeasureTheory.integrable_withDensity_iff_integrable_coe_smul hdensity]
  have hcancel : (fun z : UpperHalfPlane ↦
      (((1 / NNReal.mk z.im z.im_pos.le : NNReal) ^ 2 : NNReal) : ℝ) •
        UpperHalfPlane.petersson 2 u v z) = W := by
    funext z
    simp only [UpperHalfPlane.petersson, zpow_ofNat, NNReal.coe_pow,
      NNReal.coe_div, NNReal.coe_one, NNReal.coe_mk, Complex.real_smul,
      Complex.ofReal_pow, Complex.ofReal_div, Complex.ofReal_one, W]
    have hz : (z.im : ℂ) ≠ 0 := by exact_mod_cast z.im_ne_zero
    field_simp
  rw [hcancel]
  exact hplanar

namespace Submission

open UpperHalfPlane MeasureTheory Matrix.SpecialLinearGroup
open scoped MatrixGroups ModularForm Pointwise

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

theorem Submission.f036cc6b1f_pc_hi_finite_trace_unfolding
    (Γ Δ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
    (R : Finset (Matrix.SpecialLinearGroup (Fin 2) ℤ)) (F : Set UpperHalfPlane)
    (hΔΓ : Δ ≤ Γ) (hneg : (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) ∈ Δ)
    (hR : ∀ r ∈ R, r ∈ Γ)
    (hcover : ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, γ ∈ Γ →
      ∃ r ∈ R, γ * r⁻¹ ∈ Δ)
    (huniq : ∀ r ∈ R, ∀ s ∈ R, s * r⁻¹ ∈ Δ → s = r)
    (hF : MeasurableSet F)
    (hdom : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane),
      ∃ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
        γ ∈ Γ ∧ γ • z ∈ F ∧ ∀ δ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
          δ ∈ Γ → δ • z ∈ F → δ = γ ∨ δ = -γ)
    (u v : UpperHalfPlane → ℂ)
    (hv : ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, γ ∈ Γ →
      SlashAction.map (2 : ℤ) γ v = v) :
    let E : Set UpperHalfPlane := ⋃ r ∈ R, (fun z : UpperHalfPlane => r • z) '' F
    MeasureTheory.IntegrableOn (UpperHalfPlane.petersson 2 u v) E (MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane) →
      (∀ r ∈ R, MeasureTheory.IntegrableOn
        (UpperHalfPlane.petersson 2 (SlashAction.map (2 : ℤ) r u) v)
        F (MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane)) ∧
      MeasureTheory.integral ((MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane).restrict F)
          (UpperHalfPlane.petersson 2 (R.sum (fun r => SlashAction.map (2 : ℤ) r u)) v) =
        MeasureTheory.integral ((MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane).restrict E)
          (UpperHalfPlane.petersson 2 u v) := by
  classical
  intro E hInt
  have hLift := f036cc6b1f_pc_hi_effective_domain_lift
    Γ Δ R F hΔΓ hneg hR hcover huniq hF hdom
  have hEmb (r : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
      MeasurableEmbedding (fun z : UpperHalfPlane => r • z) :=
    (Homeomorph.smul (Matrix.SpecialLinearGroup.mapGL ℝ r)).measurableEmbedding
  have hPres (r : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
      MeasureTheory.MeasurePreserving (fun z : UpperHalfPlane => r • z) MeasureTheory.volume MeasureTheory.volume :=
    MeasureTheory.measurePreserving_smul (Matrix.SpecialLinearGroup.mapGL ℝ r) MeasureTheory.volume
  have hMeas (r : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
      MeasurableSet ((fun z : UpperHalfPlane => r • z) '' F) :=
    (hEmb r).measurableSet_image.mpr hF
  have hPiece (r : Matrix.SpecialLinearGroup (Fin 2) ℤ) (hr : r ∈ R) :
      MeasureTheory.IntegrableOn (UpperHalfPlane.petersson 2 u v)
        ((fun z : UpperHalfPlane => r • z) '' F) MeasureTheory.volume := by
    apply hInt.mono_set
    intro z hz
    exact Set.mem_iUnion.mpr ⟨r, Set.mem_iUnion.mpr ⟨hr, hz⟩⟩
  have hCov (r : Matrix.SpecialLinearGroup (Fin 2) ℤ) (hr : r ∈ R) :
      UpperHalfPlane.petersson 2 (SlashAction.map (2 : ℤ) r u) v =
        fun z => UpperHalfPlane.petersson 2 u v (r • z) := by
    funext z
    simpa only [hv r (hR r hr)] using UpperHalfPlane.petersson_slash_SL 2 u v r z
  have hTerm (r : Matrix.SpecialLinearGroup (Fin 2) ℤ) (hr : r ∈ R) :
      MeasureTheory.IntegrableOn (UpperHalfPlane.petersson 2 (SlashAction.map (2 : ℤ) r u) v)
        F MeasureTheory.volume := by
    rw [hCov r hr]
    exact ((hPres r).restrict_image_emb (hEmb r) F).integrable_comp_of_integrable
      (hPiece r hr)
  have hIntegral (r : Matrix.SpecialLinearGroup (Fin 2) ℤ) (hr : r ∈ R) :
      MeasureTheory.integral (MeasureTheory.volume.restrict F)
        (UpperHalfPlane.petersson 2 (SlashAction.map (2 : ℤ) r u) v) =
        MeasureTheory.integral
          (MeasureTheory.volume.restrict ((fun w : UpperHalfPlane => r • w) '' F))
          (UpperHalfPlane.petersson 2 u v) := by
    rw [hCov r hr]
    exact ((hPres r).setIntegral_image_emb (hEmb r) (UpperHalfPlane.petersson 2 u v) F).symm
  refine ⟨hTerm, ?_⟩
  have hSum :
      UpperHalfPlane.petersson 2 (R.sum (fun r => SlashAction.map (2 : ℤ) r u)) v =
        fun z => ∑ r ∈ R, UpperHalfPlane.petersson 2 (SlashAction.map (2 : ℤ) r u) v z := by
    funext z
    simp only [UpperHalfPlane.petersson, Finset.sum_apply, map_sum, Finset.sum_mul]
  have hUnion : (⋃ r : ↥R, (fun z : UpperHalfPlane => (r : Matrix.SpecialLinearGroup (Fin 2) ℤ) • z) '' F) = E := by
    simp only [E, Set.iUnion_subtype]
  have hDisj : Pairwise (fun r s : ↥R => MeasureTheory.AEDisjoint (MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane)
      ((fun z : UpperHalfPlane => (r : Matrix.SpecialLinearGroup (Fin 2) ℤ) • z) '' F)
      ((fun z : UpperHalfPlane => (s : Matrix.SpecialLinearGroup (Fin 2) ℤ) • z) '' F)) := by
    intro r s hrs
    apply MeasureTheory.measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hLift.2.2] with z hz
    intro hzs
    exact hrs (Subtype.ext (hz r r.property s s.property hzs.1 hzs.2))
  have hUnfold := MeasureTheory.integral_iUnion_ae (fun r : ↥R => (hMeas r).nullMeasurableSet)
    hDisj (hUnion.symm ▸ hInt)
  rw [hSum, MeasureTheory.integral_finsetSum R (fun r hr => hTerm r hr)]
  trans ∑ r ∈ R, MeasureTheory.integral
    (MeasureTheory.volume.restrict ((fun w : UpperHalfPlane => r • w) '' F))
    (UpperHalfPlane.petersson 2 u v)
  · exact Finset.sum_congr rfl hIntegral
  · rw [← Finset.sum_coe_sort R (fun r =>
      MeasureTheory.integral (MeasureTheory.volume.restrict ((fun w : UpperHalfPlane => r • w) '' F))
        (UpperHalfPlane.petersson 2 u v))]
    simpa only [hUnion, tsum_fintype] using hUnfold.symm
theorem Submission.f036cc6b1f_tdi_planar_exp_integrable_fd :
    ∀ (a : ℝ), 0 < a → MeasureTheory.IntegrableOn
      (fun z : UpperHalfPlane => Real.exp (-a * z.im)) ModularGroup.fd
      ((MeasureTheory.volume : MeasureTheory.Measure ℂ).comap UpperHalfPlane.coe) := by
  intro a ha
  let b : ℝ := Real.sqrt 3 / 2
  have hy : MeasureTheory.IntegrableOn (fun y : ℝ => Real.exp (-a * y))
      (Set.Ici b) :=
    (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr
      (exp_neg_integrableOn_Ioi b ha)
  have hx : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ))
      (Set.Icc (-(1 / 2 : ℝ)) (1 / 2)) :=
    MeasureTheory.integrableOn_const (by
      rw [Real.volume_Icc]
      exact ENNReal.ofReal_ne_top)
  have hprod : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => Real.exp (-a * p.2))
      (Set.Icc (-(1 / 2 : ℝ)) (1 / 2) ×ˢ Set.Ici b) := by
    MeasureTheory.integrableOn_Ici_iff_integrableOn_Ioi.mpr (exp_neg_integrableOn_Ioi b ha)
    (MeasureTheory.integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr
      (exp_neg_integrableOn_Ioi b ha)
  have hx : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ))
      (Set.Icc (-(1 / 2 : ℝ)) (1 / 2)) :=
    MeasureTheory.integrableOn_const (by simp only [Real.volume_Icc, ENNReal.ofReal_ne_top])
  have hprod : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => Real.exp (-a * p.2))
      (Set.Icc (-(1 / 2 : ℝ)) (1 / 2) ×ˢ Set.Ici b) := by
    change MeasureTheory.Integrable _
      (((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod MeasureTheory.volume).restrict _)
    rw [← MeasureTheory.Measure.prod_restrict]
    simpa only [one_mul] using hx.mul_prod hy
  have hc : MeasureTheory.IntegrableOn (fun z : ℂ => Real.exp (-a * z.im))
      (Complex.measurableEquivRealProd ⁻¹'
        (Set.Icc (-(1 / 2 : ℝ)) (1 / 2) ×ˢ Set.Ici b)) :=
        (Set.Icc (-(1 : ℝ) / 2) (1 / 2) ×ˢ Set.Ici b)) :=
    (Complex.volume_preserving_equiv_real_prod.integrableOn_comp_preimage
      Complex.measurableEquivRealProd.measurableEmbedding).mpr hprod
  have hi : MeasureTheory.IntegrableOn (fun z : ℂ => Real.exp (-a * z.im))
      (UpperHalfPlane.coe '' ModularGroup.fd) := by
    apply hc.mono_set
    rintro _ ⟨z, hz, rfl⟩
    change z.re ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2) ∧ b ≤ z.im
    change z.re ∈ Set.Icc (-(1 : ℝ) / 2) (1 / 2) ∧ b ≤ z.im
    constructor
    · exact abs_le.mp hz.2
    · dsimp [b]
      have hsq := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hz
      have hpos := z.im_pos
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg (3 : ℝ)]
  have ht := (UpperHalfPlane.measurableEmbedding_coe.integrableOn_iff_comap
    (Set.image_subset_range UpperHalfPlane.coe ModularGroup.fd)).mp hi
  simpa only [Set.preimage_image_eq _ UpperHalfPlane.coe_injective, Function.comp_def,
    UpperHalfPlane.coe_im] using ht
  simpa only [Set.preimage_image_eq _ UpperHalfPlane.coe_injective, Function.comp_def] using ht
/-- The Petersson integrand of two weight-two cusp forms is integrable on each
integral translate of the standard modular fundamental domain. -/
theorem f036cc6b1f_pic_translated_integrable
    (Δ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Δ.FiniteIndex]
    (r : Matrix.SpecialLinearGroup (Fin 2) ℤ) (f g : CuspForm Δ 2) :
    MeasureTheory.IntegrableOn (UpperHalfPlane.petersson 2 f g)
      ((fun z : UpperHalfPlane => r • z) '' ModularGroup.fd)
      (MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane) := by
  -- Translation preserves the arithmetic cusp conditions.
  have : (ConjAct.toConjAct (r : GL (Fin 2) ℝ)⁻¹ •
      (Δ : Subgroup (GL (Fin 2) ℝ))).IsArithmetic := by
    simpa [(show Rat.castHom ℝ = algebraMap ℚ ℝ by rfl), map_inv, map_mapGL]
      using! Subgroup.IsArithmetic.conj (Δ : Subgroup (GL (Fin 2) ℝ)) (mapGL ℚ r)⁻¹
  let u := CuspForm.translate f r
  let v := CuspForm.translate g r
  obtain ⟨a, ha, hu⟩ := CuspFormClass.exp_decay_atImInfty' u
  obtain ⟨b, hb, hv⟩ := CuspFormClass.exp_decay_atImInfty' v
  have huv : (fun z : UpperHalfPlane => u z * v z)
      =O[atImInfty] (fun z => Real.exp (-(a + b) * z.im)) := by
    apply (hu.mul hv).congr_right
    intro z
    rw [← Real.exp_add]
    congr 1
    ring
  obtain ⟨C, hC, hbound⟩ := huv.exists_pos
  obtain ⟨Y, hY⟩ := (atImInfty_mem _).mp hbound.bound
  have hint : IntegrableOn (petersson 2 u v) ModularGroup.fd
      (volume : Measure UpperHalfPlane) := by
    apply f036cc6b1f_tdi_petersson_integrable_of_exp_product_bound
      u v (a + b) C Y (ModularFormClass.continuous u) (ModularFormClass.continuous v)
      (add_pos ha hb) hC.le
    intro z hz
    simpa only [Set.mem_ofPred_eq, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hY z hz
  -- The SL₂ action preserves hyperbolic volume, and Petersson covariance
  -- identifies the pullback with the integrand of the translated forms.
  have hpres : MeasurePreserving (fun z : UpperHalfPlane => r • z)
      (volume : Measure UpperHalfPlane) volume :=
    measurePreserving_smul (r : GL (Fin 2) ℝ) volume
  have hemb : MeasurableEmbedding (fun z : UpperHalfPlane => r • z) :=
    measurableEmbedding_const_smul (r : GL (Fin 2) ℝ)
  apply (hpres.integrableOn_image hemb).mpr
  convert hint using 1
  ext z
  exact (petersson_slash_SL 2 f g r z).symm

end Submission
theorem Submission.f036cc6b1f_pic_mec_invariant_conull_core :
    ∀ (Δ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) (S : Set UpperHalfPlane),
      MeasurableSet S →
      (∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane), z ∈ S) →
      ∃ X : Set UpperHalfPlane, MeasurableSet X ∧
        (∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane), z ∈ X) ∧
        X ⊆ S ∧ (∀ (γ : Δ) (z : UpperHalfPlane),
          (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) • z ∈ X ↔ z ∈ X) := by
  intro Δ S hS hSae
  have : Countable (Matrix.SpecialLinearGroup (Fin 2) ℤ) :=
    Function.Injective.countable (β := Fin 2 → Fin 2 → ℤ)
      (f := fun g : Matrix.SpecialLinearGroup (Fin 2) ℤ => (g.1 : Fin 2 → Fin 2 → ℤ))
      Subtype.val_injective
  have hpres (γ : Δ) : MeasureTheory.MeasurePreserving
      (fun z : UpperHalfPlane => (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) • z)
      MeasureTheory.volume MeasureTheory.volume := by
    change MeasureTheory.MeasurePreserving
      (fun z : UpperHalfPlane =>
        Matrix.SpecialLinearGroup.mapGL ℝ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) • z)
      MeasureTheory.volume MeasureTheory.volume
    exact MeasureTheory.measurePreserving_smul _ _
  let X : Set UpperHalfPlane :=
    ⋂ γ : Δ, (fun z : UpperHalfPlane =>
      (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) • z) ⁻¹' S
  have hstable (γ : Δ) (z : UpperHalfPlane) (hz : z ∈ X) :
      (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) • z ∈ X := by
    refine Set.mem_iInter.mpr fun δ => ?_
    have h := Set.mem_iInter.mp hz (δ * γ)
    simpa only [Set.mem_preimage, Subgroup.coe_mul, mul_smul] using h
  refine ⟨X, MeasurableSet.iInter (fun γ => hS.preimage (hpres γ).measurable),
    ?_, ?_, ?_⟩
  · exact (MeasureTheory.ae_all_iff.mpr fun γ =>
      (hpres γ).quasiMeasurePreserving.ae hSae).mono fun z hz => Set.mem_iInter.mpr hz
  · intro z hz
    have h := Set.mem_iInter.mp hz (1 : Δ)
    simpa only [Set.mem_preimage, Subgroup.coe_one, one_smul] using h
  · intro γ z
    constructor
    · intro hz
      simpa only [Subgroup.coe_inv, inv_smul_smul] using
        hstable γ⁻¹ ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) • z) hz
    · exact hstable γ z
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
theorem Submission.f036cc6b1f_pic_psp_measurable_slice_partition :
    ∀ (Δ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) (L : Set Δ) (P S X : Set UpperHalfPlane), MeasurableSet P → MeasurableSet S → MeasurableSet X → (∀ δ : Δ, ∃ γ : Δ, γ ∈ L ∧ ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (δ : Matrix.SpecialLinearGroup (Fin 2) ℤ) ∨ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) = -(δ : Matrix.SpecialLinearGroup (Fin 2) ℤ))) → (∀ γ : Δ, γ ∈ L → ∀ η : Δ, η ∈ L → ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) = (η : Matrix.SpecialLinearGroup (Fin 2) ℤ) ∨ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) = -(η : Matrix.SpecialLinearGroup (Fin 2) ℤ)) → γ = η) → (∀ z ∈ X, ∃ r : Matrix.SpecialLinearGroup (Fin 2) ℤ, r ∈ Δ ∧ r • z ∈ S ∧ ∀ δ : Matrix.SpecialLinearGroup (Fin 2) ℤ, δ ∈ Δ → δ • z ∈ S → δ = r ∨ δ = -r) → let C : Δ → Set UpperHalfPlane := fun γ => {z | γ ∈ L ∧ z ∈ P ∩ X ∧ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) • z ∈ S}; (∀ γ, MeasurableSet (C γ)) ∧ Pairwise (fun γ η => Disjoint (C γ) (C η)) ∧ (⋃ γ, C γ) = P ∩ X := by
  intro Δ L P S X hP hS hX hcover huniq horbit
  dsimp only
  constructor
  · intro γ
    by_cases hγ : γ ∈ L
    · have hcont : Continuous (fun z : UpperHalfPlane =>
          (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) • z) := by
        change Continuous (fun z : UpperHalfPlane =>
          Matrix.SpecialLinearGroup.mapGL ℝ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) • z)
        exact continuous_const_smul _
      simpa only [hγ, true_and, Set.inter_def, Set.preimage, Set.mem_ofPred_eq] using
        (hP.inter hX).inter (hS.preimage hcont.measurable)
    · simpa only [hγ, false_and, Set.ofPred_false] using
        (MeasurableSet.empty : MeasurableSet (∅ : Set UpperHalfPlane))
  · constructor
    · intro γ η hne
      apply Set.disjoint_left.mpr
      intro z hzγ hzη
      obtain ⟨r, _, _, hr⟩ := horbit z hzγ.2.1.2
      apply hne
      apply huniq γ hzγ.1 η hzη.1
      rcases hr (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) γ.property hzγ.2.2 with hg | hg <;>
        rcases hr (η : Matrix.SpecialLinearGroup (Fin 2) ℤ) η.property hzη.2.2 with he | he
      · exact Or.inl (hg.trans he.symm)
      · exact Or.inr (by rw [hg, he, neg_neg])
      · exact Or.inr (by rw [hg, he])
      · exact Or.inl (hg.trans he.symm)
    · apply Set.Subset.antisymm
      · intro z hz
        obtain ⟨γ, hγ⟩ := Set.mem_iUnion.mp hz
        exact hγ.2.1
      · intro z hz
        obtain ⟨r, hr, hrs, _⟩ := horbit z hz.2
        obtain ⟨γ, hγ, hsgn⟩ := hcover ⟨r, hr⟩
        apply Set.mem_iUnion.mpr
        refine ⟨γ, hγ, hz, ?_⟩
        rcases hsgn with hsgn | hsgn
        · simpa only [hsgn] using hrs
        · simpa only [hsgn, ModularGroup.SL_neg_smul] using hrs

namespace Submission

theorem f036cc6b1f_pic_mec_pointwise_sign_partition
    (Δ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) (E F X : Set UpperHalfPlane)
    (hneg : (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) ∈ Δ)
    (hE : MeasurableSet E) (hF : MeasurableSet F) (hX : MeasurableSet X)
    (hinv : ∀ (γ : Δ) (z : UpperHalfPlane),
      (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) • z ∈ X ↔ z ∈ X)
    (hrep : ∀ S : Set UpperHalfPlane, (S = E ∨ S = F) → ∀ z ∈ X,
      ∃ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, γ ∈ Δ ∧ γ • z ∈ S ∧
        ∀ δ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
          δ ∈ Δ → δ • z ∈ S → δ = γ ∨ δ = -γ) :
    ∃ A B : Δ → Set UpperHalfPlane,
      (∀ γ, MeasurableSet (A γ)) ∧ (∀ γ, MeasurableSet (B γ)) ∧
      Pairwise (fun γ δ => Disjoint (A γ) (A δ)) ∧
      Pairwise (fun γ δ => Disjoint (B γ) (B δ)) ∧
      (⋃ γ, A γ) = E ∩ X ∧ (⋃ γ, B γ) = F ∩ X ∧
      (∀ γ : Δ, (fun z : UpperHalfPlane =>
        (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ)⁻¹ • z) '' (A γ) = B γ) := by
  classical
  obtain ⟨L, hcover, hunique⟩ := f036cc6b1f_pic_psp_sign_transversal Δ hneg
  -- Inversion carries a sign transversal to a sign transversal.
  let Linv : Set Δ := {γ | γ⁻¹ ∈ L}
  have hcoverInv : ∀ δ : Δ, ∃ γ : Δ, γ ∈ Linv ∧
      ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) = δ ∨
        (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) = -(δ : Matrix.SpecialLinearGroup (Fin 2) ℤ)) := by
    intro δ
    obtain ⟨γ, hγ, hsign⟩ := hcover δ⁻¹
    refine ⟨γ⁻¹, ?_, ?_⟩
    · simpa only [Linv, Set.mem_ofPred_eq, inv_inv] using hγ
    · rcases hsign with hsign | hsign
      · left
        simpa only [Subgroup.coe_inv, inv_inv] using congrArg Inv.inv hsign
      · right
        simpa only [Subgroup.coe_inv, inv_neg, inv_inv] using congrArg Inv.inv hsign
  have huniqueInv : ∀ γ : Δ, γ ∈ Linv → ∀ η : Δ, η ∈ Linv →
      ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) = η ∨
        (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) = -(η : Matrix.SpecialLinearGroup (Fin 2) ℤ)) →
      γ = η := by
    intro γ hγ η hη hsign
    apply inv_injective
    apply hunique γ⁻¹ hγ η⁻¹ hη
    rcases hsign with hsign | hsign
    · left
      simpa only [Subgroup.coe_inv] using congrArg Inv.inv hsign
    · right
      simpa only [Subgroup.coe_inv, inv_neg] using congrArg Inv.inv hsign
  let C : Δ → Set UpperHalfPlane := fun γ =>
    {z | γ ∈ Linv ∧ z ∈ E ∩ X ∧ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) • z ∈ F}
  let A : Δ → Set UpperHalfPlane := fun γ => C γ⁻¹
  let B : Δ → Set UpperHalfPlane := fun γ =>
    {z | γ ∈ L ∧ z ∈ F ∩ X ∧ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) • z ∈ E}
  obtain ⟨hCmeas, hCdisj, hCunion⟩ :=
    f036cc6b1f_pic_psp_measurable_slice_partition Δ Linv E F X hE hF hX
      hcoverInv huniqueInv (hrep F (Or.inr rfl))
  obtain ⟨hBmeas, hBdisj, hBunion⟩ :=
    f036cc6b1f_pic_psp_measurable_slice_partition Δ L F E X hF hE hX
      hcover hunique (hrep E (Or.inl rfl))
  refine ⟨A, B, (fun γ => hCmeas γ⁻¹), hBmeas, ?_, hBdisj, ?_, hBunion, ?_⟩
  · intro γ η hne
    exact hCdisj (fun h => hne (inv_injective h))
  · calc
      (⋃ γ, A γ) = ⋃ γ, C γ :=
        Set.iUnion_congr_of_surjective Inv.inv inv_surjective (fun _ => rfl)
      _ = E ∩ X := hCunion
  · intro γ
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      change (γ⁻¹)⁻¹ ∈ L ∧ z ∈ E ∩ X ∧
        ((γ⁻¹ : Δ) : Matrix.SpecialLinearGroup (Fin 2) ℤ) • z ∈ F at hz
      simp only [inv_inv, Subgroup.coe_inv] at hz
      refine ⟨hz.1, ⟨hz.2.2, (hinv γ⁻¹ z).2 hz.2.1.2⟩, ?_⟩
      simpa only [smul_inv_smul] using hz.2.1.1
    · intro hy
      change γ ∈ L ∧ y ∈ F ∩ X ∧
        (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) • y ∈ E at hy
      refine ⟨(γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) • y, ?_, inv_smul_smul _ _⟩
      change (γ⁻¹)⁻¹ ∈ L ∧
        (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) • y ∈ E ∩ X ∧
        ((γ⁻¹ : Δ) : Matrix.SpecialLinearGroup (Fin 2) ℤ) •
          ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) • y) ∈ F
      simp only [inv_inv, Subgroup.coe_inv, inv_smul_smul]
      exact ⟨hy.1, ⟨hy.2.2, (hinv γ y).2 hy.2.1.2⟩, hy.2.1.1⟩

end Submission
