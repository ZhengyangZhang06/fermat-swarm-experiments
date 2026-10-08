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
