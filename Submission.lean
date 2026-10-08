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

end Submission

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

end Submission

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

namespace Submission

theorem f036cc6b1f_pc_effective_domain
    (Δ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Δ.FiniteIndex]
    (hneg : (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) ∈ Δ) :
    ∃ R : Finset (Matrix.SpecialLinearGroup (Fin 2) ℤ),
      let F : Set UpperHalfPlane :=
        ⋃ r ∈ R, (fun z : UpperHalfPlane => r • z) '' ModularGroup.fd
      MeasurableSet F ∧
        (∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane),
          ∃ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
            γ ∈ Δ ∧ γ • z ∈ F ∧
              ∀ δ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
                δ ∈ Δ → δ • z ∈ F → δ = γ ∨ δ = -γ) := by
  classical
  -- Choose one representative of each right coset Δr.
  let : Fintype (Matrix.SpecialLinearGroup (Fin 2) ℤ ⧸ Δ) :=
    Subgroup.fintypeQuotientOfFiniteIndex
  let R : Finset (Matrix.SpecialLinearGroup (Fin 2) ℤ) :=
    Finset.univ.image (fun q : Quotient (QuotientGroup.rightRel Δ) => q.out)
  have hR : ∀ r ∈ R, ∀ s ∈ R, s * r⁻¹ ∈ Δ → s = r := by
    intro r hr s hs hsr
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hr
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hs
    have hqp : q = p :=
      Quotient.out_equiv_out.mp (QuotientGroup.rightRel_apply.mpr hsr)
    exact congrArg Quotient.out hqp.symm
  refine ⟨R, ?_, ?_⟩
  · apply R.measurableSet_biUnion
    intro r _
    -- The SL action is the restriction of the continuous GL action.
    change MeasurableSet
      ((fun z : UpperHalfPlane => Matrix.SpecialLinearGroup.mapGL ℝ r • z) ''
        ModularGroup.fd)
    exact (isClosedMap_smul (Matrix.SpecialLinearGroup.mapGL ℝ r)
      ModularGroup.fd ModularGroup.isClosed_fd).measurableSet
  · filter_upwards [Submission.f036cc6b1f_pc_ed_ae_orbit_interior] with z hz
    obtain ⟨g, hg⟩ := ModularGroup.exists_smul_mem_fd z
    let q : Quotient (QuotientGroup.rightRel Δ) := Quotient.mk _ g⁻¹
    let r : Matrix.SpecialLinearGroup (Fin 2) ℤ := q.out
    have hr : r ∈ R := Finset.mem_image.mpr ⟨q, Finset.mem_univ _, rfl⟩
    have hmem : g⁻¹ * r⁻¹ ∈ Δ :=
      QuotientGroup.rightRel_apply.mp (Quotient.mk_out g⁻¹)
    -- If g⁻¹ = ηr, then η⁻¹z = r(gz) lies in the finite union.
    have hγ : (g⁻¹ * r⁻¹)⁻¹ ∈ Δ := Δ.inv_mem hmem
    have hγF : (g⁻¹ * r⁻¹)⁻¹ • z ∈
        ⋃ s ∈ R, (fun w : UpperHalfPlane => s • w) '' ModularGroup.fd := by
      refine Set.mem_iUnion.mpr ⟨r, Set.mem_iUnion.mpr ⟨hr, ?_⟩⟩
      exact ⟨g • z, hg, by simp only [mul_inv_rev, inv_inv, mul_smul]⟩
    refine ⟨(g⁻¹ * r⁻¹)⁻¹, hγ, hγF, ?_⟩
    intro δ hδ hδF
    exact Submission.f036cc6b1f_pc_ed_transversal_unique Δ R hneg hR z hz
      (g⁻¹ * r⁻¹)⁻¹ δ hγ hδ hγF hδF

end Submission
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
