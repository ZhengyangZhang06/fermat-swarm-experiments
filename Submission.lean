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

theorem Submission.f036cc6b1f_pic_dt_integral_of_equidecomposition :
    ∀ (α ι : Type) [MeasurableSpace α] [Countable ι]
      (μ : MeasureTheory.Measure α) (E F : Set α) (A B : ι → Set α) (T : ι → α → α),
      MeasurableSet E → MeasurableSet F →
      (∀ i, MeasurableSet (A i)) → (∀ i, MeasurableSet (B i)) →
      Pairwise (fun i j => Disjoint (A i) (A j)) →
      Pairwise (fun i j => Disjoint (B i) (B j)) →
      (∀ᵐ x ∂μ, x ∈ E ↔ x ∈ ⋃ i, A i) →
      (∀ᵐ x ∂μ, x ∈ F ↔ x ∈ ⋃ i, B i) →
      (∀ i, MeasurableEmbedding (T i)) →
      (∀ i, MeasureTheory.MeasurePreserving (T i) μ μ) →
      (∀ i, T i '' A i = B i) → ∀ φ : α → ℂ,
      MeasureTheory.StronglyMeasurable φ →
      (∀ i, ∀ x ∈ A i, φ (T i x) = φ x) →
      MeasureTheory.IntegrableOn φ E μ →
      MeasureTheory.IntegrableOn φ F μ ∧ MeasureTheory.integral (μ.restrict E) φ = MeasureTheory.integral (μ.restrict F) φ := by
  intro α ι _ _ μ E F A B T _hE _hF hA hB hdA hdB hEU hFV hemb hpres himage
    φ hφ hinv hφE
  have hμE : μ.restrict E = μ.restrict (⋃ i, A i) :=
    MeasureTheory.Measure.restrict_congr_set (hEU.mono fun _ hx => propext hx)
  have hμF : μ.restrict F = μ.restrict (⋃ i, B i) :=
    MeasureTheory.Measure.restrict_congr_set (hFV.mono fun _ hx => propext hx)
  rw [MeasureTheory.IntegrableOn, hμE] at hφE
  change MeasureTheory.Integrable φ (μ.restrict F) ∧ _
  rw [hμE, hμF]
  have htransport : ∀ i, MeasureTheory.MeasurePreserving (T i) (μ.restrict (A i))
      (μ.restrict (B i)) := by
    intro i
    simpa only [himage i] using (hpres i).restrict_image_emb (hemb i) (A i)
  have hnorm : ∀ i,
      (∫⁻ x in A i, ENNReal.ofReal ‖φ x‖ ∂μ) =
        ∫⁻ x in B i, ENNReal.ofReal ‖φ x‖ ∂μ := by
    intro i
    calc
      (∫⁻ x in A i, ENNReal.ofReal ‖φ x‖ ∂μ) =
          ∫⁻ x in A i, ENNReal.ofReal ‖φ (T i x)‖ ∂μ :=
        MeasureTheory.setLIntegral_congr_fun (hA i) (fun x hx => by rw [hinv i x hx])
      _ = ∫⁻ x in B i, ENNReal.ofReal ‖φ x‖ ∂μ :=
        (htransport i).lintegral_comp_emb (hemb i) (fun x => ENNReal.ofReal ‖φ x‖)
  have hnormUnion :
      (∫⁻ x in ⋃ i, A i, ENNReal.ofReal ‖φ x‖ ∂μ) =
        ∫⁻ x in ⋃ i, B i, ENNReal.ofReal ‖φ x‖ ∂μ := by
    rw [MeasureTheory.lintegral_iUnion hA hdA, MeasureTheory.lintegral_iUnion hB hdB]
    exact tsum_congr hnorm
  have hφB : MeasureTheory.IntegrableOn φ (⋃ i, B i) μ := by
    refine ⟨hφ.aestronglyMeasurable, (MeasureTheory.hasFiniteIntegral_iff_norm φ).2 ?_⟩
    rw [← hnormUnion]
    exact (MeasureTheory.hasFiniteIntegral_iff_norm φ).1 hφE.2
  refine ⟨hφB, ?_⟩
  rw [MeasureTheory.integral_iUnion hA hdA hφE, MeasureTheory.integral_iUnion hB hdB hφB]
  apply tsum_congr
  intro i
  calc
    (∫ x in A i, φ x ∂μ) = ∫ x in A i, φ (T i x) ∂μ :=
      MeasureTheory.setIntegral_congr_fun (hA i) (fun x hx => (hinv i x hx).symm)
    _ = ∫ x in B i, φ x ∂μ := (htransport i).integral_comp (hemb i) φ
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

end Submission

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
open ModularForm ModularFormClass
open P2MW.S_ModularForm_mdifferentiable_heckeT.M4cP1W2

namespace Submission

/-- Good-prime weight-two Hecke operators commute on cusp forms of level `M`. -/
theorem f036cc6b1f_hecke_commute :
    ∀ (M : ℕ) [NeZero M] (p r : ℕ) (hp : p.Prime) (hr : r.Prime)
      (hpM : ¬ p ∣ M) (hrM : ¬ r ∣ M),
      (CuspForm.heckeTLin 2 hp hpM).comp (CuspForm.heckeTLin 2 hr hrM) =
        (CuspForm.heckeTLin 2 hr hrM).comp (CuspForm.heckeTLin 2 hp hpM) := by
  intro M _ p r hp hr hpM hrM
  by_cases hpr : p = r
  · subst r
    rfl
  have hcop : p.Coprime r := (Nat.coprime_primes hp hr).mpr hpr
  have hpr' : ¬ p ∣ r := hp.coprime_iff_not_dvd.mp hcop
  have hrp' : ¬ r ∣ p := hr.coprime_iff_not_dvd.mp hcop.symm
  have hΓ : (1 : ℝ) ∈
      (CongruenceSubgroup.Gamma0 M : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
    simp
  -- P2M/Sol/S_ModularForm_mdifferentiable_heckeT.lean, already present at
  -- proof base 674e47109a2c121849b48a3754cad6d3c648d80e, proves this coefficient
  -- formula for the exact bundled Hecke normalization and qCoeff uniqueness below.
  have hcoeff (s : ℕ) (hs : s.Prime) (hsM : ¬ s ∣ M)
      (g : CuspForm (CongruenceSubgroup.Gamma0 M) 2) :
      qCoeff (CuspForm.heckeTLin 2 hs hsM g) = coeffHeckeT 2 s (qCoeff g) := by
    funext n
    exact qCoeff_heckeT_class hs.ne_zero g hΓ n
  refine LinearMap.ext fun f => eq_of_forall_qCoeff_eq hΓ fun n => ?_
  change qCoeff (CuspForm.heckeTLin 2 hp hpM (CuspForm.heckeTLin 2 hr hrM f)) n =
    qCoeff (CuspForm.heckeTLin 2 hr hrM (CuspForm.heckeTLin 2 hp hpM f)) n
  rw [hcoeff p hp hpM, hcoeff r hr hrM, hcoeff r hr hrM, hcoeff p hp hpM]
  simp only [coeffHeckeT_apply, show (2 : ℤ) - 1 = 1 from rfl, zpow_one,
    hp.dvd_mul, hr.dvd_mul, hpr', hrp', or_false]
  -- These four divisibility cases also include the constant coefficient `n = 0`.
  by_cases hpn : p ∣ n <;> by_cases hrn : r ∣ n
  · have hrnp : r ∣ n / p :=
      (Nat.dvd_div_iff_mul_dvd hpn).mpr (hcop.mul_dvd_of_dvd_of_dvd hpn hrn)
    have hpnr : p ∣ n / r :=
      (Nat.dvd_div_iff_mul_dvd hrn).mpr (hcop.symm.mul_dvd_of_dvd_of_dvd hrn hpn)
    simp only [if_pos hpn, if_pos hrn, if_pos hrnp, if_pos hpnr]
    rw [Nat.mul_comm n p, Nat.mul_comm n r, Nat.mul_div_assoc p hrn,
      Nat.mul_div_assoc r hpn]
    simp only [Nat.div_div_eq_div_mul, Nat.mul_comm, Nat.mul_left_comm]
    ring
  · have hrnp : ¬ r ∣ n / p := fun h => hrn (dvd_trans h (Nat.div_dvd_of_dvd hpn))
    simp only [if_pos hpn, if_neg hrn, if_neg hrnp, add_zero]
    rw [Nat.mul_comm n r, Nat.mul_div_assoc r hpn]
    simp only [Nat.mul_comm, Nat.mul_left_comm]
  · have hpnr : ¬ p ∣ n / r := fun h => hpn (dvd_trans h (Nat.div_dvd_of_dvd hrn))
    simp only [if_neg hpn, if_pos hrn, if_neg hpnr, add_zero]
    rw [Nat.mul_comm n p, Nat.mul_div_assoc p hrn]
    simp only [Nat.mul_comm, Nat.mul_left_comm]
  · simp only [if_neg hpn, if_neg hrn, add_zero]
    congr 1
    exact Nat.mul_right_comm n p r

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
