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
