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
