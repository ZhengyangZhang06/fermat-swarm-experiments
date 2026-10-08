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


namespace Submission

/-- Measurable equidecomposition of two domains with representatives unique up to sign. -/
theorem f036cc6b1f_pic_dt_measurable_equidecomposition
    (Δ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) (E F : Set UpperHalfPlane)
    (hneg : (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) ∈ Δ)
    (hE : MeasurableSet E) (hF : MeasurableSet F)
    (hEae : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane),
      ∃ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
        γ ∈ Δ ∧ γ • z ∈ E ∧ ∀ δ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
          δ ∈ Δ → δ • z ∈ E → δ = γ ∨ δ = -γ)
    (hFae : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane),
      ∃ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
        γ ∈ Δ ∧ γ • z ∈ F ∧ ∀ δ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
          δ ∈ Δ → δ • z ∈ F → δ = γ ∨ δ = -γ) :
    ∃ A B : Δ → Set UpperHalfPlane,
      (∀ γ, MeasurableSet (A γ)) ∧ (∀ γ, MeasurableSet (B γ)) ∧
      Pairwise (fun γ δ => Disjoint (A γ) (A δ)) ∧
      Pairwise (fun γ δ => Disjoint (B γ) (B δ)) ∧
      (∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane),
        z ∈ E ↔ z ∈ ⋃ γ, A γ) ∧
      (∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane),
        z ∈ F ↔ z ∈ ⋃ γ, B γ) ∧
      (∀ γ : Δ,
        (fun z : UpperHalfPlane => (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ)⁻¹ • z) ''
          A γ = B γ) := by
  classical
  -- The representative predicates are measurable by countability of the matrix group.
  have : Countable (Matrix.SpecialLinearGroup (Fin 2) ℤ) := by
    change Countable {g : Fin 2 → Fin 2 → ℤ // Matrix.det g = 1}
    infer_instance
  have hsmul (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
      Measurable (fun z : UpperHalfPlane => γ • z) :=
    (continuous_const_smul (Matrix.SpecialLinearGroup.mapGL ℝ γ)).measurable
  let R : Set UpperHalfPlane → Set UpperHalfPlane := fun S =>
    {z | ∃ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      γ ∈ Δ ∧ γ • z ∈ S ∧ ∀ δ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
        δ ∈ Δ → δ • z ∈ S → δ = γ ∨ δ = -γ}
  have hR (S : Set UpperHalfPlane) (hS : MeasurableSet S) : MeasurableSet (R S) := by
    dsimp only [R]
    rw [Set.ofPred_exists]
    refine MeasurableSet.iUnion fun γ => ?_
    refine (MeasurableSet.const (γ ∈ Δ)).inter ((hS.preimage (hsmul γ)).inter ?_)
    change MeasurableSet {z : UpperHalfPlane |
      ∀ δ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
        δ ∈ Δ → δ • z ∈ S → δ = γ ∨ δ = -γ}
    rw [Set.ofPred_forall]
    refine MeasurableSet.iInter fun δ => ?_
    exact (MeasurableSet.const (δ ∈ Δ)).imp
      ((hS.preimage (hsmul δ)).imp (MeasurableSet.const (δ = γ ∨ δ = -γ)))
  have hRae : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure UpperHalfPlane),
      z ∈ R E ∩ R F := hEae.and hFae
  -- Restrict to the invariant conull core where both predicates hold pointwise.
  obtain ⟨X, hX, hXae, hXR, hXinv⟩ :=
    Submission.f036cc6b1f_pic_mec_invariant_conull_core Δ (R E ∩ R F)
      ((hR E hE).inter (hR F hF)) hRae
  obtain ⟨A, B, hA, hB, hAdisj, hBdisj, hAunion, hBunion, hAB⟩ :=
    Submission.f036cc6b1f_pic_mec_pointwise_sign_partition Δ E F X
      hneg hE hF hX hXinv (by
        rintro S (rfl | rfl) z hz
        · exact (hXR hz).1
        · exact (hXR hz).2)
  -- Conullness upgrades the exact covers of the intersections to almost-everywhere covers.
  refine ⟨A, B, hA, hB, hAdisj, hBdisj, ?_, ?_, hAB⟩
  · filter_upwards [hXae] with z hz
    rw [hAunion]
    exact ⟨fun h => ⟨h, hz⟩, fun h => h.1⟩
  · filter_upwards [hXae] with z hz
    rw [hBunion]
    exact ⟨fun h => ⟨h, hz⟩, fun h => h.1⟩

end Submission
