/-
Copyright 2026 Anthropic, PBC. Licensed under Apache-2.0; see LICENSE.
Source: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_groupCohomology_bijective_theta_dualTwist_of_res_of_isOpen.lean
Modified: replaced the proof with sorry and removed P2M proof imports.
Requires the upstream Definitions modules and their dependencies.
-/

import Mathlib
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_ContinuousH2Map
import Definitions.Def_GroupCohomology_ContinuousH1
import Definitions.Def_GroupCohomology_CupProduct
import Definitions.Def_GroupCohomology_ContinuousDuality
import Definitions.Def_GroupCohomology_Selmer
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
attribute [-instance] groupCohomology.normal_comap_fixingSubgroup groupCohomology.finiteIndex_comap_fixingSubgroup

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory Module groupCohomology ExtCitation
theorem groupCohomology.bijective_theta_dualTwist_of_res_of_isOpen
    {p : ℕ} [Fact p.Prime] (q : Nat.Primes)
    (S : Subgroup (primeLocalGaloisGroup q)) (U : Subgroup S) [U.FiniteIndex] (hUp : IsUnit ((U.index : ℕ) : ZMod p))
    (hU : ∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧
      F₀.fixingSubgroup.comap ((primeLocalToGlobal q).comp S.subtype) ≤ U)
    (hTU : FiniteDimensional (ZMod p) (continuousH2 (((primeLocalToGlobal q).comp S.subtype).comp U.subtype) (Rep.res U.subtype (Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))))) ∧
      finrank (ZMod p) (continuousH2 (((primeLocalToGlobal q).comp S.subtype).comp U.subtype) (Rep.res U.subtype (Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))))) = 1)
    (M : Rep.{0} (ZMod p) S) [FiniteDimensional (ZMod p) M]
    (hsm : ∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s : S, ((primeLocalToGlobal q).comp S.subtype) s ∈ F.fixingSubgroup → M.ρ s m = m)
    (inv : continuousH2 ((primeLocalToGlobal q).comp S.subtype) (Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))) →ₗ[ZMod p] ZMod p)
    (hinv : Function.Bijective inv)
    (hres : ∀ (invU : continuousH2 (((primeLocalToGlobal q).comp S.subtype).comp U.subtype) (Rep.res U.subtype (Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))))) →ₗ[ZMod p] ZMod p),
      Function.Bijective invU →
      ∀ (θ₀ : (Rep.res U.subtype M).ρ.invariants →ₗ[ZMod p] Module.Dual (ZMod p)
          (continuousH2 (((primeLocalToGlobal q).comp S.subtype).comp U.subtype) (Rep.res U.subtype (M.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype))))),
        IsTheta0 (((primeLocalToGlobal q).comp S.subtype).comp U.subtype) (Module.Dual.eval (ZMod p) M : Rep.res U.subtype M →ₗ[ZMod p]
            Rep.res U.subtype (M.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype)) →ₗ[ZMod p]
            Rep.res U.subtype (Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))))) invU θ₀ →
      ∀ (θ₁ : continuousH1 (((primeLocalToGlobal q).comp S.subtype).comp U.subtype) (Rep.res U.subtype M) →ₗ[ZMod p] Module.Dual (ZMod p)
          (continuousH1 (((primeLocalToGlobal q).comp S.subtype).comp U.subtype) (Rep.res U.subtype (M.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype))))),
        IsTheta1 (((primeLocalToGlobal q).comp S.subtype).comp U.subtype) (Module.Dual.eval (ZMod p) M : Rep.res U.subtype M →ₗ[ZMod p]
            Rep.res U.subtype (M.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype)) →ₗ[ZMod p]
            Rep.res U.subtype (Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))))) invU θ₁ →
      ∀ (θ₂ : continuousH2 (((primeLocalToGlobal q).comp S.subtype).comp U.subtype) (Rep.res U.subtype M) →ₗ[ZMod p] Module.Dual (ZMod p)
          (Rep.res U.subtype (M.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype))).ρ.invariants),
        IsTheta2 (((primeLocalToGlobal q).comp S.subtype).comp U.subtype) (Module.Dual.eval (ZMod p) M : Rep.res U.subtype M →ₗ[ZMod p]
            Rep.res U.subtype (M.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype)) →ₗ[ZMod p]
            Rep.res U.subtype (Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))))) invU θ₂ →
      Function.Bijective θ₀ ∧ Function.Bijective θ₁ ∧ Function.Bijective θ₂)
    (θ₀ : M.ρ.invariants →ₗ[ZMod p] Module.Dual (ZMod p) (continuousH2 ((primeLocalToGlobal q).comp S.subtype) (M.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype))))
    (hθ₀ : IsTheta0 ((primeLocalToGlobal q).comp S.subtype) (Module.Dual.eval (ZMod p) M : M →ₗ[ZMod p] M.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype) →ₗ[ZMod p]
        Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))) inv θ₀)
    (θ₁ : continuousH1 ((primeLocalToGlobal q).comp S.subtype) M →ₗ[ZMod p] Module.Dual (ZMod p) (continuousH1 ((primeLocalToGlobal q).comp S.subtype) (M.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype))))
    (hθ₁ : IsTheta1 ((primeLocalToGlobal q).comp S.subtype) (Module.Dual.eval (ZMod p) M : M →ₗ[ZMod p] M.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype) →ₗ[ZMod p]
        Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))) inv θ₁)
    (θ₂ : continuousH2 ((primeLocalToGlobal q).comp S.subtype) M →ₗ[ZMod p] Module.Dual (ZMod p) (M.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype)).ρ.invariants)
    (hθ₂ : IsTheta2 ((primeLocalToGlobal q).comp S.subtype) (Module.Dual.eval (ZMod p) M : M →ₗ[ZMod p] M.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype) →ₗ[ZMod p]
        Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))) inv θ₂) :
    Function.Bijective θ₀ ∧ Function.Bijective θ₁ ∧ Function.Bijective θ₂ := by
  sorry

theorem Submission.p08_7d1ff633a4_ck_uniform_stabilizer :
    ∀ {k G : Type} [Field k] [Group G]
      (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
      (M : Rep.{0} k G) [FiniteDimensional k M],
      (∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ),
        FiniteDimensional ℚ F ∧
        ∀ g : G, r g ∈ F.fixingSubgroup → M.ρ g m = m) →
      ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
        ∀ g : G, r g ∈ F.fixingSubgroup → ∀ m : M, M.ρ g m = m := by
  classical
  intro k G _ _ r M _ h
  let b : Basis (Fin (finrank k M)) k M := Module.finBasis k M
  choose F hF hfix using fun i => h (b i)
  let : ∀ i, FiniteDimensional ℚ (F i) := hF
  refine ⟨⨆ i, F i, inferInstance, ?_⟩
  intro g hg m
  have hρ : M.ρ g = LinearMap.id := b.ext fun i =>
    hfix i g (IntermediateField.fixingSubgroup_le (le_iSup F i) hg)
  exact LinearMap.congr_fun hρ m
theorem Submission.p08_7d1ff633a4_ck_cyclotomic_kernel :
    ∀ {p : ℕ} [Fact p.Prime],
      ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
          σ ∈ F.fixingSubgroup → ExtCitation.cycloChar p σ = 1 := by
  classical
  intro p hp
  let : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  let R : Set (AlgebraicClosure ℚ) :=
    Set.range (fun t : rootsOfUnity p (AlgebraicClosure ℚ) =>
      ((t : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ))
  have : Finite R := (Set.finite_range _).to_subtype
  refine ⟨IntermediateField.adjoin ℚ R,
    IntermediateField.finiteDimensional_adjoin ?_, ?_⟩
  · rintro x ⟨t, rfl⟩
    refine ⟨Polynomial.X ^ p - 1, ?_, ?_⟩
    · simpa only [Polynomial.C_1] using
        Polynomial.monic_X_pow_sub_C (1 : ℚ) (NeZero.ne p)
    · simpa only [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
        Polynomial.eval₂_one, sub_eq_zero] using
        (mem_rootsOfUnity' p (t : (AlgebraicClosure ℚ)ˣ)).mp t.property
  intro σ hσ
  apply Units.ext
  change (modularCyclotomicCharacter (AlgebraicClosure ℚ)
    (ExtCitation.card_rootsOfUnity_eq_self p) σ : ZMod p) = 1
  symm
  apply modularCyclotomicCharacter.unique
  intro t ht
  change σ (t : AlgebraicClosure ℚ) = (t : AlgebraicClosure ℚ) ^ (1 : ZMod p).val
  have htF : (t : AlgebraicClosure ℚ) ∈ IntermediateField.adjoin ℚ R :=
    IntermediateField.subset_adjoin ℚ R ⟨⟨t, ht⟩, rfl⟩
  simpa only [ZMod.val_one'' (Fact.out : p.Prime).ne_one, pow_one] using
    ((IntermediateField.mem_fixingSubgroup_iff _ σ).mp hσ) (t : AlgebraicClosure ℚ) htF
theorem Submission.p08_7d1ff633a4_normal_refinement :
    ∀ {ι : Type} [Finite ι] (F : ι → IntermediateField ℚ (AlgebraicClosure ℚ)),
      (∀ i, FiniteDimensional ℚ (F i)) →
      ∃ E : IntermediateField ℚ (AlgebraicClosure ℚ),
        FiniteDimensional ℚ E ∧ Normal ℚ E ∧ (∀ i, F i ≤ E) ∧
          E.fixingSubgroup.Normal ∧ E.fixingSubgroup.FiniteIndex := by
  intro ι _ F hF
  let : ∀ i, FiniteDimensional ℚ (F i) := hF
  have : IsAlgClosure ℚ (AlgebraicClosure ℚ) :=
    ⟨AlgebraicClosure.isAlgClosed ℚ, AlgebraicClosure.isAlgebraic ℚ⟩
  have : Normal ℚ (AlgebraicClosure ℚ) := IsAlgClosure.normal ℚ _
  let K : IntermediateField ℚ (AlgebraicClosure ℚ) := iSup F
  let E := IntermediateField.normalClosure ℚ K (AlgebraicClosure ℚ)
  have : FiniteDimensional ℚ K :=
    IntermediateField.finiteDimensional_iSup_of_finite
  have : FiniteDimensional ℚ E := normalClosure.is_finiteDimensional ℚ K _
  have : Normal ℚ E := normalClosure.normal ℚ K _
  refine ⟨E, inferInstance, inferInstance, ?_, ?_, ?_⟩
  · intro i
    exact (le_iSup F i).trans (IntermediateField.le_normalClosure K)
  · rw [← IntermediateField.restrictNormalHom_ker E]
    infer_instance
  · rw [← IntermediateField.restrictNormalHom_ker E]
    infer_instance
