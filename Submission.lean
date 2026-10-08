/-
Copyright 2026 Anthropic, PBC. Licensed under Apache-2.0; see LICENSE.
Source: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_AlgebraicCurve_hasPrincipalDivisors_of_transcendental.lean
Modified: replaced the proof with sorry and removed P2M proof imports.
Requires the upstream Definitions modules and their dependencies.
-/

import Definitions.Def_AlgebraicCurve_PlacesOverDVR
attribute [-instance] AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy
attribute [-simp] AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul
attribute [-simp] AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply

open AlgebraicCurve

theorem AlgebraicCurve.hasPrincipalDivisors_of_transcendental (K : Type*) [Field K] [CharZero K] {F : Type*} [Field F]
    [Algebra K F] (x : F) (hx : Transcendental K x)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F] : HasPrincipalDivisors K F := by
  sorry

namespace Submission

open AlgebraicCurve

theorem AlgebraicCurve.hasPrincipalDivisors_of_transcendental (K : Type*) [Field K] [CharZero K] {F : Type*} [Field F]
    [Algebra K F] (x : F) (hx : Transcendental K x)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F] : HasPrincipalDivisors K F := by
  sorry

import Definitions.Def_AlgebraicCurve_PlacesOverDVR
attribute [-instance] AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy
attribute [-simp] AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul
attribute [-simp] AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.Localization.Module
import Mathlib.RingTheory.Length

open AlgebraicCurve
theorem AlgebraicCurve.hasPrincipalDivisors_of_transcendental (K : Type*) [Field K] [CharZero K] {F : Type*} [Field F]
    [Algebra K F] (x : F) (hx : Transcendental K x)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F] : HasPrincipalDivisors K F := by
  sorry

set_option warningAsError true

namespace Submission

/-- A principal quotient of finite `A`-length has a `B`-composition series whose factors
are residue modules at height-one primes. The element `b` annihilates every factor,
so `b ≠ 0` rules out the zero ideal in the simple-module classification. -/
theorem p06_9e0f5043ff_wll_residue_composition_series :
    ∀ (A B : Type*) [CommRing A] [CommRing B] [IsDedekindDomain B] [Algebra A B]
      (b : B), b ≠ 0 → ∀ n : ℕ,
      Module.length A (B ⧸ Ideal.span ({b} : Set B)) = (n : ℕ∞) →
      ∃ s : CompositionSeries (Submodule B (B ⧸ Ideal.span ({b} : Set B))),
        s.head = ⊥ ∧ s.last = ⊤ ∧
        ∃ p : Fin s.length → IsDedekindDomain.HeightOneSpectrum B,
          ∀ i : Fin s.length,
            Nonempty ((↥(s i.succ) ⧸ (s i.castSucc).comap (s i.succ).subtype) ≃ₗ[B]
              (B ⧸ (p i).asIdeal)) := by
  intro A B _ _ _ _ b hb n hn
  classical
  let C := B ⧸ Ideal.span ({b} : Set B)
  -- Restricting scalars embeds the B-submodule lattice into the A-submodule lattice.
  have hfinite : IsFiniteLength A C := Module.length_ne_top_iff.mp (by
    rw [hn]
    exact ENat.natCast_ne_top n)
  obtain ⟨hnoeth, hart⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp hfinite
  have : IsNoetherian B C := isNoetherian_of_tower A hnoeth
  have : IsArtinian B C := isArtinian_of_tower A hart
  obtain ⟨s, hs_head, hs_last⟩ := exists_compositionSeries_of_isNoetherian_isArtinian B C
  refine ⟨s, hs_head, hs_last, ?_⟩
  -- The same nonzero element annihilates C and every subquotient of C.
  have hbC : b ∈ Module.annihilator B C := by
    rw [Ideal.annihilator_quotient]
    exact Ideal.subset_span (Set.mem_singleton b)
  have factors : ∀ i : Fin s.length, ∃ p : IsDedekindDomain.HeightOneSpectrum B,
      Nonempty ((↥(s i.succ) ⧸ (s i.castSucc).comap (s i.succ).subtype) ≃ₗ[B]
        (B ⧸ p.asIdeal)) := by
    intro i
    let N := (s i.castSucc).comap (s i.succ).subtype
    -- A covering step has a simple quotient, hence is a maximal-ideal quotient.
    have hsimple : IsSimpleModule B (↥(s i.succ) ⧸ N) :=
      (covBy_iff_quot_is_simple (s.step i).le).mp (s.step i)
    obtain ⟨m, hm, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp hsimple
    have hbN : b ∈ Module.annihilator B (s i.succ) :=
      (s i.succ).subtype.annihilator_le_of_injective (Submodule.injective_subtype _) hbC
    have hbS : b ∈ Module.annihilator B (↥(s i.succ) ⧸ N) :=
      N.mkQ.annihilator_le_of_surjective N.mkQ_surjective hbN
    have hbm : b ∈ m := by
      rwa [e.annihilator_eq, Ideal.annihilator_quotient] at hbS
    -- Containing b excludes the zero ideal, giving a height-one prime.
    have hm_ne : m ≠ ⊥ := by
      intro hm_bot
      exact hb (by simpa [hm_bot] using hbm)
    exact ⟨⟨m, hm.isPrime, hm_ne⟩, ⟨e⟩⟩
  choose p hp using factors
  exact ⟨p, hp⟩

/-- Compute the length over `A` by summing the residue factors of a composition series over `B`.
The sum is in `ℕ∞`, so the factors need not have finite length over `A`.
Apply `Module.length_eq_add_of_exact` after restricting scalars, then induct on the
number of factors using `Fin.sum_univ_castSucc`, including the empty series. -/
theorem p06_9e0f5043ff_wll_length_sum_factors
    (A B M : Type*) [CommRing A] [CommRing B] [IsDedekindDomain B] [Algebra A B]
    [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
    (s : CompositionSeries (Submodule B M))
    (p : Fin s.length → IsDedekindDomain.HeightOneSpectrum B)
    (hhead : s.head = ⊥) (hlast : s.last = ⊤)
    (hfactors : ∀ i : Fin s.length,
      Nonempty ((↥(s i.succ) ⧸ (s i.castSucc).comap (s i.succ).subtype) ≃ₗ[B]
        (B ⧸ (p i).asIdeal))) :
    Module.length A M =
      Finset.sum Finset.univ (fun i : Fin s.length => Module.length A (B ⧸ (p i).asIdeal)) := by
  -- Restrict each short exact sequence and its factor equivalence to A.
  have hstep (i : Fin s.length) :
      Module.length A (s i.succ) =
        Module.length A (s i.castSucc) + Module.length A (B ⧸ (p i).asIdeal) := by
    obtain ⟨e⟩ := hfactors i
    let N := (s i.castSucc).comap (s i.succ).subtype
    have h := Module.length_eq_add_of_exact
      (N.subtype.restrictScalars A) (N.mkQ.restrictScalars A)
      N.subtype_injective N.mkQ_surjective (LinearMap.exact_subtype_mkQ N)
    rw [(Submodule.comapSubtypeEquivOfLe (s.lt_succ i).le).restrictScalars A |>.length_eq,
      (e.restrictScalars A).length_eq] at h
    exact h
  -- Sum by induction in ℕ∞; cancellation would require extra finiteness.
  have hsum : ∀ (n : ℕ) (f : Fin (n + 1) → ℕ∞) (g : Fin n → ℕ∞),
      (∀ i, f i.succ = f i.castSucc + g i) →
      f (Fin.last n) = f 0 + ∑ i, g i := by
    intro n
    induction n with
    | zero =>
      intro f g h
      simp
    | succ n ih =>
      intro f g h
      change f (Fin.last n).succ = _
      rw [h (Fin.last n), ih (fun i => f i.castSucc) (fun i => g i.castSucc)
        (fun i => h i.castSucc), Fin.sum_univ_castSucc, add_assoc, Fin.castSucc_zero]
  -- Identify the zero and top endpoints with the zero module and M.
  have h := hsum s.length (fun i => Module.length A (s i))
    (fun i => Module.length A (B ⧸ (p i).asIdeal)) hstep
  change Module.length A s.last = Module.length A s.head + _ at h
  rw [hhead, hlast, Module.length_eq_zero (R := A) (M := (⊥ : Submodule B M)), zero_add] at h
  rw [← (Submodule.topEquiv (R := B) (M := M)).restrictScalars A |>.length_eq]
  exact h

/-- An integer order characterizing subring membership makes every ideal principal. -/
theorem p06_9e0f5043ff_elp_principal_ideals_of_order :
    ∀ (F : Type*) [Field F] (A : Subring F) (ν : F → ℤ),
      (∀ f g : F, f ≠ 0 → g ≠ 0 → ν (f / g) = ν f - ν g) →
      (∀ f : F, f ≠ 0 → (f ∈ A ↔ 0 ≤ ν f)) → IsPrincipalIdealRing A := by
  intro F _ A ν hdiv hmem
  classical
  constructor
  intro I
  by_cases hI : I = ⊥
  · subst I
    infer_instance
  obtain ⟨z, hzI, hz⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  -- Minimize natural orders; subring membership will recover their integer values.
  have hex : ∃ n : ℕ, ∃ h : A, h ∈ I ∧ (h : F) ≠ 0 ∧ (ν (h : F)).toNat = n :=
    ⟨_, z, hzI, fun h => hz (Subtype.ext h), rfl⟩
  obtain ⟨h, hhI, hh, hν⟩ := Nat.find_spec hex
  refine ⟨⟨h, le_antisymm ?_ ((Ideal.span_singleton_le_iff_mem I).mpr hhI)⟩⟩
  intro z hzI
  by_cases hz : (z : F) = 0
  · have hz' : z = 0 := Subtype.ext hz
    rw [hz']
    exact Ideal.zero_mem _
  have hh_nonneg : 0 ≤ ν (h : F) := (hmem _ hh).mp h.property
  have hz_nonneg : 0 ≤ ν (z : F) := (hmem _ hz).mp z.property
  have hmin : (ν (h : F)).toNat ≤ (ν (z : F)).toNat := by
    rw [hν]
    exact Nat.find_min' hex ⟨z, hzI, hz, rfl⟩
  have horder : ν (h : F) ≤ ν (z : F) := by
    simpa only [Int.toNat_of_nonneg hh_nonneg, Int.toNat_of_nonneg hz_nonneg] using
      (Int.ofNat_le.mpr hmin)
  -- Leastness makes the quotient an element of A, giving the required multiple of h.
  have hquot : (z : F) / (h : F) ∈ A := by
    apply (hmem _ (div_ne_zero hz hh)).mpr
    rw [hdiv _ _ hz hh]
    exact sub_nonneg.mpr horder
  apply Ideal.mem_span_singleton'.mpr
  refine ⟨⟨(z : F) / (h : F), hquot⟩, ?_⟩
  apply Subtype.ext
  exact div_mul_cancel₀ _ hh

/-- Clear the first row by an invertible column operation, preserving the trailing block.
The correction matrix squares to zero, so `1 - M` has the explicit inverse `1 + M`.
Divisibility supplies the coefficients without requiring the pivot to be nonzero or a unit. -/
theorem p06_9e0f5043ff_sdp_clear_first_row :
    ∀ (R : Type*) [CommRing R] (m : ℕ)
      (H : Matrix (Fin (m + 1)) (Fin (m + 1)) R),
      (∀ i : Fin m, H i.succ 0 = 0) →
      (∀ j : Fin m, H 0 0 ∣ H 0 j.succ) →
      ∃ V : Matrix (Fin (m + 1)) (Fin (m + 1)) R,
        IsUnit V ∧ H * V = Matrix.of (fun i j =>
          Fin.cases (Fin.cases (H 0 0) (fun _ => 0) j)
            (fun i' => Fin.cases 0 (fun j' => H i'.succ j'.succ) j) i) := by
  classical
  intro R _ m H hcol hdiv
  choose b hb using hdiv
  let M : Matrix (Fin (m + 1)) (Fin (m + 1)) R :=
    Matrix.of (fun i j => Fin.cases (Fin.cases 0 b j) (fun _ => 0) i)
  have hM0 (i : Fin (m + 1)) : M i 0 = 0 := by
    refine Fin.cases ?_ (fun _ => ?_) i <;> rfl
  have hMs (i : Fin m) (j : Fin (m + 1)) : M i.succ j = 0 := rfl
  have hMM : M * M = 0 := by
    ext i j
    simp [Matrix.mul_apply, Fin.sum_univ_succ, hM0, hMs]
  have hHM (i j : Fin (m + 1)) :
      (H * M) i j = H i 0 * Fin.cases 0 b j := by
    simp [Matrix.mul_apply, Fin.sum_univ_succ, M]
  refine ⟨1 - M, ?_, ?_⟩
  · refine ⟨⟨1 - M, 1 + M, ?_, ?_⟩, rfl⟩
    · simp [sub_mul, mul_add, hMM]
    · simp [mul_sub, add_mul, hMM]
  · rw [mul_sub, mul_one]
    ext i j
    refine Fin.cases ?_ (fun i' => ?_) i <;>
      refine Fin.cases ?_ (fun j' => ?_) j <;>
      simp [Matrix.sub_apply, hHM, hcol, hb]
/-- Clear the first column below a divisible pivot by a unit that preserves the first row. -/
theorem p06_9e0f5043ff_sdp_clear_first_column
    (R : Type*) [CommRing R] (m : ℕ)
    (B : Matrix (Fin (m + 1)) (Fin (m + 1)) R)
    (h : ∀ i : Fin m, B 0 0 ∣ B i.succ 0) :
    ∃ U : Matrix (Fin (m + 1)) (Fin (m + 1)) R,
      IsUnit U ∧ (∀ j : Fin (m + 1), (U * B) 0 j = B 0 j) ∧
        (∀ i : Fin m, (U * B) i.succ 0 = 0) := by
  classical
  choose a ha using h
  -- Extend the chosen coefficients by zero so the first row is unchanged.
  let c : Fin (m + 1) → R := Fin.cases 0 a
  let N : Matrix (Fin (m + 1)) (Fin (m + 1)) R :=
    Matrix.of fun i j => if j = 0 then c i else 0
  have hmul (M : Matrix (Fin (m + 1)) (Fin (m + 1)) R)
      (i j : Fin (m + 1)) : (N * M) i j = c i * M 0 j := by
    simp [Matrix.mul_apply, N]
  have hsq : N * N = 0 := by
    ext i j
    simp [hmul, N, c]
  -- Since N² = 0, the clearing matrix 1 - N has two-sided inverse 1 + N.
  refine ⟨1 - N, ?_, ?_, ?_⟩
  · refine ⟨⟨1 - N, 1 + N, ?_, ?_⟩, rfl⟩
    · simp [sub_mul, mul_add, hsq]
    · simp [mul_sub, add_mul, hsq]
  · intro j
    simp [sub_mul, hmul, c]
  · intro i
    simp [sub_mul, hmul, c, ha i, mul_comm]
/-- A finite family in a DVR with a nonzero entry has a nonzero member dividing every entry.
Choose a member of minimum uniformizer exponent among the nonzero entries. Unit factors
do not affect divisibility, and the minimum power divides every other power. -/
theorem p06_9e0f5043ff_dmd_finite_family_dividing_member
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (ι : Type*) [Fintype ι] (a : ι → A) (ha : ∃ i, a i ≠ 0) :
    ∃ i, a i ≠ 0 ∧ ∀ j, a i ∣ a j := by
  classical
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  let S := {i : ι // a i ≠ 0}
  have hfactor : ∀ i : S, ∃ (n : ℕ) (u : Aˣ), a i = u * π ^ n :=
    fun i => IsDiscreteValuationRing.eq_unit_mul_pow_irreducible i.property hπ
  choose e u he using hfactor
  have hS : (Finset.univ : Finset S).Nonempty := by
    obtain ⟨i, hi⟩ := ha
    exact ⟨⟨i, hi⟩, Finset.mem_univ _⟩
  -- Minimize the uniformizer exponent among the nonzero entries.
  obtain ⟨i, _, hmin⟩ := Finset.exists_min_image Finset.univ e hS
  refine ⟨i.val, i.property, ?_⟩
  intro j
  by_cases hj : a j = 0
  · rw [hj]
    exact dvd_zero _
  · rw [he i, he ⟨j, hj⟩, Units.mul_left_dvd, Units.dvd_mul_left]
    exact pow_dvd_pow π (hmin ⟨j, hj⟩ (Finset.mem_univ _))
/-- Polynomial evaluation at the finite place has residue kernel generated by `q`. -/
theorem p06_9e0f5043ff_fpm_rd_eval_kernel
    (K F : Type*) [Field K] [Field F] [Algebra K F] (x : F)
    (hx : Transcendental K x) (q : Polynomial K) (hq : Irreducible q)
    (v : AlgebraicCurve.Place K F)
    (hv : ∀ f : F, f ∈ v.toValuationSubring ↔
      ∃ a b : Polynomial K, ¬ q ∣ b ∧
        f = Polynomial.aeval x a / Polynomial.aeval x b) :
    ∃ e : Polynomial K →ₐ[K] v.toValuationSubring,
      (∀ a : Polynomial K, (e a : F) = Polynomial.aeval x a) ∧
      RingHom.ker ((IsLocalRing.residue v.toValuationSubring).comp e.toRingHom) =
        Ideal.span ({q} : Set (Polynomial K)) := by
  classical
  have hinj := transcendental_iff_injective.mp hx
  have hne (a : Polynomial K) (ha : a ≠ 0) : Polynomial.aeval x a ≠ 0 := by
    intro h
    exact ha (hinj (h.trans (map_zero (Polynomial.aeval x)).symm))
  -- Denominator 1 lifts every polynomial evaluation into the valuation ring.
  have hmem (a : Polynomial K) : Polynomial.aeval x a ∈ v.toValuationSubring :=
    (hv _).mpr ⟨a, 1, hq.not_dvd_one, by rw [map_one, div_one]⟩
  let e : Polynomial K →ₐ[K] v.toValuationSubring :=
    { toFun := fun a => ⟨Polynomial.aeval x a, hmem a⟩
      map_one' := Subtype.ext (map_one (Polynomial.aeval x))
      map_mul' := fun a b => Subtype.ext (map_mul (Polynomial.aeval x) a b)
      map_zero' := Subtype.ext (map_zero (Polynomial.aeval x))
      map_add' := fun a b => Subtype.ext (map_add (Polynomial.aeval x) a b)
      commutes' := fun c => Subtype.ext ((Polynomial.aeval x).commutes c) }
  have he (a : Polynomial K) : (e a : F) = Polynomial.aeval x a := rfl
  -- A polynomial not divisible by q has an inverse evaluation in the valuation ring.
  have hunit (a : Polynomial K) (ha : ¬ q ∣ a) : IsUnit (e a) := by
    have ha0 : Polynomial.aeval x a ≠ 0 := hne a (fun h => ha (h ▸ dvd_zero q))
    have hi : (Polynomial.aeval x a)⁻¹ ∈ v.toValuationSubring :=
      (hv _).mpr ⟨1, a, ha, by rw [map_one, one_div]⟩
    exact isUnit_iff_exists_inv.mpr
      ⟨⟨(Polynomial.aeval x a)⁻¹, hi⟩, Subtype.ext (mul_inv_cancel₀ ha0)⟩
  -- An inverse of q(x) would force q to divide an allowed denominator.
  have hq_nonunit : ¬ IsUnit (e q) := by
    intro hu
    obtain ⟨z, hz⟩ := isUnit_iff_exists_inv.mp hu
    have hmul : Polynomial.aeval x q * (z : F) = 1 :=
      congrArg (fun t : v.toValuationSubring => (t : F)) hz
    obtain ⟨a, b, hb, hzrep⟩ := (hv (z : F)).mp z.property
    have hb0 : Polynomial.aeval x b ≠ 0 := hne b (fun h => hb (h ▸ dvd_zero q))
    have hab : Polynomial.aeval x q * Polynomial.aeval x a = Polynomial.aeval x b := by
      calc
        Polynomial.aeval x q * Polynomial.aeval x a =
            (Polynomial.aeval x q * (z : F)) * Polynomial.aeval x b := by
          rw [hzrep, ← mul_div_assoc, div_mul_cancel₀ _ hb0]
        _ = Polynomial.aeval x b := by rw [hmul, one_mul]
    apply hb
    refine ⟨a, hinj ?_⟩
    rw [map_mul]
    exact hab.symm
  have hq_zero : IsLocalRing.residue v.toValuationSubring (e q) = 0 := by
    by_contra h
    exact hq_nonunit ((IsLocalRing.residue_ne_zero_iff_isUnit _).mp h)
  refine ⟨e, he, ?_⟩
  ext a
  rw [RingHom.mem_ker, Ideal.mem_span_singleton]
  change IsLocalRing.residue v.toValuationSubring (e a) = 0 ↔ q ∣ a
  constructor
  · intro ha
    by_contra hqa
    exact ((IsLocalRing.residue_ne_zero_iff_isUnit _).mpr (hunit a hqa)) ha
  · rintro ⟨b, rfl⟩
    rw [map_mul, map_mul, hq_zero, zero_mul]
open scoped BigOperators

/-- Length after localization is the sum of the localized successive quotient lengths.
The equality is in `ℕ∞`; the proof uses addition only and needs no finite-length hypothesis. -/
theorem p06_9e0f5043ff_llm_localized_series_sum
    (B M : Type*) [CommRing B] [AddCommGroup M] [Module B M]
    (T : Submonoid B) (s : CompositionSeries (Submodule B M))
    (hhead : s.head = ⊥) (hlast : s.last = ⊤) :
    Module.length (Localization T) (LocalizedModule T M) =
      Finset.sum Finset.univ (fun i : Fin s.length =>
        Module.length (Localization T)
          (LocalizedModule T (↥(s i.succ) ⧸ (s i.castSucc).comap (s i.succ).subtype))) := by
  -- Localize each short exact sequence of successive terms.
  have hstep (i : Fin s.length) :
      Module.length (Localization T) (LocalizedModule T (s i.succ)) =
        Module.length (Localization T) (LocalizedModule T (s i.castSucc)) +
          Module.length (Localization T)
            (LocalizedModule T (↥(s i.succ) ⧸ (s i.castSucc).comap (s i.succ).subtype)) := by
    let hle : s i.castSucc ≤ s i.succ := s.strictMono.monotone (Fin.castSucc_le_succ i)
    let f := Submodule.inclusion hle
    let g := ((s i.castSucc).comap (s i.succ).subtype).mkQ
    have hex : Function.Exact f g := by
      rw [LinearMap.exact_iff, Submodule.ker_mkQ, Submodule.range_inclusion]
    -- The localized maps are linear over `Localization T`. Clear a denominator
    -- to lift each localized kernel element through the original exact sequence.
    refine Module.length_eq_add_of_exact (LocalizedModule.map T f) (LocalizedModule.map T g)
      (LocalizedModule.map_injective T f (Submodule.inclusion_injective hle))
      (LocalizedModule.map_surjective T g (Submodule.mkQ_surjective _)) ?_
    intro y
    constructor
    · refine LocalizedModule.induction_on (fun m u hy => ?_) y
      rw [LocalizedModule.map_mk, ← LocalizedModule.zero_mk (1 : T),
        LocalizedModule.mk_eq, one_smul, smul_zero] at hy
      obtain ⟨a, haT, ha⟩ := Subtype.exists.1 hy
      rw [smul_zero, Submonoid.mk_smul, ← map_smul, hex (a • m)] at ha
      obtain ⟨x, hx⟩ := ha
      use LocalizedModule.mk x (⟨a, haT⟩ * u)
      rw [LocalizedModule.map_mk, hx,
        ← LocalizedModule.mk_cancel_common_left ⟨a, haT⟩ u m, Submonoid.mk_smul]
    · rintro ⟨x, hx⟩
      revert hx
      refine LocalizedModule.induction_on (fun m u hx => ?_) x
      rw [← hx, LocalizedModule.map_mk, LocalizedModule.map_mk,
        (hex (f m)).2 ⟨m, rfl⟩, LocalizedModule.zero_mk]
  -- Add the recurrences without subtracting or cancelling infinite lengths.
  have hsum : ∀ (n : ℕ) (l : Fin (n + 1) → ℕ∞) (q : Fin n → ℕ∞),
      (∀ i, l i.succ = l i.castSucc + q i) →
        l (Fin.last n) = l 0 + ∑ i, q i := by
    intro n
    induction n with
    | zero => intro l q h; simp
    | succ n ih =>
      intro l q h
      rw [← Fin.succ_last, h (Fin.last n), Fin.sum_univ_castSucc]
      have hprefix := ih (fun i => l i.castSucc) (fun i => q i.castSucc)
        (fun i => by simpa only [Fin.succ_castSucc] using h i.castSucc)
      rw [hprefix, Fin.castSucc_zero, add_assoc]
  have hzero : Module.length (Localization T) (LocalizedModule T (s 0)) = 0 := by
    change Module.length (Localization T) (LocalizedModule T s.head) = 0
    rw [hhead]
    exact Module.length_eq_zero
  have htop : Module.length (Localization T) (LocalizedModule T (s (Fin.last s.length))) =
      Module.length (Localization T) (LocalizedModule T M) := by
    change Module.length (Localization T) (LocalizedModule T s.last) = _
    rw [hlast]
    exact (IsLocalizedModule.mapEquiv T (LocalizedModule.mkLinearMap T (⊤ : Submodule B M))
      (LocalizedModule.mkLinearMap T M) (Localization T) (Submodule.topEquiv)).length_eq
  have h := hsum s.length
    (fun i => Module.length (Localization T) (LocalizedModule T (s i)))
    (fun i => Module.length (Localization T)
      (LocalizedModule T (↥(s i.succ) ⧸ (s i.castSucc).comap (s i.succ).subtype))) hstep
  simpa only [htop, hzero, zero_add] using h
/-- The uniformizer exponent of a nonzero scalar is both its quotient length and its place order. -/
theorem p06_9e0f5043ff_dlen_scalar_quotient
    (K E : Type*) [Field K] [Field E] [Algebra K E]
    (v : AlgebraicCurve.Place K E) (a : v.toValuationSubring) (ha : a ≠ 0) :
    ∃ n : ℕ,
      Module.length v.toValuationSubring
        (v.toValuationSubring ⧸ Ideal.span ({a} : Set v.toValuationSubring)) = (n : ℕ∞) ∧
      v.ord (algebraMap v.toValuationSubring E a) = (n : ℤ) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ
  refine ⟨n, ?_, ?_⟩
  · rw [Ideal.span_singleton_mul_left_unit u.isUnit, ← Ideal.span_singleton_pow,
      ← hπ.maximalIdeal_eq]
    exact IsDiscreteValuationRing.length_quotient_pow_maximalIdeal v.toValuationSubring n
  · change v.ord (((u : v.toValuationSubring) : E) * (π : E) ^ n) = (n : ℤ)
    simpa only [zpow_natCast] using v.ord_unit_smul_zpow u hπ (n : ℤ)
/-- The cokernel of a diagonal matrix is the product of its coordinate principal quotients. -/
theorem p06_9e0f5043ff_dmc_diagonal_quotient
    (R : Type*) [CommRing R] (m : ℕ) (d : Fin m → R) :
    Nonempty (((Fin m → R) ⧸ LinearMap.range (Matrix.mulVecLin (Matrix.diagonal d)))
      ≃ₗ[R] ((i : Fin m) → R ⧸ Ideal.span ({d i} : Set R))) := by
  classical
  -- Reduce each coordinate modulo the corresponding principal ideal.
  let C : (Fin m → R) →ₗ[R] ((i : Fin m) → R ⧸ Ideal.span ({d i} : Set R)) :=
    LinearMap.pi fun i => (Ideal.span ({d i} : Set R)).mkQ.comp (LinearMap.proj i)
  have hker : LinearMap.ker C = LinearMap.range (Matrix.mulVecLin (Matrix.diagonal d)) := by
    ext y
    simp only [LinearMap.mem_ker, LinearMap.mem_range]
    constructor
    · intro hy
      have hyi : ∀ i, d i ∣ y i := by
        intro i
        apply Ideal.mem_span_singleton.mp
        apply (Submodule.Quotient.mk_eq_zero _).mp
        exact congrFun hy i
      choose z hz using hyi
      exact ⟨z, funext fun i => (Matrix.mulVec_diagonal d z i).trans (hz i).symm⟩
    · rintro ⟨z, rfl⟩
      funext i
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      exact Ideal.mem_span_singleton.mpr ⟨z i, Matrix.mulVec_diagonal d z i⟩
  have hsurj : Function.Surjective C := by
    intro w
    choose y hy using fun i => (Ideal.span ({d i} : Set R)).mkQ_surjective (w i)
    exact ⟨y, funext hy⟩
  -- The first isomorphism theorem supplies the induced bijection and its linear inverse.
  exact ⟨(Submodule.quotEquivOfEq _ _ hker.symm).trans (C.quotKerEquivOfSurjective hsurj)⟩
theorem p06_9e0f5043ff_fpm_rd_residue_surjective
    (K F : Type*) [Field K] [Field F] [Algebra K F] (x : F)
    (hx : Transcendental K x) (q : Polynomial K) (hq : Irreducible q)
    (v : AlgebraicCurve.Place K F)
    (hrep : ∀ h : v.toValuationSubring, ∃ a b : Polynomial K,
      ¬ q ∣ b ∧ (h : F) = Polynomial.aeval x a / Polynomial.aeval x b)
    (e : Polynomial K →ₐ[K] v.toValuationSubring)
    (he : ∀ a : Polynomial K, (e a : F) = Polynomial.aeval x a)
    (heq : IsLocalRing.residue v.toValuationSubring (e q) = 0) :
    Function.Surjective ((IsLocalRing.residue v.toValuationSubring).comp e.toRingHom) := by
  let ρ := IsLocalRing.residue v.toValuationSubring
  let φ := ρ.comp e.toRingHom
  intro r
  obtain ⟨h, rfl⟩ := IsLocalRing.residue_surjective (R := v.toValuationSubring) r
  obtain ⟨a, b, hb, hab⟩ := hrep h
  have hb0 : b ≠ 0 := fun hb0 => hb (hb0 ▸ dvd_zero q)
  have heb0 : Polynomial.aeval x b ≠ 0 := by
    intro heb0
    apply hb0
    exact (transcendental_iff_injective.mp hx) (by simpa using heb0)
  obtain ⟨u, t, hut⟩ := hq.coprime_iff_not_dvd.mpr hb
  have htb : φ t * φ b = 1 := by
    have hφq : φ q = 0 := heq
    simpa only [map_add, map_mul, map_one, hφq, mul_zero, zero_add]
      using congrArg φ hut
  have hmul : h * e b = e a := by
    apply Subtype.ext
    change (h : F) * (e b : F) = (e a : F)
    rw [he, he, hab, div_mul_cancel₀ _ heb0]
  have hres : ρ h * φ b = φ a := by
    change ρ h * ρ (e b) = ρ (e a)
    simpa only [map_mul] using congrArg ρ hmul
  refine ⟨a * t, ?_⟩
  change φ (a * t) = ρ h
  calc
    φ (a * t) = φ a * φ t := map_mul φ a t
    _ = (ρ h * φ b) * φ t := by rw [hres]
    _ = ρ h := by rw [mul_assoc, mul_comm (φ b) (φ t), htb, mul_one]

end Submission


namespace Submission

theorem p06_9e0f5043ff_fpm_residue_degree
    (K F : Type*) [Field K] [Field F] [Algebra K F] (x : F)
    (hx : Transcendental K x) (q : Polynomial K) (_hq : q.Monic)
    (hqi : Irreducible q) (v : AlgebraicCurve.Place K F)
    (hv : ∀ f : F, f ∈ v.toValuationSubring ↔
      ∃ a b : Polynomial K, ¬ q ∣ b ∧
        f = Polynomial.aeval x a / Polynomial.aeval x b) :
    v.deg = q.natDegree := by
  obtain ⟨e, he, hker⟩ :=
    Submission.p06_9e0f5043ff_fpm_rd_eval_kernel K F x hx q hqi v hv
  have hqzero : IsLocalRing.residue v.toValuationSubring (e q) = 0 := by
    change q ∈ RingHom.ker ((IsLocalRing.residue v.toValuationSubring).comp e.toRingHom)
    rw [hker]
    exact Ideal.subset_span (Set.mem_singleton q)
  have hsurj := Submission.p06_9e0f5043ff_fpm_rd_residue_surjective
    K F x hx q hqi v (fun h => (hv (h : F)).mp h.property) e he hqzero
  let φ : Polynomial K →ₐ[K] v.ResidueField :=
    (IsScalarTower.toAlgHom K v.toValuationSubring v.ResidueField).comp e
  have hkerφ : RingHom.ker φ = Ideal.span ({q} : Set (Polynomial K)) := hker
  have hsurjφ : Function.Surjective φ := hsurj
  have hdim :=
    ((Ideal.quotientEquivAlgOfEq K hkerφ.symm).trans
      (Ideal.quotientKerAlgEquivOfSurjective (f := φ) hsurjφ)).toLinearEquiv.finrank_eq
  exact hdim.symm.trans finrank_quotient_span_eq_natDegree

end Submission

namespace Submission

set_option warningAsError true

/-- In the given polynomial-fraction model of a place, a fraction is a unit exactly when
its numerator is not divisible by the defining irreducible polynomial. -/
theorem p06_9e0f5043ff_fno_fraction_isunit
    (K F : Type*) [Field K] [Field F] [Algebra K F] (x : F)
    (hx : Transcendental K x) (q : Polynomial K) (_hqmonic : q.Monic)
    (hq : Irreducible q) (v : AlgebraicCurve.Place K F)
    (hmem : ∀ f : F, f ∈ v.toValuationSubring ↔
      ∃ a b : Polynomial K, ¬ q ∣ b ∧
        f = Polynomial.aeval x a / Polynomial.aeval x b)
    (a b : Polynomial K) (z : v.toValuationSubring) (hb : ¬ q ∣ b)
    (hz : (z : F) = Polynomial.aeval x a / Polynomial.aeval x b) :
    IsUnit z ↔ ¬ q ∣ a := by
  -- Transcendence lets us recover polynomial identities from identities in F.
  have hinj : Function.Injective (Polynomial.aeval x : Polynomial K →ₐ[K] F) :=
    transcendental_iff_injective.mp hx
  have hnonzero : ∀ p : Polynomial K, ¬ q ∣ p → Polynomial.aeval x p ≠ 0 := by
    intro p hp he
    have hpzero : p = 0 := hinj (by simpa only [map_zero] using he)
    exact hp (hpzero ▸ dvd_zero q)
  have hbzero := hnonzero b hb
  constructor
  · intro hu hqa
    -- Represent a unit's inverse, clear denominators, and use primality of q.
    obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.mp hu
    obtain ⟨c, d, hd, hwd⟩ := (hmem (w : F)).mp w.property
    have hprod : Polynomial.aeval x a * Polynomial.aeval x c =
        Polynomial.aeval x b * Polynomial.aeval x d := by
      have heq : (z : F) * (w : F) = 1 :=
        congrArg (fun t : v.toValuationSubring => (t : F)) hw
      rw [hz, hwd, div_mul_div_comm] at heq
      exact (div_eq_one_iff_eq (mul_ne_zero hbzero (hnonzero d hd))).mp heq
    have hpoly : a * c = b * d := hinj (by simpa only [map_mul] using hprod)
    have hdiv : q ∣ b * d := hpoly ▸ dvd_mul_of_dvd_left hqa c
    exact (hq.prime.dvd_or_dvd hdiv).elim hb hd
  · intro ha
    -- The reversed fraction belongs to the valuation subring and is an inverse.
    have hwmem : Polynomial.aeval x b / Polynomial.aeval x a ∈ v.toValuationSubring :=
      (hmem _).mpr ⟨b, a, ha, rfl⟩
    apply isUnit_iff_exists_inv.mpr
    refine ⟨⟨_, hwmem⟩, ?_⟩
    apply Subtype.ext
    change (z : F) * (Polynomial.aeval x b / Polynomial.aeval x a) = 1
    rw [hz, div_mul_div_comm, mul_comm (Polynomial.aeval x b) (Polynomial.aeval x a)]
    exact div_self (mul_ne_zero (hnonzero a ha) hbzero)

end Submission


namespace Submission

set_option warningAsError true

theorem p06_9e0f5043ff_fno_irreducible_aeval
    (K F : Type*) [Field K] [Field F] [Algebra K F] (x : F)
    (hx : Transcendental K x) (q : Polynomial K) (hq : q.Monic)
    (hqi : Irreducible q) (v : AlgebraicCurve.Place K F)
    (hv : ∀ f : F, f ∈ v.toValuationSubring ↔
      ∃ a b : Polynomial K, ¬ q ∣ b ∧
        f = Polynomial.aeval x a / Polynomial.aeval x b) :
    ∃ π : v.toValuationSubring, (π : F) = Polynomial.aeval x q ∧ Irreducible π := by
  classical
  have hinj : Function.Injective (Polynomial.aeval x : Polynomial K →ₐ[K] F) :=
    transcendental_iff_injective.mp hx
  have hq1 : ¬ q ∣ (1 : Polynomial K) := hqi.not_dvd_one
  let π : v.toValuationSubring :=
    ⟨Polynomial.aeval x q, (hv _).mpr ⟨q, 1, hq1, by simp⟩⟩
  refine ⟨π, rfl, ?_⟩
  constructor
  · intro hunit
    have hnot :=
      (Submission.p06_9e0f5043ff_fno_fraction_isunit K F x hx q hq hqi v hv
        q 1 π hq1 (by simp [π])).mp hunit
    exact hnot (dvd_refl q)
  · intro y z hyz
    obtain ⟨a, b, hb, hy⟩ := (hv (y : F)).mp y.property
    obtain ⟨c, t, ht, hz⟩ := (hv (z : F)).mp z.property
    have hb0 : Polynomial.aeval x b ≠ 0 := by
      intro h
      have : b = 0 := hinj (by simpa only [map_zero] using h)
      exact hb (this.symm ▸ dvd_zero q)
    have ht0 : Polynomial.aeval x t ≠ 0 := by
      intro h
      have : t = 0 := hinj (by simpa only [map_zero] using h)
      exact ht (this.symm ▸ dvd_zero q)
    have hprod : Polynomial.aeval x q =
        (Polynomial.aeval x a / Polynomial.aeval x b) *
          (Polynomial.aeval x c / Polynomial.aeval x t) := by
      calc
        Polynomial.aeval x q = (π : F) := rfl
        _ = (y : F) * (z : F) :=
          congrArg (fun w : v.toValuationSubring => (w : F)) hyz
        _ = _ := by rw [hy, hz]
    have hac : a * c = q * (b * t) := by
      apply hinj
      rw [div_mul_div_comm, eq_div_iff (mul_ne_zero hb0 ht0)] at hprod
      simpa only [map_mul] using hprod.symm
    by_cases ha : q ∣ a
    · right
      apply (Submission.p06_9e0f5043ff_fno_fraction_isunit K F x hx q hq hqi v hv
        c t z ht hz).mpr
      intro hc
      obtain ⟨a₁, ha₁⟩ := ha
      obtain ⟨c₁, hc₁⟩ := hc
      have hcancel : q * (q * (a₁ * c₁)) = q * (b * t) := by
        calc
          q * (q * (a₁ * c₁)) = (q * a₁) * (q * c₁) := by ring
          _ = a * c := by rw [← ha₁, ← hc₁]
          _ = q * (b * t) := hac
      have hbt : q ∣ b * t :=
        ⟨a₁ * c₁, (mul_left_cancel₀ hqi.ne_zero hcancel).symm⟩
      exact (hqi.prime.dvd_or_dvd hbt).elim hb ht
    · left
      exact (Submission.p06_9e0f5043ff_fno_fraction_isunit K F x hx q hq hqi v hv
        a b y hb hy).mpr ha

end Submission

/-- The reciprocal of the fraction-ring variable is transcendental and presents every fraction. -/
theorem Submission.p06_9e0f5043ff_inf_reciprocal_presentation :
    ∀ (K : Type*) [Field K],
      Transcendental K
        ((algebraMap (Polynomial K) (FractionRing (Polynomial K)) Polynomial.X)⁻¹) ∧
      (∀ f : FractionRing (Polynomial K), ∃ a b : Polynomial K, b ≠ 0 ∧
        f = Polynomial.aeval
          ((algebraMap (Polynomial K) (FractionRing (Polynomial K)) Polynomial.X)⁻¹) a /
          Polynomial.aeval
          ((algebraMap (Polynomial K) (FractionRing (Polynomial K)) Polynomial.X)⁻¹) b) := by
  intro K _
  let t : FractionRing (Polynomial K) :=
    algebraMap (Polynomial K) (FractionRing (Polynomial K)) Polynomial.X
  have hinj := IsFractionRing.injective (Polynomial K) (FractionRing (Polynomial K))
  have ht : t ≠ 0 := by
    exact fun h => Polynomial.X_ne_zero (hinj (h.trans (map_zero _).symm))
  have heval (p : Polynomial K) :
      Polynomial.aeval t p = algebraMap (Polynomial K) (FractionRing (Polynomial K)) p := by
    simp [t, Polynomial.aeval_algebraMap_apply]
  have htrans : Transcendental K t :=
    (transcendental_algebraMap_iff hinj).mpr (Polynomial.transcendental_X K)
  have hs : Transcendental K t⁻¹ := by
    intro h
    exact htrans (IsAlgebraic.inv_iff.mp h)
  refine ⟨hs, ?_⟩
  intro f
  change ∃ a b : Polynomial K, b ≠ 0 ∧
    f = Polynomial.aeval t⁻¹ a / Polynomial.aeval t⁻¹ b
  by_cases hf : f = 0
  · exact ⟨0, 1, one_ne_zero, by simp [hf]⟩
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (Polynomial K) f
  have hb0 : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
  have hbr : b.reverse ≠ 0 := by simpa using hb0
  have hbev : Polynomial.aeval t⁻¹ b.reverse ≠ 0 := by
    exact fun h => hbr ((transcendental_iff_injective.mp hs) (by simpa using h))
  let : Invertible t := invertibleOfNonzero ht
  have hreverse (p : Polynomial K) :
      algebraMap (Polynomial K) (FractionRing (Polynomial K)) p =
        Polynomial.aeval t⁻¹ p.reverse / (t⁻¹) ^ p.natDegree := by
    have h := Polynomial.eval₂_reverse_mul_pow
      (algebraMap K (FractionRing (Polynomial K))) t p
    simpa only [invOf_eq_inv, ← Polynomial.aeval_def, heval, inv_pow,
      div_inv_eq_mul] using h.symm
  rw [← hab, hreverse a, hreverse b]
  by_cases hdeg : a.natDegree ≤ b.natDegree
  · refine ⟨Polynomial.X ^ (b.natDegree - a.natDegree) * a.reverse,
      b.reverse, hbr, ?_⟩
    rw [map_mul, map_pow, Polynomial.aeval_X, pow_sub₀ _ (inv_ne_zero ht) hdeg]
    field_simp
  · refine ⟨a.reverse, Polynomial.X ^ (a.natDegree - b.natDegree) * b.reverse,
      mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) hbr, ?_⟩
    rw [map_mul, map_pow, Polynomial.aeval_X,
      pow_sub₀ _ (inv_ne_zero ht) (Nat.le_of_lt (Nat.lt_of_not_ge hdeg))]
    field_simp
/-- Reciprocal evaluation has order minus the degree at the place above the origin. -/
theorem Submission.p06_9e0f5043ff_inf_reciprocal_polynomial_order :
    ∀ (K F : Type*) [Field K] [Field F] [Algebra K F] (s : F),
      Transcendental K s → ∀ v : AlgebraicCurve.Place K F, v.ord s = 1 →
      (∀ c : Polynomial K, ¬ (Polynomial.X : Polynomial K) ∣ c →
        v.ord (Polynomial.aeval s c) = 0) →
      ∀ a : Polynomial K, a ≠ 0 →
        v.ord (Polynomial.aeval s⁻¹ a) = -(a.natDegree : ℤ) := by
  intro K F _ _ _ s hs v hv hzero a ha
  have hs0 : s ≠ 0 := by
    intro h
    exact hs ⟨Polynomial.X, Polynomial.X_ne_zero, by simpa using h⟩
  have hrev : a.reverse ≠ 0 := fun h => ha (Polynomial.reverse_eq_zero.mp h)
  have heval : Polynomial.aeval s a.reverse ≠ 0 := fun h => hs ⟨a.reverse, hrev, h⟩
  have hnot : ¬ (Polynomial.X : Polynomial K) ∣ a.reverse := by
    simpa only [Polynomial.X_dvd_iff, Polynomial.coeff_zero_reverse,
      Polynomial.leadingCoeff_eq_zero] using ha
  have horder : v.ord (Polynomial.aeval s a.reverse) = 0 := hzero _ hnot
  -- Reversal writes reciprocal evaluation as a negative power times a unit at v.
  have hidentity : Polynomial.aeval s⁻¹ a =
      s ^ (-(a.natDegree : ℤ)) * Polynomial.aeval s a.reverse := by
    let : Invertible s⁻¹ := invertibleOfNonzero (inv_ne_zero hs0)
    simpa only [invOf_eq_inv, inv_inv, ← Polynomial.aeval_def, zpow_neg,
      zpow_natCast, inv_pow, mul_comm] using
      (Polynomial.eval₂_reverse_mul_pow (algebraMap K F) s⁻¹ a).symm
  rw [hidentity, v.ord_mul (zpow_ne_zero _ hs0) heval, v.ord_zpow, hv,
    horder, mul_one, add_zero]

namespace Submission

namespace Submission

/-- Fractions with denominators not divisible by an irreducible polynomial form a subalgebra. -/
theorem p06_9e0f5043ff_elp_fraction_subalgebra
    (K F : Type*) [Field K] [Field F] [Algebra K F] (x : F)
    (hx : Transcendental K x) (q : Polynomial K) (_hq : q.Monic)
    (hq : Irreducible q) :
    ∃ A : Subalgebra K F, ∀ f : F, f ∈ A ↔
      ∃ a b : Polynomial K, ¬ q ∣ b ∧
        f = Polynomial.aeval x a / Polynomial.aeval x b := by
  -- Irreducibility in K[T] gives the denominator product property from the accepted proof.
  have hprime : Prime q := hq.prime
  -- A permitted denominator cannot evaluate to zero at a transcendental element.
  have hden : ∀ b : Polynomial K, ¬ q ∣ b → Polynomial.aeval x b ≠ 0 := by
    intro b hb heval
    have hb0 : b = 0 := transcendental_iff.mp hx b heval
    exact hb (hb0 ▸ dvd_zero q)
  -- Subalgebra obtains negation closure by multiplying by the included constant -1.
  have hprime : Prime q := hq.prime
  -- A permitted denominator cannot evaluate to zero at a transcendental element.
  have hden : ∀ b : Polynomial K, ¬ q ∣ b → Polynomial.aeval x b ≠ 0 := by
    intro b hb heval
    exact hb (transcendental_iff.mp hx b heval ▸ dvd_zero q)
  refine ⟨{
    carrier := {f | ∃ a b : Polynomial K, ¬ q ∣ b ∧
      f = Polynomial.aeval x a / Polynomial.aeval x b}
    algebraMap_mem' := by
      -- Constants use denominator one; Subalgebra derives zero and one membership.
      intro c
      exact ⟨Polynomial.C c, 1, hprime.not_dvd_one, by
        simp only [Polynomial.aeval_C, map_one, div_one]⟩
      intro c
      exact ⟨Polynomial.C c, 1, hprime.not_dvd_one, by simp⟩
    add_mem' := by
      rintro _ _ ⟨a, b, hb, rfl⟩ ⟨c, d, hd, rfl⟩
      refine ⟨a * d + b * c, b * d, hprime.not_dvd_mul hb hd, ?_⟩
      simpa only [map_add, map_mul] using
        div_add_div (Polynomial.aeval x a) (Polynomial.aeval x c) (hden b hb) (hden d hd)
    mul_mem' := by
      rintro _ _ ⟨a, b, hb, rfl⟩ ⟨c, d, hd, rfl⟩
      refine ⟨a * c, b * d, hprime.not_dvd_mul hb hd, ?_⟩
      simp only [map_mul, div_mul_div_comm]
  }, fun _ => Iff.rfl⟩
/-- The exponent of an irreducible polynomial, realized by the pinned library's `multiplicity`.
The monicity hypothesis is retained from the frozen contract; irreducibility suffices for the proof. -/
/-- The exponent of an irreducible polynomial, realized by the pinned library's `multiplicity`. -/
/-- The exponent of an irreducible polynomial, realized by the pinned library's `multiplicity`.
The monicity hypothesis is retained from the frozen contract; irreducibility suffices for the proof. -/
theorem p06_9e0f5043ff_io_polynomial_exponent :
    ∀ (K : Type*) [Field K] (q : Polynomial K), q.Monic → Irreducible q →
      ∃ μ : Polynomial K → ℕ, μ 1 = 0 ∧ μ q = 1 ∧
        (∀ a b : Polynomial K, a ≠ 0 → b ≠ 0 → μ (a * b) = μ a + μ b) ∧
        (∀ a : Polynomial K, a ≠ 0 → (μ a = 0 ↔ ¬ q ∣ a)) ∧
        (∀ a : Polynomial K, a ≠ 0 → ∃ a₀ : Polynomial K,
          a₀ ≠ 0 ∧ ¬ q ∣ a₀ ∧ a = q ^ μ a * a₀) := by
  intro K _ q _ hq
  -- The library's degree-based well-founded divisibility supplies finite power extraction.
  have hfin (a : Polynomial K) (ha : a ≠ 0) : FiniteMultiplicity q a :=
    FiniteMultiplicity.of_not_isUnit hq.not_isUnit ha
  -- The frozen contract leaves μ 0 unconstrained, so the library's default value is admissible.
  -- Polynomial well-founded divisibility supplies the finite power extraction.
  have hfin (a : Polynomial K) (ha : a ≠ 0) : FiniteMultiplicity q a :=
    FiniteMultiplicity.of_not_isUnit hq.not_isUnit ha
  -- The frozen contract leaves μ 0 unconstrained, so the library's default value is admissible.
  refine ⟨multiplicity q, multiplicity_of_one_right hq.not_isUnit,
    multiplicity_self, ?_, ?_, ?_⟩
  · intro a b ha hb
    exact multiplicity_mul hq.prime (hfin (a * b) (mul_ne_zero ha hb))
  · intro a _
    exact multiplicity_eq_zero
  · intro a ha
    obtain ⟨a₀, hfactor, hfree⟩ := (hfin a ha).exists_eq_pow_mul_and_not_dvd
    exact ⟨a₀, right_ne_zero_of_mul (hfactor ▸ ha), hfree, hfactor⟩

end Submission

namespace Submission

/-- Extend an additive exponent on nonzero polynomials to integer orders on a field
represented by fractions of their evaluations at a transcendental element. -/
theorem p06_9e0f5043ff_io_fraction_extension :
    ∀ (K F : Type*) [Field K] [Field F] [Algebra K F] (x : F),
      Transcendental K x →
      (∀ f : F, ∃ a b : Polynomial K, b ≠ 0 ∧
        f = Polynomial.aeval x a / Polynomial.aeval x b) →
      ∀ μ : Polynomial K → ℕ,
        (∀ a b : Polynomial K, a ≠ 0 → b ≠ 0 → μ (a * b) = μ a + μ b) →
        ∃ ν : F → ℤ, ν 0 = 0 ∧
          (∀ a b : Polynomial K, a ≠ 0 → b ≠ 0 →
            ν (Polynomial.aeval x a / Polynomial.aeval x b) =
              (μ a : ℤ) - (μ b : ℤ)) ∧
          (∀ f g : F, f ≠ 0 → g ≠ 0 → ν (f / g) = ν f - ν g) := by
  intro K F _ _ _ x hx hrepr μ hμ
  classical
  let e := Polynomial.aeval (R := K) x
  have hinj : Function.Injective e := transcendental_iff_injective.mp hx
  have hne (a : Polynomial K) (ha : a ≠ 0) : e a ≠ 0 := by
    intro h
    exact ha (hinj (h.trans (map_zero e).symm))
  choose a b hb hab using hrepr
  have ha (f : F) (hf : f ≠ 0) : a f ≠ 0 := by
    intro h
    apply hf
    simpa [h] using hab f
  -- Equal nonzero fractions have the same integer difference.
  have hwell (p q r s : Polynomial K) (hp : p ≠ 0) (hq : q ≠ 0)
      (hr : r ≠ 0) (hs : s ≠ 0) (h : e p / e q = e r / e s) :
      (μ p : ℤ) - (μ q : ℤ) = (μ r : ℤ) - (μ s : ℤ) := by
    have hcross : p * s = r * q := by
      apply hinj
      simpa only [map_mul] using (div_eq_div_iff (hne q hq) (hne s hs)).mp h
    have hsum := congrArg μ hcross
    rw [hμ p s hp hs, hμ r q hr hq] at hsum
    omega
  -- The exponent at the zero polynomial is unrestricted, so define the value at zero separately.
  let ν : F → ℤ := fun f => if f = 0 then 0 else (μ (a f) : ℤ) - (μ (b f) : ℤ)
  have hformula (p q : Polynomial K) (hp : p ≠ 0) (hq : q ≠ 0) :
      ν (e p / e q) = (μ p : ℤ) - (μ q : ℤ) := by
    have hf : e p / e q ≠ 0 := div_ne_zero (hne p hp) (hne q hq)
    dsimp only [ν]
    rw [if_neg hf]
    exact hwell _ _ p q (ha _ hf) (hb _) hp hq (hab _).symm
  refine ⟨ν, ?_, hformula, ?_⟩
  · simp [ν]
  · intro f g hf hg
    have hquot : f / g = e (a f * b g) / e (b f * a g) := by
      calc
        f / g = (e (a f) / e (b f)) / (e (a g) / e (b g)) :=
          congrArg₂ (fun u v : F => u / v) (hab f) (hab g)
        _ = e (a f * b g) / e (b f * a g) := by
          simp only [map_mul, div_div_div_eq]
    rw [hquot, hformula _ _ (mul_ne_zero (ha f hf) (hb g))
      (mul_ne_zero (hb f) (ha g hg)), hμ _ _ (ha f hf) (hb g),
      hμ _ _ (hb f) (ha g hg)]
    simp only [ν, if_neg hf, if_neg hg, Nat.cast_add]
    ring

end Submission

namespace Submission

/-- Extend an additive exponent on nonzero polynomials to integer orders on a field
represented by fractions of their evaluations at a transcendental element. -/
theorem p06_9e0f5043ff_io_fraction_extension :
    ∀ (K F : Type*) [Field K] [Field F] [Algebra K F] (x : F),
      Transcendental K x →
      (∀ f : F, ∃ a b : Polynomial K, b ≠ 0 ∧
        f = Polynomial.aeval x a / Polynomial.aeval x b) →
      ∀ μ : Polynomial K → ℕ,
        (∀ a b : Polynomial K, a ≠ 0 → b ≠ 0 → μ (a * b) = μ a + μ b) →
        ∃ ν : F → ℤ, ν 0 = 0 ∧
          (∀ a b : Polynomial K, a ≠ 0 → b ≠ 0 →
            ν (Polynomial.aeval x a / Polynomial.aeval x b) =
              (μ a : ℤ) - (μ b : ℤ)) ∧
          (∀ f g : F, f ≠ 0 → g ≠ 0 → ν (f / g) = ν f - ν g) := by
  intro K F _ _ _ x hx hrepr μ hμ
  classical
  let e := Polynomial.aeval (R := K) x
  have hinj : Function.Injective e := transcendental_iff_injective.mp hx
  have hne (a : Polynomial K) (ha : a ≠ 0) : e a ≠ 0 := by
    intro h
    exact ha (hinj (h.trans (map_zero e).symm))
  choose a b hb hab using hrepr
  have ha (f : F) (hf : f ≠ 0) : a f ≠ 0 := by
    intro h
    apply hf
    simpa [h] using hab f
  -- Equal nonzero fractions have the same integer difference.
  have hwell (p q r s : Polynomial K) (hp : p ≠ 0) (hq : q ≠ 0)
      (hr : r ≠ 0) (hs : s ≠ 0) (h : e p / e q = e r / e s) :
      (μ p : ℤ) - (μ q : ℤ) = (μ r : ℤ) - (μ s : ℤ) := by
    have hcross : p * s = r * q := by
      apply hinj
      simpa only [map_mul] using (div_eq_div_iff (hne q hq) (hne s hs)).mp h
    have hsum := congrArg μ hcross
    rw [hμ p s hp hs, hμ r q hr hq] at hsum
    omega
  -- The exponent at the zero polynomial is unrestricted, so define the value at zero separately.
  let ν : F → ℤ := fun f => if f = 0 then 0 else (μ (a f) : ℤ) - (μ (b f) : ℤ)
  have hformula (p q : Polynomial K) (hp : p ≠ 0) (hq : q ≠ 0) :
      ν (e p / e q) = (μ p : ℤ) - (μ q : ℤ) := by
    have hf : e p / e q ≠ 0 := div_ne_zero (hne p hp) (hne q hq)
    dsimp only [ν]
    rw [if_neg hf]
    exact hwell _ _ p q (ha _ hf) (hb _) hp hq (hab _).symm
  refine ⟨ν, ?_, hformula, ?_⟩
  · simp [ν]
  · intro f g hf hg
    have hquot : f / g = e (a f * b g) / e (b f * a g) := by
      calc
        f / g = (e (a f) / e (b f)) / (e (a g) / e (b g)) :=
          congrArg₂ (fun u v : F => u / v) (hab f) (hab g)
        _ = e (a f * b g) / e (b f * a g) := by
          simp only [map_mul, div_div_div_eq]
    rw [hquot, hformula _ _ (mul_ne_zero (ha f hf) (hb g))
      (mul_ne_zero (hb f) (ha g hg)), hμ _ _ (ha f hf) (hb g),
      hμ _ _ (hb f) (ha g hg)]
    simp only [ν, if_neg hf, if_neg hg, Nat.cast_add]
    ring
    refine ⟨a₀, ?_, hfree, hfactor⟩
    intro hzero
    apply ha
    simpa [hzero] using hfactor

end Submission

namespace Submission

/-- Monic equations for a nonzero element and its inverse over the restricted valuation ring
make the element a unit upstairs, so its order is zero.

Map each polynomial to `L`, use `Place.mem_restrict_iff` to transfer its coefficient
memberships, and apply `Place.mem_of_eval_monic_eq_zero`. The resulting unit has order
zero by `Place.ord_coe_unit`. -/
theorem p06_9e0f5043ff_fosa_ord_zero_of_monic_pair
    (K E L : Type*) [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra K L] [Algebra E L] [IsScalarTower K E L]
    [Algebra.IsIntegral E L] (w : AlgebraicCurve.Place K L) (f : L)
    (P Q : Polynomial E) (hf : f ≠ 0) (hP : P.Monic) (hQ : Q.Monic)
    (hPf : Polynomial.eval₂ (algebraMap E L) f P = 0)
    (hQf : Polynomial.eval₂ (algebraMap E L) (f⁻¹) Q = 0)
    (hPcoeff : ∀ i : ℕ, P.coeff i ∈ (w.restrict E).toValuationSubring)
    (hQcoeff : ∀ i : ℕ, Q.coeff i ∈ (w.restrict E).toValuationSubring) :
    w.ord f = 0 := by
  have mem_of_root (R : Polynomial E) (x : L) (hR : R.Monic)
      (hcoeff : ∀ i : ℕ, R.coeff i ∈ (w.restrict E).toValuationSubring)
      (hx : Polynomial.eval₂ (algebraMap E L) x R = 0) :
      x ∈ w.toValuationSubring := by
    apply w.mem_of_eval_monic_eq_zero (P := R.map (algebraMap E L)) (hR.map _)
    · intro i
      simpa only [Polynomial.coeff_map] using w.mem_restrict_iff.mp (hcoeff i)
    · simpa only [Polynomial.eval_map] using hx
  exact w.ord_coe_unit
    { val := ⟨f, mem_of_root P f hP hPcoeff hPf⟩
      inv := ⟨f⁻¹, mem_of_root Q f⁻¹ hQ hQcoeff hQf⟩
      val_inv := Subtype.ext (mul_inv_cancel₀ hf)
      inv_val := Subtype.ext (inv_mul_cancel₀ hf) }

end Submission

namespace Submission

open AlgebraicCurve IsDedekindDomain

/-- The localized principal quotient and its corresponding place have the same
nonnegative order, witnessed by the exponent of a uniformizer. -/
theorem p06_9e0f5043ff_ifl_local_length_order
    (K E L : Type*) [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra K L] [Algebra E L] [IsScalarTower K E L]
    [FiniteDimensional E L] [Algebra.IsSeparable E L]
    (v : Place K E) (q : HeightOneSpectrum (Place.integralClosureAt L v))
    (R : Type*) [CommRing R] [IsDomain R]
    [Algebra (Place.integralClosureAt L v) R] [IsLocalization.AtPrime R q.asIdeal]
    (b : Place.integralClosureAt L v) (hb : b ≠ 0) :
    ∃ m : ℕ,
      Module.length R (R ⧸ Ideal.span
        ({algebraMap (Place.integralClosureAt L v) R b} : Set R)) = (m : ℕ∞) ∧
      (Place.placeOfPrime q).ord
        (algebraMap (Place.integralClosureAt L v) L b) = (m : ℤ) := by
  let B := Place.integralClosureAt L v
  let w := Place.placeOfPrime q
  let O := HeightOneSpectrum.valuationSubringAtPrime L q
  let : IsDiscreteValuationRing R :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain B q.ne_bot R
  let e : R ≃ₐ[B] O := IsLocalization.algEquiv q.asIdeal.primeCompl R O
  have hbR : algebraMap B R b ≠ 0 :=
    (map_ne_zero_iff (algebraMap B R)
      (IsLocalization.injective R q.asIdeal.primeCompl_le_nonZeroDivisors)).mpr hb
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨m, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hbR hπ
  refine ⟨m, ?_, ?_⟩
  -- The pinned Mathlib/RingTheory/DiscreteValuationRing/Basic.lean theorem
  -- combines Module.length_quotient with coheight_pow_maximalIdeal to compute
  -- the coheight of the uniformizer-power ideal, including when m = 0.
  · rw [hu, Ideal.span_singleton_mul_left_unit u.isUnit,
      ← Ideal.span_singleton_pow, ← hπ.maximalIdeal_eq]
    exact IsDiscreteValuationRing.length_quotient_pow_maximalIdeal R m
  · let u' : w.toValuationSubringˣ := Units.map e.toMonoidHom u
    have hπ' : Irreducible (e π : w.toValuationSubring) := hπ.map e.toMulEquiv
    -- The localization equivalence preserves the image of the original element.
    have he : ((e (algebraMap B R b) : O) : L) = algebraMap B L b := by
      change algebraMap O L (e (algebraMap B R b)) = _
      rw [e.commutes, ← IsScalarTower.algebraMap_apply B O L]
    have hcoe : algebraMap B L b =
        ((u' : w.toValuationSubring) : L) * ((e π : O) : L) ^ (m : ℤ) := by
      have h := congrArg (fun x : R => ((e x : O) : L)) hu
      rw [he] at h
      simpa [u', zpow_natCast] using h
    rw [hcoe]
    exact w.ord_unit_smul_zpow u' hπ' (m : ℤ)

end Submission

namespace Submission

/-- Finite order supports give a finite exceptional set for all coefficients of a polynomial.
Take the union of the order supports of its nonzero coefficients. Outside that union,
unit–uniformizer factorization makes each nonzero coefficient a valuation-subring unit. -/
theorem p06_9e0f5043ff_fosa_coefficients_integral_off_finite
    (K E : Type*) [Field K] [Field E] [Algebra K E]
    (hfinite : ∀ a : E, a ≠ 0 → {v : AlgebraicCurve.Place K E | v.ord a ≠ 0}.Finite)
    (P : Polynomial E) :
    ∃ T : Set (AlgebraicCurve.Place K E), T.Finite ∧
      ∀ v : AlgebraicCurve.Place K E, v ∉ T → ∀ i : ℕ,
        P.coeff i ∈ v.toValuationSubring := by
  classical
  refine ⟨⋃ i ∈ P.support, {v | v.ord (P.coeff i) ≠ 0}, ?_, ?_⟩
  · exact P.support.finite_toSet.biUnion fun i hi =>
      hfinite (P.coeff i) (Polynomial.mem_support_iff.mp hi)
  · intro v hv i
    by_cases hi : P.coeff i = 0
    · rw [hi]
      exact v.toValuationSubring.zero_mem
    · have hord : v.ord (P.coeff i) = 0 := by
        by_contra h
        exact hv (Set.mem_biUnion (Polynomial.mem_support_iff.mpr hi) h)
      obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
      obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hi hπ
      rw [hu, hord, zpow_zero, mul_one]
      exact (u : v.toValuationSubring).property

end Submission

namespace Submission

/-- Finite order support ascends along a finite separable field extension.
Choose monic equations for the element and its inverse. The approved coefficient lemma
gives two finite exceptional sets downstairs; the approved monic-pair lemma makes the
order zero outside their inverse image. Restriction has finite fibers by the pinned
`AlgebraicCurve.Place.finite_setOf_restrict_eq`, so that inverse image is finite. -/
theorem p06_9e0f5043ff_finite_order_support_ascent
    (K E L : Type*) [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra K L] [Algebra E L] [IsScalarTower K E L]
    [FiniteDimensional E L] [Algebra.IsSeparable E L]
    (hE : ∀ a : E, a ≠ 0 → {v : AlgebraicCurve.Place K E | v.ord a ≠ 0}.Finite)
    (f : L) (hf : f ≠ 0) :
    {w : AlgebraicCurve.Place K L | w.ord f ≠ 0}.Finite := by
  classical
  obtain ⟨P, hP, hPf⟩ := IsIntegral.of_finite E f
  obtain ⟨Q, hQ, hQf⟩ := IsIntegral.of_finite E (f⁻¹)
  obtain ⟨TP, hTP, hPcoeff⟩ :=
    p06_9e0f5043ff_fosa_coefficients_integral_off_finite K E hE P
  obtain ⟨TQ, hTQ, hQcoeff⟩ :=
    p06_9e0f5043ff_fosa_coefficients_integral_off_finite K E hE Q
  have hfinite :
      ((fun w : AlgebraicCurve.Place K L => w.restrict E) ⁻¹' (TP ∪ TQ)).Finite :=
    (hTP.union hTQ).preimage' fun v _ =>
      AlgebraicCurve.Place.finite_setOf_restrict_eq (F' := L) v
  refine hfinite.subset ?_
  intro w hw
  change w.restrict E ∈ TP ∪ TQ
  by_contra hout
  apply hw
  exact p06_9e0f5043ff_fosa_ord_zero_of_monic_pair K E L w f P Q
    hf hP hQ hPf hQf
    (hPcoeff (w.restrict E) (fun hv => hout (Or.inl hv)))
    (hQcoeff (w.restrict E) (fun hv => hout (Or.inr hv)))

end Submission

/-- Polynomial evaluation at a nonunit of a place is a unit exactly away from `(X)`. -/
theorem Submission.p06_9e0f5043ff_vfc_polynomial_unit_criterion :
    ∀ (K F : Type*) [Field K] [Field F] [Algebra K F]
      (s : F) (w : AlgebraicCurve.Place K F),
      s⁻¹ ∉ w.toValuationSubring → ∀ p : Polynomial K,
        (∃ u : Units w.toValuationSubring,
          ((u : w.toValuationSubring) : F) = Polynomial.aeval s p) ↔
        ¬ (Polynomial.X : Polynomial K) ∣ p := by
  intro K F _ _ _ s w hinv p
  have hs : s ∈ w.toValuationSubring :=
    (w.toValuationSubring.mem_or_inv_mem s).resolve_right hinv
  let t : w.toValuationSubring := ⟨s, hs⟩
  have ht : ¬ IsUnit t := by
    rintro ⟨u, hu⟩
    have hmul : s * (((u⁻¹ : Units w.toValuationSubring) : w.toValuationSubring) : F) = 1 := by
      change (t : F) * _ = 1
      rw [← hu]
      exact congrArg (fun x : w.toValuationSubring => (x : F)) u.val_inv
    have hi : (((u⁻¹ : Units w.toValuationSubring) : w.toValuationSubring) : F) = s⁻¹ :=
      eq_inv_of_mul_eq_one_right hmul
    exact hinv (hi ▸ (u⁻¹).val.property)
  -- Evaluate inside the valuation subring using its inherited K-algebra structure.
  let E : Polynomial K →+* w.toValuationSubring := (Polynomial.aeval t).toRingHom
  have hE (q : Polynomial K) : (E q : F) = Polynomial.aeval s q := by
    exact (Polynomial.aeval_algHom_apply
      (IsScalarTower.toAlgHom K w.toValuationSubring F) t q).symm
  let J : Ideal (Polynomial K) := (IsLocalRing.maximalIdeal w.toValuationSubring).comap E
  have hJ : J ≠ ⊤ :=
    Ideal.comap_ne_top E (IsLocalRing.maximalIdeal.isMaximal w.toValuationSubring).ne_top
  have hX : (Polynomial.X : Polynomial K) ∈ J := by
    change E Polynomial.X ∈ IsLocalRing.maximalIdeal w.toValuationSubring
    change Polynomial.aeval t Polynomial.X ∈ IsLocalRing.maximalIdeal w.toValuationSubring
    rw [Polynomial.aeval_X, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact ht
  -- The proper contraction contains the maximal ideal (X), so they coincide.
  have hspan : Ideal.span ({Polynomial.X} : Set (Polynomial K)) = J :=
    (PrincipalIdealRing.isMaximal_of_irreducible Polynomial.irreducible_X).eq_of_le hJ
      (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hX))
  have hunit : IsUnit (E p) ↔ ¬ (Polynomial.X : Polynomial K) ∣ p := by
    rw [← IsLocalRing.notMem_maximalIdeal]
    change p ∉ J ↔ ¬ (Polynomial.X : Polynomial K) ∣ p
    rw [← hspan, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨u, hu⟩
    apply hunit.mp
    refine ⟨u, ?_⟩
    exact Subtype.ext (hu.trans (hE p).symm)
  · intro hp
    obtain ⟨u, hu⟩ := hunit.mpr hp
    exact ⟨u, (congrArg (fun x : w.toValuationSubring => (x : F)) hu).trans (hE p)⟩
/-- Membership of a unit times a parameter-power quotient forces nonnegative exponent. -/
theorem Submission.p06_9e0f5043ff_vfc_unit_power_quotient_exponents :
    ∀ (F : Type*) [Field F] (W : Subring F) (s : F), s ∈ W → s⁻¹ ∉ W →
      ∀ (u : Units W) (r k : ℕ), ((u : W) : F) * s ^ r / s ^ k ∈ W → k ≤ r := by
  intro F _ W s hs hsinv u r k hquot
  have hs0 : s ≠ 0 := by
    intro h
    apply hsinv
    simp [h]
  have hu : ((u : W) : F) * ((↑(u⁻¹) : W) : F) = 1 := by
    exact_mod_cast u.mul_inv
  by_contra hle
  let n := k - r - 1
  have hk : k = r + n + 1 := by
    dsimp [n]
    omega
  have hprod :
      (((u : W) : F) * s ^ r / s ^ k) * ((↑(u⁻¹) : W) : F) * s ^ n ∈ W :=
    W.mul_mem (W.mul_mem hquot (↑(u⁻¹) : W).property) (W.pow_mem hs n)
  have heq :
      (((u : W) : F) * s ^ r / s ^ k) * ((↑(u⁻¹) : W) : F) * s ^ n = s⁻¹ := by
    calc
      _ = (((u : W) : F) * ((↑(u⁻¹) : W) : F)) * (s ^ r * s ^ n) / s ^ k := by
        ring
      _ = s ^ (r + n) / s ^ (r + n + 1) := by
        rw [hu, one_mul, ← pow_add, hk]
      _ = s⁻¹ := by
        rw [pow_succ, div_mul_eq_div_div, div_self (pow_ne_zero _ hs0), one_div]
  exact hsinv (heq ▸ hprod)

namespace Submission

/-- Split off an entry dividing every matrix entry using invertible row and column operations.
Swap the pivot into position `(0, 0)`, then apply the approved column and row clearing lemmas.
The pivot need not be nonzero, and the trailing block may have size zero. -/
theorem p06_9e0f5043ff_dmd_split_divisible_pivot
    (R : Type*) [CommRing R] (m : ℕ)
    (D : Matrix (Fin (m + 1)) (Fin (m + 1)) R) (r c : Fin (m + 1))
    (hdiv : ∀ i j, D r c ∣ D i j) :
    ∃ (P Q : Matrix (Fin (m + 1)) (Fin (m + 1)) R)
      (C : Matrix (Fin m) (Fin m) R),
      IsUnit P ∧ IsUnit Q ∧
        P * D * Q = Matrix.of (fun i j =>
          Fin.cases (Fin.cases (D r c) (fun _ => 0) j)
            (fun i' => Fin.cases 0 (fun j' => C i' j') j) i) := by
  classical
  -- Move the chosen pivot to the upper-left corner using two involutions.
  let σ := Equiv.swap (0 : Fin (m + 1)) r
  let τ := Equiv.swap (0 : Fin (m + 1)) c
  let S : Matrix (Fin (m + 1)) (Fin (m + 1)) R :=
    (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) R).submatrix σ (Equiv.refl _)
  let T : Matrix (Fin (m + 1)) (Fin (m + 1)) R :=
    (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) R).submatrix (Equiv.refl _) τ
  have hSS : S * S = 1 := by
    dsimp only [S]
    rw [Matrix.one_submatrix_mul]
    ext i j
    exact congrArg (fun k => (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) R) k j)
      (Equiv.swap_apply_self 0 r i)
  have hTT : T * T = 1 := by
    dsimp only [T]
    rw [Matrix.mul_submatrix_one]
    ext i j
    exact congrArg (fun k => (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) R) i k)
      (Equiv.swap_apply_self 0 c j)
  have hS : IsUnit S := ⟨⟨S, S, hSS, hSS⟩, rfl⟩
  have hT : IsUnit T := ⟨⟨T, T, hTT, hTT⟩, rfl⟩
  let B := S * D * T
  have hB : B = D.submatrix σ τ := by
    dsimp only [B, S, T]
    rw [Matrix.one_submatrix_mul, Matrix.mul_submatrix_one]
    rfl
  have hB00 : B 0 0 = D r c := by
    simp [hB, Matrix.submatrix, σ, τ]
  have hdivB : ∀ i j, B 0 0 ∣ B i j := by
    intro i j
    rw [hB00, hB]
    exact hdiv _ _
  -- The first operation preserves row zero, so its divisibility also survives.
  obtain ⟨U, hU, hrow, hcol⟩ :=
    p06_9e0f5043ff_sdp_clear_first_column R m B (fun i => hdivB i.succ 0)
  obtain ⟨V, hV, hblock⟩ :=
    p06_9e0f5043ff_sdp_clear_first_row R m (U * B) hcol (by
      intro j
      rw [hrow 0, hrow j.succ]
      exact hdivB 0 j.succ)
  refine ⟨U * S, T * V, Matrix.of (fun i j => (U * B) i.succ j.succ),
    hU.mul hS, hT.mul hV, ?_⟩
  calc
    (U * S) * D * (T * V) = (U * B) * V := by
      simp only [B, mul_assoc]
    _ = _ := by
      simpa only [hrow 0, hB00, Matrix.of_apply] using hblock

end Submission

namespace Submission

/-- A residue module localized at a height-one prime is simple at its own prime
and is the zero module at every distinct height-one prime.

At its own prime, the localization equivalence over `B` transfers simplicity of
the residue field. Every nonzero element then also generates the module over the
localized ring, since the original scalars act through its canonical algebra map. -/
theorem p06_9e0f5043ff_llm_localized_residue_factors
    (B : Type*) [CommRing B] [IsDedekindDomain B]
    (p q : IsDedekindDomain.HeightOneSpectrum B) :
    (p = q → IsSimpleModule (Localization.AtPrime q.asIdeal)
      (LocalizedModule q.asIdeal.primeCompl (B ⧸ p.asIdeal))) ∧
    (p ≠ q → Subsingleton (LocalizedModule q.asIdeal.primeCompl (B ⧸ p.asIdeal))) := by
  constructor
  · rintro rfl
    -- At the same prime, every denominator acts invertibly on the residue field.
    let k := B ⧸ p.asIdeal
    let : Field k := Ideal.Quotient.field p.asIdeal
    let T := p.asIdeal.primeCompl
    have : IsLocalizedModule T (LinearMap.id : k →ₗ[B] k) := by
      refine ⟨?_, fun m ↦ ⟨(m, 1), by simp⟩, fun h ↦ ⟨1, by simpa using h⟩⟩
      intro s
      rw [Module.End.isUnit_iff]
      change Function.Bijective (fun m : k ↦ (s : B) • m)
      have hs : (Ideal.Quotient.mk p.asIdeal (s : B) : k) ≠ 0 :=
        fun h ↦ s.property ((Ideal.Quotient.eq_zero_iff_mem).mp h)
      simpa only [Algebra.smul_def, k, Ideal.Quotient.algebraMap_eq] using
        mulLeft_bijective₀ (Ideal.Quotient.mk p.asIdeal (s : B)) hs
    have : IsSimpleModule B k :=
      isSimpleModule_iff_isCoatom.mpr (Ideal.isMaximal_def.mp p.isMaximal)
    -- The localization equivalence preserves simplicity over B; enlarging scalars
    -- preserves the fact that each nonzero element generates the whole module.
    have : IsSimpleModule B (LocalizedModule T k) :=
      IsSimpleModule.congr
        (IsLocalizedModule.linearEquiv T (LocalizedModule.mkLinearMap T k) LinearMap.id)
    refine isSimpleModule_iff_toSpanSingleton_surjective.mpr
      ⟨IsSimpleModule.nontrivial B _, ?_⟩
    intro x hx y
    obtain ⟨b, hb⟩ := IsSimpleModule.toSpanSingleton_surjective B hx y
    exact ⟨algebraMap B (Localization.AtPrime p.asIdeal) b, by
      simpa only [LinearMap.toSpanSingleton_apply, algebraMap_smul] using hb⟩
  · intro hpq
    -- A distinct maximal ideal contains an annihilator outside the localization prime.
    have hnot : ¬p.asIdeal ≤ q.asIdeal := by
      intro h
      exact hpq (IsDedekindDomain.HeightOneSpectrum.asIdeal_injective
        (p.isMaximal.eq_of_le q.isPrime.ne_top h))
    obtain ⟨t, htp, htq⟩ := SetLike.not_le_iff_exists.mp hnot
    apply LocalizedModule.subsingleton_iff.mpr
    intro m
    refine ⟨t, htq, ?_⟩
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem.mpr htp, zero_mul]

end Submission

namespace Submission

/-- Diagonalization over a DVR, with no divisibility ordering on the diagonal. -/
theorem p06_9e0f5043ff_dlen_matrix_diagonalization
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (m : ℕ) (D : Matrix (Fin m) (Fin m) A) (hD : D.det ≠ 0) :
    ∃ (P Q : Matrix (Fin m) (Fin m) A) (d : Fin m → A),
      IsUnit P ∧ IsUnit Q ∧ (∀ i, d i ≠ 0) ∧ P * D * Q = Matrix.diagonal d := by
  classical
  induction m with
  | zero =>
      refine ⟨1, 1, Fin.elim0, isUnit_one, isUnit_one, ?_, ?_⟩
      · intro i
        exact Fin.elim0 i
      · ext i
        exact Fin.elim0 i
  | succ m ih =>
      -- The children select a dividing pivot and isolate its one-by-one block.
      have hentry : ∃ ij : Fin (m + 1) × Fin (m + 1), D ij.1 ij.2 ≠ 0 := by
        by_contra! h
        have hz : D = 0 := by
          ext i j
          exact h (i, j)
        exact hD (by simp [hz])
      obtain ⟨⟨r, c⟩, hp, hdiv⟩ :=
        p06_9e0f5043ff_dmd_finite_family_dividing_member A
          (Fin (m + 1) × Fin (m + 1)) (fun ij => D ij.1 ij.2) hentry
      obtain ⟨P₀, Q₀, C, hP₀, hQ₀, hsplit⟩ :=
        p06_9e0f5043ff_dmd_split_divisible_pivot A m D r c
          (fun i j => hdiv (i, j))
      let block (a : A) (B : Matrix (Fin m) (Fin m) A) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) A :=
        Matrix.of (fun i j =>
          Fin.cases (Fin.cases a (fun _ => 0) j)
            (fun i' => Fin.cases 0 (fun j' => B i' j') j) i)
      have hdet (a : A) (B : Matrix (Fin m) (Fin m) A) :
          (block a B).det = a * B.det := by
        rw [Matrix.det_succ_row_zero]
        simp [block, Fin.sum_univ_succ, Matrix.submatrix,
          show Matrix.of (fun i j => B i j) = B from rfl]
      have hmul (a b : A) (B E : Matrix (Fin m) (Fin m) A) :
          block a B * block b E = block (a * b) (B * E) := by
        ext i j
        refine Fin.cases ?_ (fun i => ?_) i <;>
          refine Fin.cases ?_ (fun j => ?_) j <;>
          simp [block, Matrix.mul_apply, Fin.sum_univ_succ]
      have hdiag (a : A) (d : Fin m → A) :
          block a (Matrix.diagonal d) = Matrix.diagonal (Fin.cases a d) := by
        ext i j
        refine Fin.cases ?_ (fun i => ?_) i <;>
          refine Fin.cases ?_ (fun j => ?_) j <;>
          simp [block, Matrix.diagonal, eq_comm]
      change P₀ * D * Q₀ = block (D r c) C at hsplit
      -- Nonvanishing of the determinant passes to the remaining block.
      have hsplit_det : (block (D r c) C).det ≠ 0 := by
        rw [← hsplit, Matrix.det_mul, Matrix.det_mul]
        exact mul_ne_zero
          (mul_ne_zero ((Matrix.isUnit_iff_isUnit_det P₀).mp hP₀).ne_zero hD)
          ((Matrix.isUnit_iff_isUnit_det Q₀).mp hQ₀).ne_zero
      have hC : C.det ≠ 0 := by
        intro hz
        apply hsplit_det
        rw [hdet, hz, mul_zero]
      obtain ⟨P', Q', d', hP', hQ', hd', heq⟩ := ih C hC
      have hunit (B : Matrix (Fin m) (Fin m) A) (hB : IsUnit B) :
          IsUnit (block 1 B) := by
        apply (Matrix.isUnit_iff_isUnit_det _).mpr
        rw [hdet, one_mul]
        exact (Matrix.isUnit_iff_isUnit_det B).mp hB
      refine ⟨block 1 P' * P₀, Q₀ * block 1 Q', Fin.cases (D r c) d',
        (hunit P' hP').mul hP₀, hQ₀.mul (hunit Q' hQ'), ?_, ?_⟩
      · intro i
        exact Fin.cases hp (fun j => hd' j) i
      · calc
          block 1 P' * P₀ * D * (Q₀ * block 1 Q') =
              block 1 P' * (P₀ * D * Q₀) * block 1 Q' := by
                simp only [mul_assoc]
          _ = block 1 P' * block (D r c) C * block 1 Q' := by rw [hsplit]
          _ = block (D r c) (P' * C * Q') := by rw [hmul, hmul, one_mul, mul_one]
          _ = Matrix.diagonal (Fin.cases (D r c) d') := by rw [heq, hdiag]

end Submission


namespace Submission
/-- The valuation ring in which the parameter is a nonunit consists exactly of
fractions whose denominator is not divisible by `X`. -/
theorem p06_9e0f5043ff_inf_valuation_fraction_characterization :
    ∀ (K F : Type*) [Field K] [Field F] [Algebra K F] (s : F),
      Transcendental K s →
      (∀ f : F, ∃ a b : Polynomial K, b ≠ 0 ∧
        f = Polynomial.aeval s a / Polynomial.aeval s b) →
      ∀ w : AlgebraicCurve.Place K F, s⁻¹ ∉ w.toValuationSubring →
      ∀ f : F, f ∈ w.toValuationSubring ↔
        ∃ a b : Polynomial K, ¬ (Polynomial.X : Polynomial K) ∣ b ∧
          f = Polynomial.aeval s a / Polynomial.aeval s b := by
  intro K F _ _ _ s hs hfrac w hsinv f
  classical
  let W : Subring F := w.toValuationSubring.toSubring
  have hsW : s ∈ W := (w.toValuationSubring.mem_or_inv_mem s).resolve_right hsinv
  have hs0 : s ≠ 0 := by
    intro h
    apply hsinv
    simp [h]
  have heval_mem (p : Polynomial K) : Polynomial.aeval s p ∈ W := by
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simpa only [map_add] using W.add_mem hp hq
    | monomial n a =>
      rw [Polynomial.aeval_monomial]
      exact W.mul_mem (w.algebraMap_mem' a) (W.pow_mem hsW n)
  have hunit_inv (u : Units W) :
      (((u⁻¹ : Units W) : W) : F) = (((u : W) : F))⁻¹ := by
    exact (Units.map W.subtype.toMonoidHom u).val_inv_eq_inv_val
  have heval_ne (p : Polynomial K) (hp : p ≠ 0) : Polynomial.aeval s p ≠ 0 := by
    intro h
    apply hp
    exact (transcendental_iff_injective.mp hs) (h.trans (map_zero _).symm)
  constructor
  · intro hf
    by_cases hf0 : f = 0
    · exact ⟨0, 1, by simp [Polynomial.X_dvd_iff], by simp [hf0]⟩
    obtain ⟨a, b, hb, hfab⟩ := hfrac f
    have ha : a ≠ 0 := by
      intro h
      apply hf0
      simpa [h] using hfab
    -- Remove all factors of X, leaving polynomials that evaluate to units.
    obtain ⟨a₀, ha_factor, ha₀⟩ :=
      Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd a ha 0
    obtain ⟨b₀, hb_factor, hb₀⟩ :=
      Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd b hb 0
    simp only [map_zero, sub_zero] at ha_factor ha₀ hb_factor hb₀
    obtain ⟨ua, hua⟩ :=
      (p06_9e0f5043ff_vfc_polynomial_unit_criterion K F s w hsinv a₀).mpr ha₀
    obtain ⟨ub, hub⟩ :=
      (p06_9e0f5043ff_vfc_polynomial_unit_criterion K F s w hsinv b₀).mpr hb₀
    let r := a.rootMultiplicity 0
    let k := b.rootMultiplicity 0
    let u : Units W := ua * ub⁻¹
    have hu : ((u : W) : F) = Polynomial.aeval s a₀ / Polynomial.aeval s b₀ := by
      change ((ua : W) : F) * (((ub⁻¹ : Units W) : W) : F) = _
      rw [hunit_inv, hua, hub, div_eq_mul_inv]
    have hnormalized : f = ((u : W) : F) * s ^ r / s ^ k := by
      rw [hfab, ha_factor, hb_factor, hu]
      simp only [map_mul, map_pow, Polynomial.aeval_X]
      dsimp only [r, k]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    -- Membership rules out a negative exponent of the nonunit parameter.
    have hkr : k ≤ r :=
      p06_9e0f5043ff_vfc_unit_power_quotient_exponents F W s hsW hsinv u r k
        (hnormalized ▸ hf)
    refine ⟨Polynomial.X ^ (r - k) * a₀, b₀, hb₀, ?_⟩
    have hb₀_ne : Polynomial.aeval s b₀ ≠ 0 :=
      heval_ne b₀ (fun h => hb₀ (by simp [h]))
    have hpow : s ^ r = s ^ (r - k) * s ^ k := by
      rw [← pow_add, Nat.sub_add_cancel hkr]
    rw [hnormalized, hu]
    simp only [map_mul, map_pow, Polynomial.aeval_X]
    rw [hpow]
    field_simp [hs0, hb₀_ne]
  · rintro ⟨a, b, hb, rfl⟩
    obtain ⟨u, hu⟩ :=
      (p06_9e0f5043ff_vfc_polynomial_unit_criterion K F s w hsinv b).mpr hb
    have hinv : (Polynomial.aeval s b)⁻¹ ∈ W := by
      rw [← hu, ← hunit_inv]
      exact ((u⁻¹ : Units W) : W).property
    change Polynomial.aeval s a / Polynomial.aeval s b ∈ W
    rw [div_eq_mul_inv]
    exact W.mul_mem (heval_mem a) hinv
end Submission

namespace Submission

/-- Left and right multiplication by unit matrices preserve the cokernel up to linear equivalence. -/
theorem p06_9e0f5043ff_dmc_cokernel_units :
    ∀ (R : Type*) [CommRing R] (m : ℕ) (D P Q : Matrix (Fin m) (Fin m) R),
      IsUnit P → IsUnit Q →
        Nonempty (((Fin m → R) ⧸ LinearMap.range (Matrix.mulVecLin D)) ≃ₗ[R]
          ((Fin m → R) ⧸ LinearMap.range (Matrix.mulVecLin (P * D * Q)))) := by
  intro R _ m D P Q hP hQ
  let eP := Matrix.toLinearEquiv' P hP.invertible
  let eQ := Matrix.toLinearEquiv' Q hQ.invertible
  -- Descend P and its inverse once P maps range(D) onto range(P * D * Q).
  refine ⟨Submodule.Quotient.equiv _ _ eP ?_⟩
  -- P(range D) = range (P * D), and surjectivity of Q gives range (P * D * Q).
  change (LinearMap.range D.mulVecLin).map P.mulVecLin =
    LinearMap.range (P * D * Q).mulVecLin
  rw [← LinearMap.range_comp, ← Matrix.mulVecLin_mul, Matrix.mulVecLin_mul (P * D) Q]
  exact (eQ.range_comp _).symm


end Submission

namespace Submission

/-- Localizing the given composition factors counts exactly the factors at `q`. -/
theorem p06_9e0f5043ff_wll_local_length_multiplicity
    (B : Type*) [CommRing B] [IsDedekindDomain B] (b : B)
    (s : CompositionSeries (Submodule B (B ⧸ Ideal.span ({b} : Set B))))
    (p : Fin s.length → IsDedekindDomain.HeightOneSpectrum B)
    (hhead : s.head = ⊥) (hlast : s.last = ⊤)
    (hfactors : ∀ i : Fin s.length,
      Nonempty ((↥(s i.succ) ⧸ (s i.castSucc).comap (s i.succ).subtype) ≃ₗ[B]
        (B ⧸ (p i).asIdeal)))
    (q : IsDedekindDomain.HeightOneSpectrum B) :
    Module.length (Localization.AtPrime q.asIdeal)
      (Localization.AtPrime q.asIdeal ⧸ Ideal.span
        ({algebraMap B (Localization.AtPrime q.asIdeal) b} :
          Set (Localization.AtPrime q.asIdeal))) =
      (Nat.card {i : Fin s.length // p i = q} : ℕ∞) := by
  classical
  let T := q.asIdeal.primeCompl
  let R := Localization.AtPrime q.asIdeal
  let I : Ideal B := Ideal.span ({b} : Set B)
  let f : B →ₗ[B] R := Algebra.linearMap B R
  -- The canonical localized quotient is the quotient by the image of `b`.
  have hI : I.localized' R T f = Ideal.span ({algebraMap B R b} : Set R) := by
    simpa only [I, Ideal.span, f, Set.image_singleton, Algebra.linearMap_apply] using
      (Submodule.localized'_span R T f ({b} : Set B))
  let e := (IsLocalizedModule.linearEquiv T (I.toLocalizedQuotient' R T f)
    (LocalizedModule.mkLinearMap T (B ⧸ I))).extendScalarsOfIsLocalization T R
  have hquot : Module.length R (R ⧸ Ideal.span ({algebraMap B R b} : Set R)) =
      Module.length R (LocalizedModule T (B ⧸ I)) := by
    rw [← hI]
    exact e.length_eq
  calc
    Module.length R (R ⧸ Ideal.span ({algebraMap B R b} : Set R)) =
        Module.length R (LocalizedModule T (B ⧸ I)) := hquot
    _ = ∑ i : Fin s.length, Module.length R
        (LocalizedModule T (↥(s i.succ) ⧸ (s i.castSucc).comap (s i.succ).subtype)) :=
      p06_9e0f5043ff_llm_localized_series_sum B (B ⧸ I) T s hhead hlast
    _ = ∑ i : Fin s.length, (if p i = q then (1 : ℕ∞) else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      let ei := IsLocalizedModule.mapEquiv T (LocalizedModule.mkLinearMap T _)
        (LocalizedModule.mkLinearMap T _) R (hfactors i).some
      rw [ei.length_eq]
      by_cases hi : p i = q
      · have := (p06_9e0f5043ff_llm_localized_residue_factors B (p i) q).1 hi
        simp only [if_pos hi, Module.length_eq_one]
      · have := (p06_9e0f5043ff_llm_localized_residue_factors B (p i) q).2 hi
        simp only [if_neg hi, Module.length_eq_zero]
    _ = (Nat.card {i : Fin s.length // p i = q} : ℕ∞) := by
      simp [Nat.card_eq_fintype_card, Fintype.card_subtype]

end Submission

namespace Submission

set_option warningAsError true

theorem p06_9e0f5043ff_fpm_normalized_orders
    (K F : Type*) [Field K] [Field F] [Algebra K F] (x : F)
    (hx : Transcendental K x) (q : Polynomial K) (hq : q.Monic)
    (hqirr : Irreducible q) (v : AlgebraicCurve.Place K F)
    (hv : ∀ f : F, f ∈ v.toValuationSubring ↔
      ∃ a b : Polynomial K, ¬ q ∣ b ∧
        f = Polynomial.aeval x a / Polynomial.aeval x b) :
    v.ord (Polynomial.aeval x q) = 1 ∧
      (∀ a : Polynomial K, ¬ q ∣ a → v.ord (Polynomial.aeval x a) = 0) := by
  obtain ⟨π, hπ, hπirr⟩ :=
    Submission.p06_9e0f5043ff_fno_irreducible_aeval K F x hx q hq hqirr v hv
  constructor
  · simpa only [hπ] using v.ord_coe_irreducible hπirr
  · intro a ha
    have hqone : ¬ q ∣ (1 : Polynomial K) := hqirr.not_dvd_one
    have hamem : Polynomial.aeval x a ∈ v.toValuationSubring :=
      (hv _).mpr ⟨a, 1, hqone, by simp⟩
    let z : v.toValuationSubring := ⟨Polynomial.aeval x a, hamem⟩
    have hz : IsUnit z :=
      (Submission.p06_9e0f5043ff_fno_fraction_isunit K F x hx q hq hqirr v hv
        a 1 z hqone (by simp [z])).mpr ha
    simpa only [IsUnit.unit_spec] using v.ord_coe_unit hz.unit

end Submission

namespace Submission

theorem p06_9e0f5043ff_dlen_diagonal_cokernel
    (R : Type*) [CommRing R] (m : ℕ) (D P Q : Matrix (Fin m) (Fin m) R)
    (d : Fin m → R) (hP : IsUnit P) (hQ : IsUnit Q)
    (hdiag : P * D * Q = Matrix.diagonal d) :
    Nonempty (((Fin m → R) ⧸ LinearMap.range (Matrix.mulVecLin D)) ≃ₗ[R]
      ((i : Fin m) → R ⧸ Ideal.span ({d i} : Set R))) := by
  obtain ⟨eUnits⟩ := Submission.p06_9e0f5043ff_dmc_cokernel_units R m D P Q hP hQ
  rw [hdiag] at eUnits
  obtain ⟨eDiagonal⟩ := Submission.p06_9e0f5043ff_dmc_diagonal_quotient R m d
  exact ⟨eUnits.trans eDiagonal⟩
theorem p06_9e0f5043ff_elp_integer_order :
    ∀ (K F : Type*) [Field K] [Field F] [Algebra K F] (x : F),
      Transcendental K x →
      (∀ f : F, ∃ a b : Polynomial K,
        b ≠ 0 ∧ f = Polynomial.aeval x a / Polynomial.aeval x b) →
      ∀ q : Polynomial K, q.Monic → Irreducible q →
      ∃ ν : F → ℤ, ν 0 = 0 ∧ ν (Polynomial.aeval x q) = 1 ∧
        (∀ f g : F, f ≠ 0 → g ≠ 0 → ν (f / g) = ν f - ν g) ∧
        (∀ f : F, f ≠ 0 → (0 ≤ ν f ↔
          ∃ a b : Polynomial K, ¬ q ∣ b ∧
            f = Polynomial.aeval x a / Polynomial.aeval x b)) := by
  intro K F _ _ _ x hx hrepr q hqmonic hq
  obtain ⟨μ, hμone, hμq, hμmul, hμzero, hμfactor⟩ :=
    Submission.p06_9e0f5043ff_io_polynomial_exponent K q hqmonic hq
  obtain ⟨ν, hνzero, hνfraction, hνdiv⟩ :=
    Submission.p06_9e0f5043ff_io_fraction_extension K F x hx hrepr μ hμmul
  have hinj : Function.Injective (Polynomial.aeval x : Polynomial K →ₐ[K] F) :=
    transcendental_iff_injective.mp hx
  have heval_ne : ∀ a : Polynomial K, a ≠ 0 → Polynomial.aeval x a ≠ 0 := by
    intro a ha h
    apply ha
    apply hinj
    simpa only [map_zero] using h
  refine ⟨ν, hνzero, ?_, hνdiv, ?_⟩
  · simpa only [map_one, div_one, hμq, hμone, Nat.cast_one, Nat.cast_zero, sub_zero]
      using hνfraction q 1 hq.ne_zero one_ne_zero
  · intro f hf
    constructor
    · intro hnonneg
      obtain ⟨a, b, hb, hrep⟩ := hrepr f
      have ha : a ≠ 0 := by
        intro ha
        apply hf
        rw [hrep, ha, map_zero, zero_div]
      have horder : 0 ≤ (μ a : ℤ) - (μ b : ℤ) := by
        rwa [hrep, hνfraction a b ha hb] at hnonneg
      have hba : μ b ≤ μ a := by
        exact_mod_cast sub_nonneg.mp horder
      obtain ⟨a₀, _, _, hafactor⟩ := hμfactor a ha
      obtain ⟨b₀, _, hqb₀, hbfactor⟩ := hμfactor b hb
      refine ⟨q ^ (μ a - μ b) * a₀, b₀, hqb₀, ?_⟩
      calc
        f = Polynomial.aeval x a / Polynomial.aeval x b := hrep
        _ = Polynomial.aeval x (q ^ μ a * a₀) /
            Polynomial.aeval x (q ^ μ b * b₀) :=
          congrArg₂ (fun r s : Polynomial K =>
            Polynomial.aeval x r / Polynomial.aeval x s) hafactor hbfactor
        _ = Polynomial.aeval x (q ^ (μ a - μ b) * a₀) /
            Polynomial.aeval x b₀ := by
          simp only [map_mul, map_pow]
          rw [← pow_mul_pow_sub (Polynomial.aeval x q) hba, mul_assoc,
            mul_div_mul_left _ _ (pow_ne_zero _ (heval_ne q hq.ne_zero))]
    · rintro ⟨a, b, hqb, hrep⟩
      have hb : b ≠ 0 := by
        rintro rfl
        exact hqb (dvd_zero q)
      have ha : a ≠ 0 := by
        intro ha
        apply hf
        rw [hrep, ha, map_zero, zero_div]
      rw [hrep, hνfraction a b ha hb, (hμzero b hb).2 hqb, Nat.cast_zero, sub_zero]
      exact Nat.cast_nonneg _
/-- An integer order characterizing subring membership makes every ideal principal. -/
theorem p06_9e0f5043ff_elp_principal_ideals_of_order :
    ∀ (F : Type*) [Field F] (A : Subring F) (ν : F → ℤ),
      (∀ f g : F, f ≠ 0 → g ≠ 0 → ν (f / g) = ν f - ν g) →
      (∀ f : F, f ≠ 0 → (f ∈ A ↔ 0 ≤ ν f)) → IsPrincipalIdealRing A := by
  intro F _ A ν hdiv hmem
  classical
  constructor
  intro I
  by_cases hI : I = ⊥
  · subst I
    infer_instance
  obtain ⟨z, hzI, hz⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  -- Minimize natural orders; subring membership will recover their integer values.
  have hex : ∃ n : ℕ, ∃ h : A, h ∈ I ∧ (h : F) ≠ 0 ∧ (ν (h : F)).toNat = n :=
    ⟨_, z, hzI, fun h => hz (Subtype.ext h), rfl⟩
  obtain ⟨h, hhI, hh, hν⟩ := Nat.find_spec hex
  refine ⟨⟨h, le_antisymm ?_ ((Ideal.span_singleton_le_iff_mem I).mpr hhI)⟩⟩
  intro z hzI
  by_cases hz : (z : F) = 0
  · have hz' : z = 0 := Subtype.ext hz
    rw [hz']
    exact Ideal.zero_mem _
  have hh_nonneg : 0 ≤ ν (h : F) := (hmem _ hh).mp h.property
  have hz_nonneg : 0 ≤ ν (z : F) := (hmem _ hz).mp z.property
  have hmin : (ν (h : F)).toNat ≤ (ν (z : F)).toNat := by
    rw [hν]
    exact Nat.find_min' hex ⟨z, hzI, hz, rfl⟩
  have horder : ν (h : F) ≤ ν (z : F) := by
    simpa only [Int.toNat_of_nonneg hh_nonneg, Int.toNat_of_nonneg hz_nonneg] using
      (Int.ofNat_le.mpr hmin)
  -- Leastness makes the quotient an element of A, giving the required multiple of h.
  have hquot : (z : F) / (h : F) ∈ A := by
    apply (hmem _ (div_ne_zero hz hh)).mpr
    rw [hdiv _ _ hz hh]
    exact sub_nonneg.mpr horder
  apply Ideal.mem_span_singleton'.mpr
  refine ⟨⟨(z : F) / (h : F), hquot⟩, ?_⟩
  apply Subtype.ext
  exact div_mul_cancel₀ _ hh

end Submission

namespace Submission

open IsDedekindDomain IsLocalRing AlgebraicCurve.Place

theorem p06_9e0f5043ff_ifl_residue_length_inertia
    (K E L : Type*) [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra K L] [Algebra E L] [IsScalarTower K E L]
    [FiniteDimensional E L] [Algebra.IsSeparable E L]
    (v : AlgebraicCurve.Place K E) (w : AlgebraicCurve.Place K L)
    (hw : w.restrict E = v) :
    Module.length v.toValuationSubring
      (integralClosureAt L v ⧸ (fiberCenter L v hw).asIdeal) =
        (w.inertiaDeg E : ℕ∞) := by
  classical
  subst v
  let A := (w.restrict E).toValuationSubring
  let B := integralClosureAt L (w.restrict E)
  let q := (fiberCenter L (w.restrict E) rfl).asIdeal
  -- The fiber center is the inverse image of the maximal ideal of O_w.
  let f : B →+* w.toValuationSubring :=
    (algebraMap B L).codRestrict w.toValuationSubring.toSubring
      (forall_mem_of_restrict_eq rfl)
  let g : B ⧸ q →+* w.ResidueField :=
    Ideal.Quotient.lift q ((residue _).comp f) (by
      intro b hb
      exact (Ideal.Quotient.eq_zero_iff_mem).mpr hb)
  have : q.IsMaximal := (fiberCenter L (w.restrict E) rfl).isMaximal
  let : Field (B ⧸ q) := Ideal.Quotient.field q
  have hg : Function.Surjective g := by
    -- Every element of O_w is a fraction with denominator outside the fiber center.
    intro y
    obtain ⟨x, rfl⟩ := residue_surjective (R := w.toValuationSubring) y
    have hx := x.property
    simp only [toValuationSubring_eq_of_restrict_eq (w := w) (v := w.restrict E) rfl] at hx
    obtain ⟨a, s, hs, hxs⟩ := hx
    have hs' : g (Ideal.Quotient.mk q s) ≠ 0 := by
      intro h
      have hmem : f s ∈ maximalIdeal w.toValuationSubring :=
        (Ideal.Quotient.eq_zero_iff_mem).mp h
      exact hs hmem
    refine ⟨Ideal.Quotient.mk q a / Ideal.Quotient.mk q s, ?_⟩
    rw [map_div₀, div_eq_iff hs']
    change residue _ (f a) = residue _ x * residue _ (f s)
    rw [← map_mul]
    apply congrArg (residue _)
    apply Subtype.ext
    change algebraMap B L a = (x : L) * algebraMap B L s
    rw [hxs]
    have hs0 : algebraMap B L s ≠ 0 := by
      intro h
      apply hs'
      change residue _ (f s) = 0
      have : f s = 0 := Subtype.ext h
      rw [this, map_zero]
    simpa only [div_eq_mul_inv] using (div_mul_cancel₀ (algebraMap B L a) hs0).symm
  let e := RingEquiv.ofBijective g ⟨g.injective, hg⟩
  -- Use exactly the residue-field scalar action defining the inertia degree.
  let : Algebra A w.ResidueField :=
    ((restrictResidueMap E w).comp (residue A)).toAlgebra
  have : IsScalarTower A (w.restrict E).ResidueField w.ResidueField :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let eA : (B ⧸ q) ≃ₐ[A] w.ResidueField :=
    { e with
      commutes' := by
        intro a
        change residue _ (f (algebraMap A B a)) =
          restrictResidueMap E w (residue A a)
        rw [restrictResidueMap_residue]
        apply congrArg (residue _)
        exact Subtype.ext rfl }
  have : Module.Finite A w.ResidueField :=
    Module.Finite.of_surjective eA.toLinearMap eA.surjective
  have : FiniteDimensional (w.restrict E).ResidueField w.ResidueField :=
    Module.Finite.of_restrictScalars_finite A (w.restrict E).ResidueField w.ResidueField
  -- Surjectivity of the residue map identifies the two submodule lattices.
  calc
    Module.length A (B ⧸ q) = Module.length A w.ResidueField := eA.toLinearEquiv.length_eq
    _ = Module.length (w.restrict E).ResidueField w.ResidueField :=
      Module.length_eq_of_surjective (residue_surjective (R := A))
    _ = (w.inertiaDeg E : ℕ∞) := Module.length_eq_finrank _ _

end Submission

namespace Submission

/-- Regroup residue composition factors by their height-one primes and substitute
the localized lengths, which count those factors. All sums remain in `ℕ∞`. -/
theorem p06_9e0f5043ff_ifl_weighted_local_lengths
    (A B : Type*) [CommRing A] [CommRing B] [IsDedekindDomain B] [Algebra A B]
    [Fintype (IsDedekindDomain.HeightOneSpectrum B)] (b : B) (hb : b ≠ 0)
    (n : ℕ) (hn : Module.length A (B ⧸ Ideal.span ({b} : Set B)) = (n : ℕ∞)) :
    Finset.sum Finset.univ (fun q : IsDedekindDomain.HeightOneSpectrum B =>
      Module.length A (B ⧸ q.asIdeal) *
        Module.length (Localization.AtPrime q.asIdeal)
          (Localization.AtPrime q.asIdeal ⧸
            Ideal.span ({algebraMap B (Localization.AtPrime q.asIdeal) b} :
              Set (Localization.AtPrime q.asIdeal)))) = (n : ℕ∞) := by
  classical
  obtain ⟨s, hs₀, hs₁, p, hp⟩ :=
    Submission.p06_9e0f5043ff_wll_residue_composition_series A B b hb n hn
  have hsum := Submission.p06_9e0f5043ff_wll_length_sum_factors
    A B (B ⧸ Ideal.span ({b} : Set B)) s p hs₀ hs₁ hp
  have hlocal := Submission.p06_9e0f5043ff_wll_local_length_multiplicity
    B b s p hs₀ hs₁ hp
  simp_rw [hlocal]
  calc
    _ = Finset.sum Finset.univ (fun q : IsDedekindDomain.HeightOneSpectrum B =>
        Finset.sum Finset.univ (fun _i : {i : Fin s.length // p i = q} =>
          Module.length A (B ⧸ q.asIdeal))) := by
      apply Finset.sum_congr rfl
      intro q _
      simp only [Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card,
        nsmul_eq_mul, mul_comm]
    _ = Finset.sum Finset.univ (fun i : Fin s.length =>
        Module.length A (B ⧸ (p i).asIdeal)) :=
      Fintype.sum_fiberwise' p (fun q => Module.length A (B ⧸ q.asIdeal))
    _ = (n : ℕ∞) := hsum.symm.trans hn

end Submission

namespace Submission

theorem p06_9e0f5043ff_elp_integer_order :
    ∀ (K F : Type*) [Field K] [Field F] [Algebra K F] (x : F),
      Transcendental K x →
      (∀ f : F, ∃ a b : Polynomial K,
        b ≠ 0 ∧ f = Polynomial.aeval x a / Polynomial.aeval x b) →
      ∀ q : Polynomial K, q.Monic → Irreducible q →
      ∃ ν : F → ℤ, ν 0 = 0 ∧ ν (Polynomial.aeval x q) = 1 ∧
        (∀ f g : F, f ≠ 0 → g ≠ 0 → ν (f / g) = ν f - ν g) ∧
        (∀ f : F, f ≠ 0 → (0 ≤ ν f ↔
          ∃ a b : Polynomial K, ¬ q ∣ b ∧
            f = Polynomial.aeval x a / Polynomial.aeval x b)) := by
  intro K F _ _ _ x hx hrepr q hqmonic hq
  obtain ⟨μ, hμone, hμq, hμmul, hμzero, hμfactor⟩ :=
    Submission.p06_9e0f5043ff_io_polynomial_exponent K q hqmonic hq
  obtain ⟨ν, hνzero, hνfraction, hνdiv⟩ :=
    Submission.p06_9e0f5043ff_io_fraction_extension K F x hx hrepr μ hμmul
  have hinj : Function.Injective (Polynomial.aeval x : Polynomial K →ₐ[K] F) :=
    transcendental_iff_injective.mp hx
  have heval_ne : ∀ a : Polynomial K, a ≠ 0 → Polynomial.aeval x a ≠ 0 := by
    intro a ha h
    apply ha
    apply hinj
    simpa only [map_zero] using h
  refine ⟨ν, hνzero, ?_, hνdiv, ?_⟩
  · simpa only [map_one, div_one, hμq, hμone, Nat.cast_one, Nat.cast_zero, sub_zero]
      using hνfraction q 1 hq.ne_zero one_ne_zero
  · intro f hf
    constructor
    · intro hnonneg
      obtain ⟨a, b, hb, hrep⟩ := hrepr f
      have ha : a ≠ 0 := by
        intro ha
        apply hf
        rw [hrep, ha, map_zero, zero_div]
      have horder : 0 ≤ (μ a : ℤ) - (μ b : ℤ) := by
        rwa [hrep, hνfraction a b ha hb] at hnonneg
      have hba : μ b ≤ μ a := by
        exact_mod_cast sub_nonneg.mp horder
      obtain ⟨a₀, _, _, hafactor⟩ := hμfactor a ha
      obtain ⟨b₀, _, hqb₀, hbfactor⟩ := hμfactor b hb
      refine ⟨q ^ (μ a - μ b) * a₀, b₀, hqb₀, ?_⟩
      calc
        f = Polynomial.aeval x a / Polynomial.aeval x b := hrep
        _ = Polynomial.aeval x (q ^ μ a * a₀) /
            Polynomial.aeval x (q ^ μ b * b₀) :=
          congrArg₂ (fun r s : Polynomial K =>
            Polynomial.aeval x r / Polynomial.aeval x s) hafactor hbfactor
        _ = Polynomial.aeval x (q ^ (μ a - μ b) * a₀) /
            Polynomial.aeval x b₀ := by
          simp only [map_mul, map_pow]
          rw [← pow_mul_pow_sub (Polynomial.aeval x q) hba, mul_assoc,
            mul_div_mul_left _ _ (pow_ne_zero _ (heval_ne q hq.ne_zero))]
    · rintro ⟨a, b, hqb, hrep⟩
      have hb : b ≠ 0 := by
        rintro rfl
        exact hqb (dvd_zero q)
      have ha : a ≠ 0 := by
        intro ha
        apply hf
        rw [hrep, ha, map_zero, zero_div]
      rw [hrep, hνfraction a b ha hb, (hμzero b hb).2 hqb, Nat.cast_zero, sub_zero]
      exact Nat.cast_nonneg _
/-- Over a place DVR, the cokernel length equals the order of the determinant. -/
theorem p06_9e0f5043ff_lno_dvr_determinant_length
    (K E : Type*) [Field K] [Field E] [Algebra K E]
    (v : AlgebraicCurve.Place K E) (M : Type*) [AddCommGroup M]
    [Module v.toValuationSubring M] [Module.Free v.toValuationSubring M]
    [Module.Finite v.toValuationSubring M] (T : M →ₗ[v.toValuationSubring] M)
    (hT : LinearMap.det T ≠ 0) :
    ∃ n : ℕ, Module.length v.toValuationSubring (M ⧸ LinearMap.range T) = (n : ℕ∞) ∧
      v.ord (algebraMap v.toValuationSubring E (LinearMap.det T)) = (n : ℤ) := by
  classical
  let A := v.toValuationSubring
  let m := Module.finrank A M
  let b := Module.finBasis A M
  let D := LinearMap.toMatrix b b T
  have hD : D.det ≠ 0 := by simpa [D] using hT
  obtain ⟨P, Q, d, hP, hQ, hd, hdiag⟩ :=
    p06_9e0f5043ff_dlen_matrix_diagonalization A m D hD
  obtain ⟨c⟩ := p06_9e0f5043ff_dlen_diagonal_cokernel A m D P Q d hP hQ hdiag
  choose a hlength hord using fun i => p06_9e0f5043ff_dlen_scalar_quotient K E v (d i) (hd i)
  have hcoord (x : M) : Matrix.mulVecLin D (b.equivFun x) = b.equivFun (T x) := by
    exact LinearMap.toMatrix_mulVec_repr b b T x
  have hrange : (LinearMap.range T).map b.equivFun.toLinearMap =
      LinearMap.range (Matrix.mulVecLin D) := by
    ext y
    constructor
    · rintro ⟨z, ⟨x, rfl⟩, rfl⟩
      exact ⟨b.equivFun x, hcoord x⟩
    · rintro ⟨x, rfl⟩
      refine ⟨T (b.equivFun.symm x), ⟨b.equivFun.symm x, rfl⟩, ?_⟩
      change b.equivFun (T (b.equivFun.symm x)) = Matrix.mulVecLin D x
      rw [← hcoord, LinearEquiv.apply_symm_apply]
  let e := Submodule.Quotient.equiv (LinearMap.range T)
    (LinearMap.range (Matrix.mulVecLin D)) b.equivFun hrange
  refine ⟨∑ i, a i, ?_, ?_⟩
  · rw [(e.trans c).length_eq, Module.length_pi_of_fintype]
    rw [Nat.cast_sum]
    exact Finset.sum_congr rfl (fun i _ => hlength i)
  · have hcoe (x : A) (hx : x ≠ 0) : algebraMap A E x ≠ 0 := by
      exact fun h => hx (Subtype.ext h)
    have hunit (x : A) (hx : IsUnit x) : v.ord (algebraMap A E x) = 0 := by
      obtain ⟨u, rfl⟩ := hx
      exact v.ord_coe_unit u
    have hPdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
    have hQdet : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).mp hQ
    have hdet : P.det * D.det * Q.det = ∏ i, d i := by
      simpa only [Matrix.det_mul, Matrix.det_diagonal] using congrArg Matrix.det hdiag
    have hprod : ∀ s : Finset (Fin m),
        v.ord (algebraMap A E (∏ i ∈ s, d i)) = ∑ i ∈ s, (a i : ℤ) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | @insert i s hi ih =>
        rw [Finset.prod_insert hi, map_mul,
          v.ord_mul (hcoe _ (hd i))
            (hcoe _ (Finset.prod_ne_zero_iff.mpr (fun j _ => hd j))),
          hord i, ih, Finset.sum_insert hi]
    have horder := congrArg (fun x : A => v.ord (algebraMap A E x)) hdet
    rw [map_mul, map_mul,
      v.ord_mul (mul_ne_zero (hcoe _ hPdet.ne_zero) (hcoe _ hD))
        (hcoe _ hQdet.ne_zero),
      v.ord_mul (hcoe _ hPdet.ne_zero) (hcoe _ hD),
      hunit _ hPdet, hunit _ hQdet, zero_add, add_zero, hprod] at horder
    simpa only [D, LinearMap.det_toMatrix, Nat.cast_sum] using horder

end Submission

namespace Submission

set_option warningAsError true in
/-- A compatible equivalence of valuation rings preserves normalized orders.

Transport a unit-times-uniformizer factorization through the two compatible equivalences,
then evaluate its normalized order in the target valuation ring. The factorization and
evaluation lemmas are `Place.exists_unit_mul_zpow` and `Place.ord_unit_smul_zpow`
from `Definitions.Def_AlgebraicCurve_DivisorClassGroup`. The uniformizer is supplied by
`IsDiscreteValuationRing.exists_irreducible`; `Irreducible.map` and `Units.map`
transport its irreducibility and the unit through the valuation-ring equivalence. -/
theorem p06_9e0f5043ff_pae_compatible_order_invariance
    (K E L : Type*) [Field K] [Field E] [Field L] [Algebra K E] [Algebra K L]
    (e : E ≃ₐ[K] L) (v : AlgebraicCurve.Place K E) (w : AlgebraicCurve.Place K L)
    (r : v.toValuationSubring ≃ₐ[K] w.toValuationSubring)
    (hcompat : ∀ a : v.toValuationSubring, (r a : L) = e (a : E))
    (f : E) (hf : f ≠ 0) : w.ord (e f) = v.ord f := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  have hπ' : Irreducible (r π) := hπ.map r
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  let u' : w.toValuationSubringˣ := Units.map r.toRingEquiv.toMonoidHom u
  have hcoeu : ((u' : w.toValuationSubring) : L) =
      e ((u : v.toValuationSubring) : E) := hcompat (u : v.toValuationSubring)
  have hfactor : e f = ((u' : w.toValuationSubring) : L) *
      ((r π : L) ^ v.ord f) := by
    simpa only [map_mul, map_zpow₀, hcoeu, hcompat π] using congrArg e hu
  rw [hfactor, w.ord_unit_smul_zpow u' hπ' (v.ord f)]

end Submission

namespace Submission

/-- Reindex the weighted local quotient lengths by the places above `v`. -/
theorem p06_9e0f5043ff_lno_integral_fiber_length
    (K E L : Type*) [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra K L] [Algebra E L] [IsScalarTower K E L]
    [FiniteDimensional E L] [Algebra.IsSeparable E L]
    (v : AlgebraicCurve.Place K E) (b : AlgebraicCurve.Place.integralClosureAt L v)
    (hb : b ≠ 0) (n : ℕ)
    (hn : Module.length v.toValuationSubring
      (AlgebraicCurve.Place.integralClosureAt L v ⧸
        Ideal.span ({b} : Set (AlgebraicCurve.Place.integralClosureAt L v))) = (n : ℕ∞)) :
    Finset.sum (v.fiberOver L) (fun w => (w.inertiaDeg E : ℤ) *
      w.ord (algebraMap (AlgebraicCurve.Place.integralClosureAt L v) L b)) = (n : ℤ) := by
  classical
  let B := Place.integralClosureAt L v
  let Q := IsDedekindDomain.HeightOneSpectrum B
  let : Fintype {w : Place K L // w.restrict E = v} :=
    (Place.finite_setOf_restrict_eq (F' := L) v).fintype
  let : Fintype Q := Fintype.ofEquiv _ (Place.fiberEquiv L v)
  -- Choose the finite local lengths supplied by the local order formula.
  choose m hm_length hm_order using fun q : Q =>
    p06_9e0f5043ff_ifl_local_length_order K E L v q
      (Localization.AtPrime q.asIdeal) b hb
  have hresidue (q : Q) : Module.length v.toValuationSubring (B ⧸ q.asIdeal) =
      ((Place.placeOfPrime q).inertiaDeg E : ℕ∞) := by
    have h :=
      p06_9e0f5043ff_ifl_residue_length_inertia K E L v
        (Place.placeOfPrime q) (Place.restrict_placeOfPrime q)
    rw [Place.fiberCenter_placeOfPrime] at h
    exact h
  -- All summands are finite, so the weighted length identity descends to ℕ.
  have hsum_nat : Finset.sum Finset.univ
      (fun q : Q => (Place.placeOfPrime q).inertiaDeg E * m q) = n := by
    have hweighted :=
      p06_9e0f5043ff_ifl_weighted_local_lengths v.toValuationSubring B b hb n hn
    apply ENat.natCast_inj.mp
    rw [← hweighted, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro q _
    rw [Nat.cast_mul, hresidue q, hm_length q]
  have hsum_int : Finset.sum Finset.univ (fun q : Q =>
      ((Place.placeOfPrime q).inertiaDeg E : ℤ) * (m q : ℤ)) = (n : ℤ) := by
    exact_mod_cast hsum_nat
  -- Reindex by the canonical correspondence between places and prime ideals.
  calc
    Finset.sum (v.fiberOver L) (fun w => (w.inertiaDeg E : ℤ) *
        w.ord (algebraMap B L b)) =
        Finset.sum Finset.univ (fun q : Q =>
          ((Place.placeOfPrime q).inertiaDeg E : ℤ) * (m q : ℤ)) := by
      refine Finset.sum_bij
        (fun w hw => Place.fiberCenter L v ((Place.mem_fiberOver v).mp hw))
        (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
      · intro w hw w' hw' h
        exact Place.eq_of_fiberCenter_eq
          ((Place.mem_fiberOver v).mp hw) ((Place.mem_fiberOver v).mp hw') h
      · intro q _
        exact ⟨Place.placeOfPrime q,
          (Place.mem_fiberOver v).mpr (Place.restrict_placeOfPrime q),
          Place.fiberCenter_placeOfPrime q⟩
      · intro w hw
        have hplace : Place.placeOfPrime
            (Place.fiberCenter L v ((Place.mem_fiberOver v).mp hw)) = w :=
          congrArg Subtype.val ((Place.fiberEquiv L v).symm_apply_apply
            ⟨w, (Place.mem_fiberOver v).mp hw⟩)
        rw [← hm_order _, hplace]
    _ = (n : ℤ) := hsum_int

end Submission

namespace Submission

/-- The finite place whose ring consists of fractions with denominator prime to `q`. -/
theorem p06_9e0f5043ff_fpm_exists_local_place
    (K F : Type*) [Field K] [Field F] [Algebra K F] (x : F)
    (hx : Transcendental K x)
    (hF : ∀ f : F, ∃ a b : Polynomial K, b ≠ 0 ∧
      f = Polynomial.aeval x a / Polynomial.aeval x b)
    (q : Polynomial K) (hqmonic : q.Monic) (hq : Irreducible q) :
    ∃ v : AlgebraicCurve.Place K F, ∀ f : F,
      f ∈ v.toValuationSubring ↔ ∃ a b : Polynomial K,
        ¬ q ∣ b ∧ f = Polynomial.aeval x a / Polynomial.aeval x b := by
  obtain ⟨A, hA⟩ := p06_9e0f5043ff_elp_fraction_subalgebra K F x hx q hqmonic hq
  obtain ⟨ν, hνzero, hνq, hνdiv, hνmem⟩ :=
    p06_9e0f5043ff_elp_integer_order K F x hx hF q hqmonic hq
  have hmem (f : F) (hf : f ≠ 0) : f ∈ A ↔ 0 ≤ ν f :=
    (hA f).trans (hνmem f hf).symm
  have hνone : ν 1 = 0 := by
    simpa only [div_self (one_ne_zero : (1 : F) ≠ 0), sub_self] using
      hνdiv 1 1 one_ne_zero one_ne_zero
  have hνinv (f : F) (hf : f ≠ 0) : ν f⁻¹ = -ν f := by
    simpa only [one_div, hνone, zero_sub] using hνdiv 1 f one_ne_zero hf
  -- The sign of the order gives the valuation-subring alternative.
  let V : ValuationSubring F :=
    { A.toSubring with
      mem_or_inv_mem' := by
        intro f
        change f ∈ A ∨ f⁻¹ ∈ A
        by_cases hf : f = 0
        · exact Or.inl (hf ▸ A.zero_mem)
        · by_cases hnonneg : 0 ≤ ν f
          · exact Or.inl ((hmem f hf).mpr hnonneg)
          · apply Or.inr
            apply (hmem f⁻¹ (inv_ne_zero hf)).mpr
            rw [hνinv f hf]
            omega }
  -- The inverse of q(x) has order -1, so this valuation subring is proper.
  have hqx : Polynomial.aeval x q ≠ 0 := by
    intro hzero
    rw [hzero, hνzero] at hνq
    omega
  have hVproper : V ≠ ⊤ := by
    intro htop
    have hin : (Polynomial.aeval x q)⁻¹ ∈ V := by
      rw [htop]
      exact ValuationSubring.mem_top _
    have hnonneg := (hmem _ (inv_ne_zero hqx)).mp hin
    rw [hνinv _ hqx, hνq] at hnonneg
    omega
  refine ⟨{
    toValuationSubring := V
    algebraMap_mem' := A.algebraMap_mem
    ne_top' := hVproper
    isPrincipalIdealRing' :=
      p06_9e0f5043ff_elp_principal_ideals_of_order F A.toSubring ν hνdiv hmem
  }, ?_⟩
  exact hA

end Submission

namespace Submission

set_option warningAsError true

/-- In the given polynomial-fraction model of a place, a fraction is a unit exactly when
its numerator is not divisible by the defining irreducible polynomial. -/
theorem p06_9e0f5043ff_fno_fraction_isunit
    (K F : Type*) [Field K] [Field F] [Algebra K F] (x : F)
    (hx : Transcendental K x) (q : Polynomial K) (_hqmonic : q.Monic)
    (hq : Irreducible q) (v : AlgebraicCurve.Place K F)
    (hmem : ∀ f : F, f ∈ v.toValuationSubring ↔
      ∃ a b : Polynomial K, ¬ q ∣ b ∧
        f = Polynomial.aeval x a / Polynomial.aeval x b)
    (a b : Polynomial K) (z : v.toValuationSubring) (hb : ¬ q ∣ b)
    (hz : (z : F) = Polynomial.aeval x a / Polynomial.aeval x b) :
    IsUnit z ↔ ¬ q ∣ a := by
  -- Transcendence lets us recover polynomial identities from identities in F.
  have hinj : Function.Injective (Polynomial.aeval x : Polynomial K →ₐ[K] F) :=
    transcendental_iff_injective.mp hx
  have hnonzero : ∀ p : Polynomial K, ¬ q ∣ p → Polynomial.aeval x p ≠ 0 := by
    intro p hp he
    have hpzero : p = 0 := hinj (by simpa only [map_zero] using he)
    exact hp (hpzero ▸ dvd_zero q)
  have hbzero := hnonzero b hb
  constructor
  · intro hu hqa
    -- Represent a unit's inverse, clear denominators, and use primality of q.
    obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.mp hu
    obtain ⟨c, d, hd, hwd⟩ := (hmem (w : F)).mp w.property
    have hprod : Polynomial.aeval x a * Polynomial.aeval x c =
        Polynomial.aeval x b * Polynomial.aeval x d := by
      have heq : (z : F) * (w : F) = 1 :=
        congrArg (fun t : v.toValuationSubring => (t : F)) hw
      rw [hz, hwd, div_mul_div_comm] at heq
      exact (div_eq_one_iff_eq (mul_ne_zero hbzero (hnonzero d hd))).mp heq
    have hpoly : a * c = b * d := hinj (by simpa only [map_mul] using hprod)
    have hdiv : q ∣ b * d := hpoly ▸ dvd_mul_of_dvd_left hqa c
    exact (hq.prime.dvd_or_dvd hdiv).elim hb hd
  · intro ha
    -- The reversed fraction belongs to the valuation subring and is an inverse.
    have hwmem : Polynomial.aeval x b / Polynomial.aeval x a ∈ v.toValuationSubring :=
      (hmem _).mpr ⟨b, a, ha, rfl⟩
    apply isUnit_iff_exists_inv.mpr
    refine ⟨⟨_, hwmem⟩, ?_⟩
    apply Subtype.ext
    change (z : F) * (Polynomial.aeval x b / Polynomial.aeval x a) = 1
    rw [hz, div_mul_div_comm, mul_comm (Polynomial.aeval x b) (Polynomial.aeval x a)]
    exact div_self (mul_ne_zero (hnonzero a ha) hbzero)

end Submission


namespace Submission

theorem p06_9e0f5043ff_lno_integral_norm_length
    (K E L : Type*) [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra K L] [Algebra E L] [IsScalarTower K E L]
    [FiniteDimensional E L] [Algebra.IsSeparable E L]
    (v : AlgebraicCurve.Place K E) (b : AlgebraicCurve.Place.integralClosureAt L v)
    (hb : b ≠ 0) :
    ∃ n : ℕ,
      Module.length v.toValuationSubring
        (AlgebraicCurve.Place.integralClosureAt L v ⧸
          Ideal.span ({b} : Set (AlgebraicCurve.Place.integralClosureAt L v))) = (n : ℕ∞) ∧
      v.ord (Algebra.norm E
        (algebraMap (AlgebraicCurve.Place.integralClosureAt L v) L b)) = (n : ℤ) := by
  classical
  let A := v.toValuationSubring
  let B := AlgebraicCurve.Place.integralClosureAt L v
  have : Module.Free A B := inferInstance
  have : IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors A)) L :=
    IsIntegralClosure.isLocalization A E L B
  -- Extending an integral basis to the fraction field identifies the two norms.
  have hnorm : Algebra.norm E (algebraMap B L b) =
      algebraMap A E (LinearMap.det (LinearMap.mul A B b)) := by
    let e := Module.finBasis A B
    have hmatrix : (algebraMap A E).mapMatrix (Algebra.leftMulMatrix e b) =
        Algebra.leftMulMatrix (e.localizationLocalization E (nonZeroDivisors A) L)
          (algebraMap B L b) := by
      ext i j
      simp only [Matrix.map_apply, RingHom.mapMatrix_apply,
        Algebra.leftMulMatrix_eq_repr_mul, ← map_mul,
        Module.Basis.localizationLocalization_apply,
        Module.Basis.localizationLocalization_repr_algebraMap]
    change Algebra.norm E (algebraMap B L b) = algebraMap A E (Algebra.norm A b)
    rw [Algebra.norm_eq_matrix_det (e.localizationLocalization E (nonZeroDivisors A) L),
      Algebra.norm_eq_matrix_det e, RingHom.map_det, hmatrix]
  have hbL : algebraMap B L b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective B L)).mpr hb
  have hdet : LinearMap.det (LinearMap.mul A B b) ≠ 0 := by
    intro hzero
    have hnorm0 : Algebra.norm E (algebraMap B L b) = 0 := by
      rw [hnorm, hzero, map_zero]
    exact hbL (Algebra.norm_eq_zero_iff.mp hnorm0)
  obtain ⟨n, hlength, hord⟩ :=
    Submission.p06_9e0f5043ff_lno_dvr_determinant_length K E v B
      (LinearMap.mul A B b) hdet
  refine ⟨n, ?_, ?_⟩
  · rw [Ideal.range_mul] at hlength
    exact (Submodule.Quotient.restrictScalarsEquiv A (Ideal.span {b})).length_eq.symm.trans
      hlength
  · rw [hnorm]
    exact hord

end Submission

namespace Submission

/-- An algebra equivalence transports places and preserves their residue degrees.
The valuation rings are pulled back along the inverse equivalence; their induced residue
algebra equivalences preserve `finrank` without a finite-dimensionality assumption. -/
theorem p06_9e0f5043ff_pae_place_equivalence_degree :
    ∀ (K E L : Type*) [Field K] [Field E] [Field L] [Algebra K E] [Algebra K L]
      (e : E ≃ₐ[K] L),
      ∃ θ : AlgebraicCurve.Place K E ≃ AlgebraicCurve.Place K L,
        (∀ v : AlgebraicCurve.Place K E, (θ v).deg = v.deg) ∧
        (∀ v : AlgebraicCurve.Place K E,
          ∃ r : v.toValuationSubring ≃ₐ[K] (θ v).toValuationSubring,
            ∀ a : v.toValuationSubring, (r a : L) = e (a : E)) := by
  intro K E L _ _ _ _ _ e
  classical
  -- Prove both directions together so the fields retain independent universes.
  have transport :
      (∀ (f : E ≃ₐ[K] L) (v : AlgebraicCurve.Place K E),
        ∃ w : AlgebraicCurve.Place K L,
          w.toValuationSubring = v.toValuationSubring.comap f.symm.toRingHom ∧
          ∃ r : v.toValuationSubring ≃ₐ[K] w.toValuationSubring,
            ∀ a : v.toValuationSubring, (r a : L) = f (a : E)) ∧
      (∀ (f : L ≃ₐ[K] E) (v : AlgebraicCurve.Place K L),
        ∃ w : AlgebraicCurve.Place K E,
          w.toValuationSubring = v.toValuationSubring.comap f.symm.toRingHom ∧
          ∃ r : v.toValuationSubring ≃ₐ[K] w.toValuationSubring,
            ∀ a : v.toValuationSubring, (r a : E) = f (a : L)) := by
    constructor <;> intro f v
    all_goals
      let A := v.toValuationSubring.comap f.symm.toRingHom
      let r₀ : v.toValuationSubring ≃+* A :=
        { toFun := fun a => ⟨f a, by simp [A, a.property]⟩
          invFun := fun b => ⟨f.symm b, b.property⟩
          left_inv := fun a => Subtype.ext (f.symm_apply_apply a)
          right_inv := fun b => Subtype.ext (f.apply_symm_apply b)
          map_mul' := fun a b => Subtype.ext (f.map_mul a b)
          map_add' := fun a b => Subtype.ext (f.map_add a b) }
      let w : AlgebraicCurve.Place K _ :=
        { toValuationSubring := A
          algebraMap_mem' := fun k => by
            change f.symm (algebraMap K _ k) ∈ v.toValuationSubring
            rw [f.symm.commutes]
            exact v.algebraMap_mem' k
          ne_top' := by
            intro h
            apply v.ne_top'
            apply eq_top_iff.mpr
            intro x _
            have hx : f x ∈ A := by
              rw [h]
              exact ValuationSubring.mem_top _
            change f.symm (f x) ∈ v.toValuationSubring at hx
            simpa using hx
          -- The pinned library transports generators through this surjective ring map.
          isPrincipalIdealRing' := IsPrincipalIdealRing.of_surjective r₀ r₀.surjective }
      let := AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring w
      let r : v.toValuationSubring ≃ₐ[K] w.toValuationSubring :=
        { r₀ with commutes' := fun k => Subtype.ext (f.commutes k) }
      exact ⟨w, rfl, r, fun _ => rfl⟩
  choose T hT using transport.1 e
  choose S hS using transport.2 e.symm
  let θ : AlgebraicCurve.Place K E ≃ AlgebraicCurve.Place K L :=
    { toFun := T
      invFun := S
      left_inv := fun v => by
        apply AlgebraicCurve.Place.ext
        rw [(hS (T v)).1, (hT v).1]
        apply SetLike.ext
        intro x
        change e.symm (e x) ∈ v.toValuationSubring ↔ x ∈ v.toValuationSubring
        rw [e.symm_apply_apply]
      right_inv := fun v => by
        apply AlgebraicCurve.Place.ext
        rw [(hT (S v)).1, (hS v).1]
        apply SetLike.ext
        intro x
        change e (e.symm x) ∈ v.toValuationSubring ↔ x ∈ v.toValuationSubring
        rw [e.apply_symm_apply] }
  refine ⟨θ, ?_, fun v => (hT v).2⟩
  intro v
  obtain ⟨r, _⟩ := (hT v).2
  -- The residue equivalence descends through the maximal ideals; finrank needs no finiteness.
  exact (IsLocalRing.ResidueField.mapAlgEquiv r).toLinearEquiv.finrank_eq.symm

end Submission

namespace Submission

set_option warningAsError true in
/-- Transport principal divisors along an algebra equivalence using the approved
place equivalence and normalized-order invariance. The finite-support reindexing
lemmas are from the pinned `Mathlib.Data.Finsupp.Basic`. -/
theorem p06_9e0f5043ff_principal_alg_equiv
    (K E L : Type*) [Field K] [Field E] [Field L] [Algebra K E] [Algebra K L]
    (e : E ≃ₐ[K] L) (h : HasPrincipalDivisors K E) : HasPrincipalDivisors K L := by
  classical
  obtain ⟨θ, hdeg, hring⟩ := p06_9e0f5043ff_pae_place_equivalence_degree K E L e
  refine ⟨fun f hf => ?_⟩
  have hf' : e.symm f ≠ 0 := by
    intro hzero
    apply hf
    simpa only [AlgEquiv.apply_symm_apply, map_zero] using congrArg e hzero
  obtain ⟨D, hD, hDdeg⟩ := h.exists_divisor (e.symm f) hf'
  refine ⟨Finsupp.equivMapDomain θ D, ?_, ?_⟩
  · intro w
    obtain ⟨r, hr⟩ := hring (θ.symm w)
    have hord := p06_9e0f5043ff_pae_compatible_order_invariance K E L e
      (θ.symm w) (θ (θ.symm w)) r hr (e.symm f) hf'
    rw [Finsupp.equivMapDomain_apply, hD]
    simpa only [Equiv.apply_symm_apply, AlgEquiv.apply_symm_apply] using hord.symm
  · change (Finsupp.equivMapDomain θ D).sum (fun w n => n * (w.deg : ℤ)) = 0
    rw [Finsupp.sum_equivMapDomain]
    change D.sum (fun v n => n * (v.deg : ℤ)) = 0 at hDdeg
    simpa only [hdeg] using hDdeg

end Submission

set_option warningAsError true

namespace Submission

/-- A place containing the polynomial coordinate is the localization at a monic
irreducible polynomial. The frozen proof base supplies `Place.center_ne_bot`
for the nonzero prime center and `Place.toValuationSubring_eq_of_forall_mem`
for its localization in `Definitions.Def_AlgebraicCurve_PlacesOverDVR`. -/
theorem p06_9e0f5043ff_rmp_finite_place_classification
    (K : Type*) [Field K]
    (v : AlgebraicCurve.Place K (FractionRing (Polynomial K)))
    (hX : algebraMap (Polynomial K) (FractionRing (Polynomial K)) Polynomial.X ∈
      v.toValuationSubring) :
    ∃ q : Polynomial K, q.Monic ∧ Irreducible q ∧
      (∀ f : FractionRing (Polynomial K), f ∈ v.toValuationSubring ↔
        ∃ a b : Polynomial K, ¬ q ∣ b ∧
          f = algebraMap (Polynomial K) (FractionRing (Polynomial K)) a /
            algebraMap (Polynomial K) (FractionRing (Polynomial K)) b) := by
  classical
  -- Constants and the coordinate generate the polynomial ring.
  have hpoly : ∀ p : Polynomial K,
      algebraMap (Polynomial K) (FractionRing (Polynomial K)) p ∈
        v.toValuationSubring := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p r hp hr => simpa only [map_add] using add_mem hp hr
    | monomial n a =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow]
      apply mul_mem
      · rw [Polynomial.C_eq_algebraMap, ← IsScalarTower.algebraMap_apply]
        exact v.algebraMap_mem' a
      · exact pow_mem hX n
  -- Normalize the generator of the nonzero prime center.
  obtain ⟨q, hnorm, hspan⟩ := Ideal.exists_normalized_span_of_isPrincipal
    (AlgebraicCurve.Place.center (Polynomial K) v hpoly)
  have hq0 : q ≠ 0 := by
    intro hq
    apply v.center_ne_bot hpoly
    simpa only [hq, Ideal.span_singleton_zero] using hspan
  have hprime : (Ideal.span {q}).IsPrime := by
    rw [← hspan]
    infer_instance
  refine ⟨q, (Polynomial.normalize_eq_self_iff_monic hq0).mp hnorm,
    ((Ideal.span_singleton_prime hq0).mp hprime).irreducible, ?_⟩
  intro f
  -- The inherited localization theorem supplies both membership directions.
  -- Since the center is (q), its complement consists of denominators not divisible by q.
  rw [v.toValuationSubring_eq_of_forall_mem hpoly]
  change (∃ (a b : Polynomial K)
    (_ : b ∉ AlgebraicCurve.Place.center (Polynomial K) v hpoly),
      f = algebraMap (Polynomial K) (FractionRing (Polynomial K)) a *
        (algebraMap (Polynomial K) (FractionRing (Polynomial K)) b)⁻¹) ↔ _
  simp only [hspan, Ideal.mem_span_singleton, exists_prop, div_eq_mul_inv]

end Submission

namespace Submission

/-- Assemble the finite place, its residue degree, and its normalized orders. -/
theorem p06_9e0f5043ff_rmp_finite_place_model
    (K F : Type*) [Field K] [Field F] [Algebra K F] (x : F)
    (hx : Transcendental K x)
    (hfrac : ∀ f : F, ∃ a b : Polynomial K,
      b ≠ 0 ∧ f = Polynomial.aeval x a / Polynomial.aeval x b)
    (q : Polynomial K) (hq : q.Monic) (hirr : Irreducible q) :
    ∃ v : AlgebraicCurve.Place K F,
      (∀ f : F, f ∈ v.toValuationSubring ↔ ∃ a b : Polynomial K,
        ¬ q ∣ b ∧ f = Polynomial.aeval x a / Polynomial.aeval x b) ∧
      v.deg = q.natDegree ∧
      v.ord (Polynomial.aeval x q) = 1 ∧
      (∀ a : Polynomial K, ¬ q ∣ a → v.ord (Polynomial.aeval x a) = 0) := by
  obtain ⟨v, hv⟩ :=
    Submission.p06_9e0f5043ff_fpm_exists_local_place K F x hx hfrac q hq hirr
  exact ⟨v, hv,
    Submission.p06_9e0f5043ff_fpm_residue_degree K F x hx q hq hirr v hv,
    Submission.p06_9e0f5043ff_fpm_normalized_orders K F x hx q hq hirr v hv⟩

end Submission

namespace Submission

/-- Extend the integral norm-order identity to the fraction field of the integral closure. -/
theorem p06_9e0f5043ff_local_norm_order
    (K E L : Type*) [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra K L] [Algebra E L] [IsScalarTower K E L]
    [FiniteDimensional E L] [Algebra.IsSeparable E L]
    (v : AlgebraicCurve.Place K E) (f : L) (hf : f ≠ 0) :
    v.ord (Algebra.norm E f) = Finset.sum (v.fiberOver L)
      (fun w => (w.inertiaDeg E : ℤ) * w.ord f) := by
  classical
  let B := AlgebraicCurve.Place.integralClosureAt L v
  have hintegral (b : B) (hb : b ≠ 0) :
      v.ord (Algebra.norm E (algebraMap B L b)) =
        Finset.sum (v.fiberOver L)
          (fun w => (w.inertiaDeg E : ℤ) * w.ord (algebraMap B L b)) := by
    obtain ⟨n, hlength, hord⟩ :=
      p06_9e0f5043ff_lno_integral_norm_length K E L v b hb
    exact hord.trans (p06_9e0f5043ff_lno_integral_fiber_length K E L v b hb n hlength).symm
  obtain ⟨b, c, hc, hfrac⟩ := IsFractionRing.div_surjective B f
  have hcL : algebraMap B L c ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hc
  have hbL : algebraMap B L b ≠ 0 := by
    intro hb0
    apply hf
    rw [← hfrac, hb0, zero_div]
  have hb : b ≠ 0 := fun h => hbL (by rw [h, map_zero])
  have hcB : c ≠ 0 := fun h => hcL (by rw [h, map_zero])
  have hord (w : AlgebraicCurve.Place K L) :
      w.ord (algebraMap B L b / algebraMap B L c) =
        w.ord (algebraMap B L b) - w.ord (algebraMap B L c) := by
    rw [div_eq_mul_inv, w.ord_mul hbL (inv_ne_zero hcL), w.ord_inv, sub_eq_add_neg]
  calc
    v.ord (Algebra.norm E f) =
        v.ord (Algebra.norm E (algebraMap B L b)) -
          v.ord (Algebra.norm E (algebraMap B L c)) := by
      rw [← hfrac, div_eq_mul_inv, map_mul, Algebra.norm_inv,
        v.ord_mul (Algebra.norm_ne_zero_iff.mpr hbL)
          (inv_ne_zero (Algebra.norm_ne_zero_iff.mpr hcL)),
        v.ord_inv, sub_eq_add_neg]
    _ = Finset.sum (v.fiberOver L)
          (fun w => (w.inertiaDeg E : ℤ) * w.ord (algebraMap B L b)) -
        Finset.sum (v.fiberOver L)
          (fun w => (w.inertiaDeg E : ℤ) * w.ord (algebraMap B L c)) := by
      rw [hintegral b hb, hintegral c hcB]
    _ = Finset.sum (v.fiberOver L) (fun w => (w.inertiaDeg E : ℤ) * w.ord f) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro w _
      rw [← hfrac, hord, mul_sub]

end Submission

namespace Submission

/-- The unique place at infinity, obtained from the finite place of the reciprocal variable. -/
theorem p06_9e0f5043ff_rmp_infinity_place :
    ∀ (K : Type*) [Field K],
      ∃ v : AlgebraicCurve.Place K (FractionRing (Polynomial K)),
        algebraMap (Polynomial K) (FractionRing (Polynomial K)) Polynomial.X ∉
            v.toValuationSubring ∧
          v.deg = 1 ∧
          (∀ a : Polynomial K, a ≠ 0 →
            v.ord (algebraMap (Polynomial K) (FractionRing (Polynomial K)) a) =
              -(a.natDegree : ℤ)) ∧
          (∀ w : AlgebraicCurve.Place K (FractionRing (Polynomial K)),
            algebraMap (Polynomial K) (FractionRing (Polynomial K)) Polynomial.X ∉
                w.toValuationSubring → w = v) := by
  intro K _
  let t : FractionRing (Polynomial K) :=
    algebraMap (Polynomial K) (FractionRing (Polynomial K)) Polynomial.X
  let s : FractionRing (Polynomial K) := t⁻¹
  obtain ⟨hs, hfractions⟩ := p06_9e0f5043ff_inf_reciprocal_presentation K
  change Transcendental K s at hs
  change ∀ f : FractionRing (Polynomial K), ∃ a b : Polynomial K, b ≠ 0 ∧
    f = Polynomial.aeval s a / Polynomial.aeval s b at hfractions
  have hinj := transcendental_iff_injective.mp hs
  have hs0 : s ≠ 0 := by
    simpa only [Polynomial.aeval_X, map_zero] using
      hinj.ne (Polynomial.X_ne_zero (R := K))
  obtain ⟨v, hmem, hdeg, hord, hunits⟩ :=
    p06_9e0f5043ff_rmp_finite_place_model K (FractionRing (Polynomial K)) s hs hfractions
      Polynomial.X Polynomial.monic_X Polynomial.irreducible_X
  have hnotmem : t ∉ v.toValuationSubring := by
    intro ht
    obtain ⟨a, b, hb, hab⟩ := (hmem t).mp ht
    have hb0 : b ≠ 0 := fun h => hb (h ▸ dvd_zero Polynomial.X)
    have hbeval : Polynomial.aeval s b ≠ 0 := by
      simpa only [map_zero] using hinj.ne hb0
    have hmul : s⁻¹ * Polynomial.aeval s b = Polynomial.aeval s a := by
      apply (eq_div_iff hbeval).mp
      change t⁻¹⁻¹ = _
      rw [inv_inv]
      exact hab
    apply hb
    refine ⟨a, hinj ?_⟩
    rw [map_mul, Polynomial.aeval_X]
    calc
      Polynomial.aeval s b = s * (s⁻¹ * Polynomial.aeval s b) := by
        rw [← mul_assoc, mul_inv_cancel₀ hs0, one_mul]
      _ = s * Polynomial.aeval s a := by rw [hmul]
  refine ⟨v, hnotmem, ?_, ?_, ?_⟩
  · simpa only [Polynomial.natDegree_X] using hdeg
  · intro a ha
    have hsord : v.ord s = 1 := by
      simpa only [Polynomial.aeval_X] using hord
    have heval : Polynomial.aeval s⁻¹ a =
        algebraMap (Polynomial K) (FractionRing (Polynomial K)) a := by
      change Polynomial.aeval t⁻¹⁻¹ a = _
      rw [inv_inv]
      simpa only [Polynomial.aeval_X_left_apply, IsScalarTower.toAlgHom_apply] using
        (Polynomial.aeval_algHom_apply
          (IsScalarTower.toAlgHom K (Polynomial K) (FractionRing (Polynomial K)))
          Polynomial.X a)
    rw [← heval]
    exact p06_9e0f5043ff_inf_reciprocal_polynomial_order
      K (FractionRing (Polynomial K)) s hs v hsord hunits a ha
  · intro w hw
    have hw' : s⁻¹ ∉ w.toValuationSubring := by
      change t⁻¹⁻¹ ∉ w.toValuationSubring
      rw [inv_inv]
      exact hw
    apply AlgebraicCurve.Place.ext
    apply SetLike.ext
    intro f
    exact (p06_9e0f5043ff_inf_valuation_fraction_characterization
      K (FractionRing (Polynomial K)) s hs hfractions w hw' f).trans (hmem f).symm

end Submission


namespace Submission

/-- The rational function field has principal divisors, assembled from the finite
places and the unique place at infinity. -/
theorem p06_9e0f5043ff_rational_model_principal (K : Type*) [Field K] :
    AlgebraicCurve.HasPrincipalDivisors K (FractionRing (Polynomial K)) := by
  classical
  let M := FractionRing (Polynomial K)
  let ι : Polynomial K →+* M := algebraMap (Polynomial K) M
  have hι : Function.Injective ι := IsFractionRing.injective (Polynomial K) M
  have hιne (a : Polynomial K) (ha : a ≠ 0) : ι a ≠ 0 := by
    intro h
    exact ha (hι (h.trans (map_zero ι).symm))
  have heval (a : Polynomial K) : Polynomial.aeval (ι Polynomial.X) a = ι a := by
    change Polynomial.aeval (algebraMap (Polynomial K) M Polynomial.X) a =
      algebraMap (Polynomial K) M a
    rw [Polynomial.aeval_algebraMap_apply, Polynomial.aeval_X_left_apply]
  have hx : Transcendental K (ι Polynomial.X) :=
    (transcendental_algebraMap_iff hι).mpr (Polynomial.transcendental_X K)
  have hrep (f : M) : ∃ a b : Polynomial K, b ≠ 0 ∧ f = ι a / ι b := by
    obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (Polynomial K) f
    exact ⟨a, b, mem_nonZeroDivisors_iff_ne_zero.mp hb, hab.symm⟩
  have hrepEval (f : M) : ∃ a b : Polynomial K, b ≠ 0 ∧
      f = Polynomial.aeval (ι Polynomial.X) a / Polynomial.aeval (ι Polynomial.X) b := by
    simpa only [heval] using hrep f
  have hmodel (q : Polynomial K) (hm : q.Monic) (hi : Irreducible q) :
      ∃ v : Place K M,
        (∀ f : M, f ∈ v.toValuationSubring ↔
          ∃ a b : Polynomial K, ¬ q ∣ b ∧ f = ι a / ι b) ∧
        v.deg = q.natDegree ∧ v.ord (ι q) = 1 ∧
        (∀ a : Polynomial K, ¬ q ∣ a → v.ord (ι a) = 0) := by
    simpa only [heval] using
      p06_9e0f5043ff_rmp_finite_place_model K M (ι Polynomial.X) hx hrepEval q hm hi
  obtain ⟨vinf, hinfX, hinfdeg, hinford, hinfunique⟩ :=
    p06_9e0f5043ff_rmp_infinity_place K

  -- Divisor witnesses are closed under multiplication of nonzero functions.
  let P : M → Prop := fun f => ∃ D : Divisor K M,
    (∀ v : Place K M, D v = v.ord f) ∧ Divisor.degree D = 0
  have hmul {f g : M} (hf : f ≠ 0) (hg : g ≠ 0) (hPf : P f) (hPg : P g) :
      P (f * g) := by
    obtain ⟨D, hD, hDdeg⟩ := hPf
    obtain ⟨E, hE, hEdeg⟩ := hPg
    refine ⟨D + E, ?_, ?_⟩
    · intro v
      rw [Finsupp.add_apply, hD v, hE v, v.ord_mul hf hg]
    · rw [map_add, hDdeg, hEdeg, add_zero]
  have hunit (a : Polynomial K) (ha : IsUnit a) : P (ι a) := by
    obtain ⟨c, hc, rfl⟩ := Polynomial.isUnit_iff.mp ha
    obtain ⟨u, rfl⟩ := hc
    refine ⟨0, ?_, map_zero _⟩
    intro v
    change 0 = v.ord (algebraMap K M (u : K))
    exact (v.ord_coe_unit
      (Units.map (algebraMap K v.toValuationSubring).toMonoidHom u)).symm

  -- A monic irreducible contributes [v_q] - deg(q) [vinf].
  have hmonic (q : Polynomial K) (hm : q.Monic) (hi : Irreducible q) : P (ι q) := by
    obtain ⟨vq, hvq, hvqdeg, hvqord, _⟩ := hmodel q hm hi
    have hqone : ¬ q ∣ (1 : Polynomial K) := fun h =>
      hi.not_isUnit (isUnit_iff_dvd_one.mpr h)
    have hvqX : ι Polynomial.X ∈ vq.toValuationSubring := by
      exact (hvq _).mpr ⟨Polynomial.X, 1, hqone, by simp⟩
    have hvqinf : vq ≠ vinf := by
      intro h
      exact hinfX (h ▸ hvqX)
    refine ⟨Finsupp.single vq 1 - Finsupp.single vinf (q.natDegree : ℤ), ?_, ?_⟩
    · intro w
      by_cases hwX : ι Polynomial.X ∈ w.toValuationSubring
      · have hwinf : w ≠ vinf := by
          intro h
          exact hinfX (h ▸ hwX)
        obtain ⟨r, hrm, hri, hwr⟩ :=
          p06_9e0f5043ff_rmp_finite_place_classification K w hwX
        obtain ⟨vr, hvr, _, _, hvrcoprime⟩ := hmodel r hrm hri
        have hwvr : w = vr := by
          apply Place.ext
          exact SetLike.ext fun f => (hwr f).trans (hvr f).symm
        subst vr
        by_cases hrq : r = q
        · subst r
          have hwq : w = vq := by
            apply Place.ext
            exact SetLike.ext fun f => (hvr f).trans (hvq f).symm
          subst w
          simp [Finsupp.sub_apply, hvqinf, hvqord]
        · have hrndvd : ¬ r ∣ q := by
            intro h
            exact hrq (Polynomial.eq_of_monic_of_associated hrm hm
              (hri.associated_of_dvd hi h))
          have hwq : w ≠ vq := by
            intro h
            have hz := hvrcoprime q hrndvd
            rw [h, hvqord] at hz
            norm_num at hz
          simp [Finsupp.sub_apply, hwq, hwinf, hvrcoprime q hrndvd]
      · have hwinf : w = vinf := hinfunique w hwX
        subst w
        have hqinf : vinf.ord (ι q) = -(q.natDegree : ℤ) := hinford q hi.ne_zero
        simp [Finsupp.sub_apply, hvqinf, hqinf]
    · simp only [map_sub, Divisor.degree_single, hvqdeg, hinfdeg,
        Nat.cast_one, mul_one, one_mul, sub_self]

  -- Normalize irreducibles, then assemble a polynomial's finitely many factors.
  have hirred (q : Polynomial K) (hq : Irreducible q) : P (ι q) := by
    have hn := (associated_normalize q).irreducible hq
    have hPn := hmonic (normalize q) (Polynomial.monic_normalize hq.ne_zero) hn
    obtain ⟨u, hu⟩ := normalize_associated q
    rw [← hu, map_mul]
    exact hmul (hιne _ hn.ne_zero) (hιne _ u.ne_zero) hPn (hunit _ u.isUnit)
  have hpoly (a : Polynomial K) : a ≠ 0 → P (ι a) := by
    induction a using WfDvdMonoid.induction_on_irreducible with
    | zero => exact fun h => (h rfl).elim
    | unit a ha => exact fun _ => hunit a ha
    | mul a q ha hq ih =>
        intro _
        rw [map_mul]
        exact hmul (hιne q hq.ne_zero) (hιne a ha) (hirred q hq) (ih ha)

  -- Subtract the denominator divisor from the numerator divisor.
  refine ⟨?_⟩
  intro f hf
  obtain ⟨a, b, hb, rfl⟩ := hrep f
  have ha : a ≠ 0 := by
    intro ha
    apply hf
    simp [ha]
  obtain ⟨D, hD, hDdeg⟩ := hpoly a ha
  obtain ⟨E, hE, hEdeg⟩ := hpoly b hb
  refine ⟨D - E, ?_, ?_⟩
  · intro v
    rw [Finsupp.sub_apply, hD v, hE v, div_eq_mul_inv,
      v.ord_mul (hιne a ha) (inv_ne_zero (hιne b hb)), v.ord_inv, sub_eq_add_neg]
  · rw [map_sub, hDdeg, hEdeg, sub_self]

end Submission

namespace Submission

open scoped IntermediateField.algebraAdjoinAdjoin in
theorem p06_9e0f5043ff_rational_adjoin_principal
    (K : Type*) [Field K] {F : Type*} [Field F] [Algebra K F]
    (x : F) (hx : Transcendental K x) :
    HasPrincipalDivisors K (IntermediateField.adjoin K ({x} : Set F)) := by
  let e : FractionRing (Polynomial K) ≃ₐ[K] IntermediateField.adjoin K ({x} : Set F) :=
    IsFractionRing.algEquivOfAlgEquiv (Polynomial.algEquivOfTranscendental K x hx)
  exact Submission.p06_9e0f5043ff_principal_alg_equiv K (FractionRing (Polynomial K))
    (IntermediateField.adjoin K ({x} : Set F)) e
    (Submission.p06_9e0f5043ff_rational_model_principal K)
set_option warningAsError true

theorem p06_9e0f5043ff_fno_irreducible_aeval
    (K F : Type*) [Field K] [Field F] [Algebra K F] (x : F)
    (hx : Transcendental K x) (q : Polynomial K) (hq : q.Monic)
    (hqi : Irreducible q) (v : AlgebraicCurve.Place K F)
    (hv : ∀ f : F, f ∈ v.toValuationSubring ↔
      ∃ a b : Polynomial K, ¬ q ∣ b ∧
        f = Polynomial.aeval x a / Polynomial.aeval x b) :
    ∃ π : v.toValuationSubring, (π : F) = Polynomial.aeval x q ∧ Irreducible π := by
  classical
  have hinj : Function.Injective (Polynomial.aeval x : Polynomial K →ₐ[K] F) :=
    transcendental_iff_injective.mp hx
  have hq1 : ¬ q ∣ (1 : Polynomial K) := hqi.not_dvd_one
  let π : v.toValuationSubring :=
    ⟨Polynomial.aeval x q, (hv _).mpr ⟨q, 1, hq1, by simp⟩⟩
  refine ⟨π, rfl, ?_⟩
  constructor
  · intro hunit
    have hnot :=
      (Submission.p06_9e0f5043ff_fno_fraction_isunit K F x hx q hq hqi v hv
        q 1 π hq1 (by simp [π])).mp hunit
    exact hnot (dvd_refl q)
  · intro y z hyz
    obtain ⟨a, b, hb, hy⟩ := (hv (y : F)).mp y.property
    obtain ⟨c, t, ht, hz⟩ := (hv (z : F)).mp z.property
    have hb0 : Polynomial.aeval x b ≠ 0 := by
      intro h
      have : b = 0 := hinj (by simpa only [map_zero] using h)
      exact hb (this.symm ▸ dvd_zero q)
    have ht0 : Polynomial.aeval x t ≠ 0 := by
      intro h
      have : t = 0 := hinj (by simpa only [map_zero] using h)
      exact ht (this.symm ▸ dvd_zero q)
    have hprod : Polynomial.aeval x q =
        (Polynomial.aeval x a / Polynomial.aeval x b) *
          (Polynomial.aeval x c / Polynomial.aeval x t) := by
      calc
        Polynomial.aeval x q = (π : F) := rfl
        _ = (y : F) * (z : F) :=
          congrArg (fun w : v.toValuationSubring => (w : F)) hyz
        _ = _ := by rw [hy, hz]
    have hac : a * c = q * (b * t) := by
      apply hinj
      rw [div_mul_div_comm, eq_div_iff (mul_ne_zero hb0 ht0)] at hprod
      simpa only [map_mul] using hprod.symm
    by_cases ha : q ∣ a
    · right
      apply (Submission.p06_9e0f5043ff_fno_fraction_isunit K F x hx q hq hqi v hv
        c t z ht hz).mpr
      intro hc
      obtain ⟨a₁, ha₁⟩ := ha
      obtain ⟨c₁, hc₁⟩ := hc
      have hcancel : q * (q * (a₁ * c₁)) = q * (b * t) := by
        calc
          q * (q * (a₁ * c₁)) = (q * a₁) * (q * c₁) := by ring
          _ = a * c := by rw [← ha₁, ← hc₁]
          _ = q * (b * t) := hac
      have hbt : q ∣ b * t :=
        ⟨a₁ * c₁, (mul_left_cancel₀ hqi.ne_zero hcancel).symm⟩
      exact (hqi.prime.dvd_or_dvd hbt).elim hb ht
    · left
      exact (Submission.p06_9e0f5043ff_fno_fraction_isunit K F x hx q hq hqi v hv
        a b y hb hy).mpr ha

end Submission

namespace Submission

set_option warningAsError true

theorem p06_9e0f5043ff_fpm_normalized_orders
    (K F : Type*) [Field K] [Field F] [Algebra K F] (x : F)
    (hx : Transcendental K x) (q : Polynomial K) (hq : q.Monic)
    (hqirr : Irreducible q) (v : AlgebraicCurve.Place K F)
    (hv : ∀ f : F, f ∈ v.toValuationSubring ↔
      ∃ a b : Polynomial K, ¬ q ∣ b ∧
        f = Polynomial.aeval x a / Polynomial.aeval x b) :
    v.ord (Polynomial.aeval x q) = 1 ∧
      (∀ a : Polynomial K, ¬ q ∣ a → v.ord (Polynomial.aeval x a) = 0) := by
  obtain ⟨π, hπ, hπirr⟩ :=
    Submission.p06_9e0f5043ff_fno_irreducible_aeval K F x hx q hq hqirr v hv
  constructor
  · simpa only [hπ] using v.ord_coe_irreducible hπirr
  · intro a ha
    have hqone : ¬ q ∣ (1 : Polynomial K) := hqirr.not_dvd_one
    have hamem : Polynomial.aeval x a ∈ v.toValuationSubring :=
      (hv _).mpr ⟨a, 1, hqone, by simp⟩
    let z : v.toValuationSubring := ⟨Polynomial.aeval x a, hamem⟩
    have hz : IsUnit z :=
      (Submission.p06_9e0f5043ff_fno_fraction_isunit K F x hx q hq hqirr v hv
        a 1 z hqone (by simp [z])).mpr ha
    simpa only [IsUnit.unit_spec] using v.ord_coe_unit hz.unit
/-- Polynomial evaluation at the finite place has residue kernel generated by `q`. -/
theorem p06_9e0f5043ff_fpm_rd_eval_kernel
    (K F : Type*) [Field K] [Field F] [Algebra K F] (x : F)
    (hx : Transcendental K x) (q : Polynomial K) (hq : Irreducible q)
    (v : AlgebraicCurve.Place K F)
    (hv : ∀ f : F, f ∈ v.toValuationSubring ↔
      ∃ a b : Polynomial K, ¬ q ∣ b ∧
        f = Polynomial.aeval x a / Polynomial.aeval x b) :
    ∃ e : Polynomial K →ₐ[K] v.toValuationSubring,
      (∀ a : Polynomial K, (e a : F) = Polynomial.aeval x a) ∧
      RingHom.ker ((IsLocalRing.residue v.toValuationSubring).comp e.toRingHom) =
        Ideal.span ({q} : Set (Polynomial K)) := by
  classical
  have hinj := transcendental_iff_injective.mp hx
  have hne (a : Polynomial K) (ha : a ≠ 0) : Polynomial.aeval x a ≠ 0 := by
    intro h
    exact ha (hinj (h.trans (map_zero (Polynomial.aeval x)).symm))
  -- Denominator 1 lifts every polynomial evaluation into the valuation ring.
  have hmem (a : Polynomial K) : Polynomial.aeval x a ∈ v.toValuationSubring :=
    (hv _).mpr ⟨a, 1, hq.not_dvd_one, by rw [map_one, div_one]⟩
  let e : Polynomial K →ₐ[K] v.toValuationSubring :=
    { toFun := fun a => ⟨Polynomial.aeval x a, hmem a⟩
      map_one' := Subtype.ext (map_one (Polynomial.aeval x))
      map_mul' := fun a b => Subtype.ext (map_mul (Polynomial.aeval x) a b)
      map_zero' := Subtype.ext (map_zero (Polynomial.aeval x))
      map_add' := fun a b => Subtype.ext (map_add (Polynomial.aeval x) a b)
      commutes' := fun c => Subtype.ext ((Polynomial.aeval x).commutes c) }
  have he (a : Polynomial K) : (e a : F) = Polynomial.aeval x a := rfl
  -- A polynomial not divisible by q has an inverse evaluation in the valuation ring.
  have hunit (a : Polynomial K) (ha : ¬ q ∣ a) : IsUnit (e a) := by
    have ha0 : Polynomial.aeval x a ≠ 0 := hne a (fun h => ha (h ▸ dvd_zero q))
    have hi : (Polynomial.aeval x a)⁻¹ ∈ v.toValuationSubring :=
      (hv _).mpr ⟨1, a, ha, by rw [map_one, one_div]⟩
    exact isUnit_iff_exists_inv.mpr
      ⟨⟨(Polynomial.aeval x a)⁻¹, hi⟩, Subtype.ext (mul_inv_cancel₀ ha0)⟩
  -- An inverse of q(x) would force q to divide an allowed denominator.
  have hq_nonunit : ¬ IsUnit (e q) := by
    intro hu
    obtain ⟨z, hz⟩ := isUnit_iff_exists_inv.mp hu
    have hmul : Polynomial.aeval x q * (z : F) = 1 :=
      congrArg (fun t : v.toValuationSubring => (t : F)) hz
    obtain ⟨a, b, hb, hzrep⟩ := (hv (z : F)).mp z.property
    have hb0 : Polynomial.aeval x b ≠ 0 := hne b (fun h => hb (h ▸ dvd_zero q))
    have hab : Polynomial.aeval x q * Polynomial.aeval x a = Polynomial.aeval x b := by
      calc
        Polynomial.aeval x q * Polynomial.aeval x a =
            (Polynomial.aeval x q * (z : F)) * Polynomial.aeval x b := by
          rw [hzrep, ← mul_div_assoc, div_mul_cancel₀ _ hb0]
        _ = Polynomial.aeval x b := by rw [hmul, one_mul]
    apply hb
    refine ⟨a, hinj ?_⟩
    rw [map_mul]
    exact hab.symm
  have hq_zero : IsLocalRing.residue v.toValuationSubring (e q) = 0 := by
    by_contra h
    exact hq_nonunit ((IsLocalRing.residue_ne_zero_iff_isUnit _).mp h)
  refine ⟨e, he, ?_⟩
  ext a
  rw [RingHom.mem_ker, Ideal.mem_span_singleton]
  change IsLocalRing.residue v.toValuationSubring (e a) = 0 ↔ q ∣ a
  constructor
  · intro ha
    by_contra hqa
    exact ((IsLocalRing.residue_ne_zero_iff_isUnit _).mpr (hunit a hqa)) ha
  · rintro ⟨b, rfl⟩
    rw [map_mul, map_mul, hq_zero, zero_mul]
theorem p06_9e0f5043ff_fpm_rd_residue_surjective
    (K F : Type*) [Field K] [Field F] [Algebra K F] (x : F)
    (hx : Transcendental K x) (q : Polynomial K) (hq : Irreducible q)
    (v : AlgebraicCurve.Place K F)
    (hrep : ∀ h : v.toValuationSubring, ∃ a b : Polynomial K,
      ¬ q ∣ b ∧ (h : F) = Polynomial.aeval x a / Polynomial.aeval x b)
    (e : Polynomial K →ₐ[K] v.toValuationSubring)
    (he : ∀ a : Polynomial K, (e a : F) = Polynomial.aeval x a)
    (heq : IsLocalRing.residue v.toValuationSubring (e q) = 0) :
    Function.Surjective ((IsLocalRing.residue v.toValuationSubring).comp e.toRingHom) := by
  let ρ := IsLocalRing.residue v.toValuationSubring
  let φ := ρ.comp e.toRingHom
  intro r
  obtain ⟨h, rfl⟩ := IsLocalRing.residue_surjective (R := v.toValuationSubring) r
  obtain ⟨a, b, hb, hab⟩ := hrep h
  have hb0 : b ≠ 0 := fun hb0 => hb (hb0 ▸ dvd_zero q)
  have heb0 : Polynomial.aeval x b ≠ 0 := by
    intro heb0
    apply hb0
    exact (transcendental_iff_injective.mp hx) (by simpa using heb0)
  obtain ⟨u, t, hut⟩ := hq.coprime_iff_not_dvd.mpr hb
  have htb : φ t * φ b = 1 := by
    have hφq : φ q = 0 := heq
    simpa only [map_add, map_mul, map_one, hφq, mul_zero, zero_add]
      using congrArg φ hut
  have hmul : h * e b = e a := by
    apply Subtype.ext
    change (h : F) * (e b : F) = (e a : F)
    rw [he, he, hab, div_mul_cancel₀ _ heb0]
  have hres : ρ h * φ b = φ a := by
    change ρ h * ρ (e b) = ρ (e a)
    simpa only [map_mul] using congrArg ρ hmul
  refine ⟨a * t, ?_⟩
  change φ (a * t) = ρ h
  calc
    φ (a * t) = φ a * φ t := map_mul φ a t
    _ = (ρ h * φ b) * φ t := by rw [hres]
    _ = ρ h := by rw [mul_assoc, mul_comm (φ b) (φ t), htb, mul_one]

end Submission


namespace Submission

theorem p06_9e0f5043ff_fpm_residue_degree
    (K F : Type*) [Field K] [Field F] [Algebra K F] (x : F)
    (hx : Transcendental K x) (q : Polynomial K) (_hq : q.Monic)
    (hqi : Irreducible q) (v : AlgebraicCurve.Place K F)
    (hv : ∀ f : F, f ∈ v.toValuationSubring ↔
      ∃ a b : Polynomial K, ¬ q ∣ b ∧
        f = Polynomial.aeval x a / Polynomial.aeval x b) :
    v.deg = q.natDegree := by
  obtain ⟨e, he, hker⟩ :=
    Submission.p06_9e0f5043ff_fpm_rd_eval_kernel K F x hx q hqi v hv
  have hqzero : IsLocalRing.residue v.toValuationSubring (e q) = 0 := by
    change q ∈ RingHom.ker ((IsLocalRing.residue v.toValuationSubring).comp e.toRingHom)
    rw [hker]
    exact Ideal.subset_span (Set.mem_singleton q)
  have hsurj := Submission.p06_9e0f5043ff_fpm_rd_residue_surjective
    K F x hx q hqi v (fun h => (hv (h : F)).mp h.property) e he hqzero
  let φ : Polynomial K →ₐ[K] v.ResidueField :=
    (IsScalarTower.toAlgHom K v.toValuationSubring v.ResidueField).comp e
  have hkerφ : RingHom.ker φ = Ideal.span ({q} : Set (Polynomial K)) := hker
  have hsurjφ : Function.Surjective φ := hsurj
  have hdim :=
    ((Ideal.quotientEquivAlgOfEq K hkerφ.symm).trans
      (Ideal.quotientKerAlgEquivOfSurjective (f := φ) hsurjφ)).toLinearEquiv.finrank_eq
  exact hdim.symm.trans finrank_quotient_span_eq_natDegree

/-- Assemble the finite place, its residue degree, and its normalized orders. -/
theorem p06_9e0f5043ff_rmp_finite_place_model
    (K F : Type*) [Field K] [Field F] [Algebra K F] (x : F)
    (hx : Transcendental K x)
    (hfrac : ∀ f : F, ∃ a b : Polynomial K,
      b ≠ 0 ∧ f = Polynomial.aeval x a / Polynomial.aeval x b)
    (q : Polynomial K) (hq : q.Monic) (hirr : Irreducible q) :
    ∃ v : AlgebraicCurve.Place K F,
      (∀ f : F, f ∈ v.toValuationSubring ↔ ∃ a b : Polynomial K,
        ¬ q ∣ b ∧ f = Polynomial.aeval x a / Polynomial.aeval x b) ∧
      v.deg = q.natDegree ∧
      v.ord (Polynomial.aeval x q) = 1 ∧
      (∀ a : Polynomial K, ¬ q ∣ a → v.ord (Polynomial.aeval x a) = 0) := by
  obtain ⟨v, hv⟩ :=
    Submission.p06_9e0f5043ff_fpm_exists_local_place K F x hx hfrac q hq hirr
  exact ⟨v, hv,
    Submission.p06_9e0f5043ff_fpm_residue_degree K F x hx q hq hirr v hv,
    Submission.p06_9e0f5043ff_fpm_normalized_orders K F x hx q hq hirr v hv⟩
set_option warningAsError true

namespace Submission

/-- A place containing the polynomial coordinate is the localization at a monic
irreducible polynomial. The frozen proof base supplies `Place.center_ne_bot`
for the nonzero prime center and `Place.toValuationSubring_eq_of_forall_mem`
for its localization in `Definitions.Def_AlgebraicCurve_PlacesOverDVR`. -/
theorem p06_9e0f5043ff_rmp_finite_place_classification
    (K : Type*) [Field K]
    (v : AlgebraicCurve.Place K (FractionRing (Polynomial K)))
    (hX : algebraMap (Polynomial K) (FractionRing (Polynomial K)) Polynomial.X ∈
      v.toValuationSubring) :
    ∃ q : Polynomial K, q.Monic ∧ Irreducible q ∧
      (∀ f : FractionRing (Polynomial K), f ∈ v.toValuationSubring ↔
        ∃ a b : Polynomial K, ¬ q ∣ b ∧
          f = algebraMap (Polynomial K) (FractionRing (Polynomial K)) a /
            algebraMap (Polynomial K) (FractionRing (Polynomial K)) b) := by
  classical
  -- Constants and the coordinate generate the polynomial ring.
  have hpoly : ∀ p : Polynomial K,
      algebraMap (Polynomial K) (FractionRing (Polynomial K)) p ∈
        v.toValuationSubring := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p r hp hr => simpa only [map_add] using add_mem hp hr
    | monomial n a =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow]
      apply mul_mem
      · rw [Polynomial.C_eq_algebraMap, ← IsScalarTower.algebraMap_apply]
        exact v.algebraMap_mem' a
      · exact pow_mem hX n
  -- Normalize the generator of the nonzero prime center.
  obtain ⟨q, hnorm, hspan⟩ := Ideal.exists_normalized_span_of_isPrincipal
    (AlgebraicCurve.Place.center (Polynomial K) v hpoly)
  have hq0 : q ≠ 0 := by
    intro hq
    apply v.center_ne_bot hpoly
    simpa only [hq, Ideal.span_singleton_zero] using hspan
  have hprime : (Ideal.span {q}).IsPrime := by
    rw [← hspan]
    infer_instance
  refine ⟨q, (Polynomial.normalize_eq_self_iff_monic hq0).mp hnorm,
    ((Ideal.span_singleton_prime hq0).mp hprime).irreducible, ?_⟩
  intro f
  -- The inherited localization theorem supplies both membership directions.
  -- Since the center is (q), its complement consists of denominators not divisible by q.
  rw [v.toValuationSubring_eq_of_forall_mem hpoly]
  change (∃ (a b : Polynomial K)
    (_ : b ∉ AlgebraicCurve.Place.center (Polynomial K) v hpoly),
      f = algebraMap (Polynomial K) (FractionRing (Polynomial K)) a *
        (algebraMap (Polynomial K) (FractionRing (Polynomial K)) b)⁻¹) ↔ _
  simp only [hspan, Ideal.mem_span_singleton, exists_prop, div_eq_mul_inv]

end Submission
/-- Clear the first row by an invertible column operation, preserving the trailing block.
The correction matrix squares to zero, so `1 - M` has the explicit inverse `1 + M`.
Divisibility supplies the coefficients without requiring the pivot to be nonzero or a unit. -/
theorem p06_9e0f5043ff_sdp_clear_first_row :
    ∀ (R : Type*) [CommRing R] (m : ℕ)
      (H : Matrix (Fin (m + 1)) (Fin (m + 1)) R),
      (∀ i : Fin m, H i.succ 0 = 0) →
      (∀ j : Fin m, H 0 0 ∣ H 0 j.succ) →
      ∃ V : Matrix (Fin (m + 1)) (Fin (m + 1)) R,
        IsUnit V ∧ H * V = Matrix.of (fun i j =>
          Fin.cases (Fin.cases (H 0 0) (fun _ => 0) j)
            (fun i' => Fin.cases 0 (fun j' => H i'.succ j'.succ) j) i) := by
  classical
  intro R _ m H hcol hdiv
  choose b hb using hdiv
  let M : Matrix (Fin (m + 1)) (Fin (m + 1)) R :=
    Matrix.of (fun i j => Fin.cases (Fin.cases 0 b j) (fun _ => 0) i)
  have hM0 (i : Fin (m + 1)) : M i 0 = 0 := by
    refine Fin.cases ?_ (fun _ => ?_) i <;> rfl
  have hMs (i : Fin m) (j : Fin (m + 1)) : M i.succ j = 0 := rfl
  have hMM : M * M = 0 := by
    ext i j
    simp [Matrix.mul_apply, Fin.sum_univ_succ, hM0, hMs]
  have hHM (i j : Fin (m + 1)) :
      (H * M) i j = H i 0 * Fin.cases 0 b j := by
    simp [Matrix.mul_apply, Fin.sum_univ_succ, M]
  refine ⟨1 - M, ?_, ?_⟩
  · refine ⟨⟨1 - M, 1 + M, ?_, ?_⟩, rfl⟩
    · simp [sub_mul, mul_add, hMM]
    · simp [mul_sub, add_mul, hMM]
  · rw [mul_sub, mul_one]
    ext i j
    refine Fin.cases ?_ (fun i' => ?_) i <;>
      refine Fin.cases ?_ (fun j' => ?_) j <;>
      simp [Matrix.sub_apply, hHM, hcol, hb]
/-- Clear the first column below a divisible pivot by a unit that preserves the first row. -/
theorem p06_9e0f5043ff_sdp_clear_first_column
    (R : Type*) [CommRing R] (m : ℕ)
    (B : Matrix (Fin (m + 1)) (Fin (m + 1)) R)
    (h : ∀ i : Fin m, B 0 0 ∣ B i.succ 0) :
    ∃ U : Matrix (Fin (m + 1)) (Fin (m + 1)) R,
      IsUnit U ∧ (∀ j : Fin (m + 1), (U * B) 0 j = B 0 j) ∧
        (∀ i : Fin m, (U * B) i.succ 0 = 0) := by
  classical
  choose a ha using h
  -- Extend the chosen coefficients by zero so the first row is unchanged.
  let c : Fin (m + 1) → R := Fin.cases 0 a
  let N : Matrix (Fin (m + 1)) (Fin (m + 1)) R :=
    Matrix.of fun i j => if j = 0 then c i else 0
  have hmul (M : Matrix (Fin (m + 1)) (Fin (m + 1)) R)
      (i j : Fin (m + 1)) : (N * M) i j = c i * M 0 j := by
    simp [Matrix.mul_apply, N]
  have hsq : N * N = 0 := by
    ext i j
    simp [hmul, N, c]
  -- Since N² = 0, the clearing matrix 1 - N has two-sided inverse 1 + N.
  refine ⟨1 - N, ?_, ?_, ?_⟩
  · refine ⟨⟨1 - N, 1 + N, ?_, ?_⟩, rfl⟩
    · simp [sub_mul, mul_add, hsq]
    · simp [mul_sub, add_mul, hsq]
  · intro j
    simp [sub_mul, hmul, c]
  · intro i
    simp [sub_mul, hmul, c, ha i, mul_comm]

end Submission

/-- The reciprocal of the fraction-ring variable is transcendental and presents every fraction. -/
theorem Submission.p06_9e0f5043ff_inf_reciprocal_presentation :
    ∀ (K : Type*) [Field K],
      Transcendental K
        ((algebraMap (Polynomial K) (FractionRing (Polynomial K)) Polynomial.X)⁻¹) ∧
      (∀ f : FractionRing (Polynomial K), ∃ a b : Polynomial K, b ≠ 0 ∧
        f = Polynomial.aeval
          ((algebraMap (Polynomial K) (FractionRing (Polynomial K)) Polynomial.X)⁻¹) a /
          Polynomial.aeval
          ((algebraMap (Polynomial K) (FractionRing (Polynomial K)) Polynomial.X)⁻¹) b) := by
  intro K _
  let t : FractionRing (Polynomial K) :=
    algebraMap (Polynomial K) (FractionRing (Polynomial K)) Polynomial.X
  have hinj := IsFractionRing.injective (Polynomial K) (FractionRing (Polynomial K))
  have ht : t ≠ 0 := by
    exact fun h => Polynomial.X_ne_zero (hinj (h.trans (map_zero _).symm))
  have heval (p : Polynomial K) :
      Polynomial.aeval t p = algebraMap (Polynomial K) (FractionRing (Polynomial K)) p := by
    simp [t, Polynomial.aeval_algebraMap_apply]
  have htrans : Transcendental K t :=
    (transcendental_algebraMap_iff hinj).mpr (Polynomial.transcendental_X K)
  have hs : Transcendental K t⁻¹ := by
    intro h
    exact htrans (IsAlgebraic.inv_iff.mp h)
  refine ⟨hs, ?_⟩
  intro f
  change ∃ a b : Polynomial K, b ≠ 0 ∧
    f = Polynomial.aeval t⁻¹ a / Polynomial.aeval t⁻¹ b
  by_cases hf : f = 0
  · exact ⟨0, 1, one_ne_zero, by simp [hf]⟩
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (Polynomial K) f
  have hb0 : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
  have hbr : b.reverse ≠ 0 := by simpa using hb0
  have hbev : Polynomial.aeval t⁻¹ b.reverse ≠ 0 := by
    exact fun h => hbr ((transcendental_iff_injective.mp hs) (by simpa using h))
  let : Invertible t := invertibleOfNonzero ht
  have hreverse (p : Polynomial K) :
      algebraMap (Polynomial K) (FractionRing (Polynomial K)) p =
        Polynomial.aeval t⁻¹ p.reverse / (t⁻¹) ^ p.natDegree := by
    have h := Polynomial.eval₂_reverse_mul_pow
      (algebraMap K (FractionRing (Polynomial K))) t p
    simpa only [invOf_eq_inv, ← Polynomial.aeval_def, heval, inv_pow,
      div_inv_eq_mul] using h.symm
  rw [← hab, hreverse a, hreverse b]
  by_cases hdeg : a.natDegree ≤ b.natDegree
  · refine ⟨Polynomial.X ^ (b.natDegree - a.natDegree) * a.reverse,
      b.reverse, hbr, ?_⟩
    rw [map_mul, map_pow, Polynomial.aeval_X, pow_sub₀ _ (inv_ne_zero ht) hdeg]
    field_simp
  · refine ⟨a.reverse, Polynomial.X ^ (a.natDegree - b.natDegree) * b.reverse,
      mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) hbr, ?_⟩
    rw [map_mul, map_pow, Polynomial.aeval_X,
      pow_sub₀ _ (inv_ne_zero ht) (Nat.le_of_lt (Nat.lt_of_not_ge hdeg))]
    field_simp
/-- Reciprocal evaluation has order minus the degree at the place above the origin. -/
theorem Submission.p06_9e0f5043ff_inf_reciprocal_polynomial_order :
    ∀ (K F : Type*) [Field K] [Field F] [Algebra K F] (s : F),
      Transcendental K s → ∀ v : AlgebraicCurve.Place K F, v.ord s = 1 →
      (∀ c : Polynomial K, ¬ (Polynomial.X : Polynomial K) ∣ c →
        v.ord (Polynomial.aeval s c) = 0) →
      ∀ a : Polynomial K, a ≠ 0 →
        v.ord (Polynomial.aeval s⁻¹ a) = -(a.natDegree : ℤ) := by
  intro K F _ _ _ s hs v hv hzero a ha
  have hs0 : s ≠ 0 := by
    intro h
    exact hs ⟨Polynomial.X, Polynomial.X_ne_zero, by simpa using h⟩
  have hrev : a.reverse ≠ 0 := fun h => ha (Polynomial.reverse_eq_zero.mp h)
  have heval : Polynomial.aeval s a.reverse ≠ 0 := fun h => hs ⟨a.reverse, hrev, h⟩
  have hnot : ¬ (Polynomial.X : Polynomial K) ∣ a.reverse := by
    simpa only [Polynomial.X_dvd_iff, Polynomial.coeff_zero_reverse,
      Polynomial.leadingCoeff_eq_zero] using ha
  have horder : v.ord (Polynomial.aeval s a.reverse) = 0 := hzero _ hnot
  -- Reversal writes reciprocal evaluation as a negative power times a unit at v.
  have hidentity : Polynomial.aeval s⁻¹ a =
      s ^ (-(a.natDegree : ℤ)) * Polynomial.aeval s a.reverse := by
    let : Invertible s⁻¹ := invertibleOfNonzero (inv_ne_zero hs0)
    simpa only [invOf_eq_inv, inv_inv, ← Polynomial.aeval_def, zpow_neg,
      zpow_natCast, inv_pow, mul_comm] using
      (Polynomial.eval₂_reverse_mul_pow (algebraMap K F) s⁻¹ a).symm
  rw [hidentity, v.ord_mul (zpow_ne_zero _ hs0) heval, v.ord_zpow, hv,
    horder, mul_one, add_zero]
/-- Polynomial evaluation at a nonunit of a place is a unit exactly away from `(X)`. -/
theorem Submission.p06_9e0f5043ff_vfc_polynomial_unit_criterion :
    ∀ (K F : Type*) [Field K] [Field F] [Algebra K F]
      (s : F) (w : AlgebraicCurve.Place K F),
      s⁻¹ ∉ w.toValuationSubring → ∀ p : Polynomial K,
        (∃ u : Units w.toValuationSubring,
          ((u : w.toValuationSubring) : F) = Polynomial.aeval s p) ↔
        ¬ (Polynomial.X : Polynomial K) ∣ p := by
  intro K F _ _ _ s w hinv p
  have hs : s ∈ w.toValuationSubring :=
    (w.toValuationSubring.mem_or_inv_mem s).resolve_right hinv
  let t : w.toValuationSubring := ⟨s, hs⟩
  have ht : ¬ IsUnit t := by
    rintro ⟨u, hu⟩
    have hmul : s * (((u⁻¹ : Units w.toValuationSubring) : w.toValuationSubring) : F) = 1 := by
      change (t : F) * _ = 1
      rw [← hu]
      exact congrArg (fun x : w.toValuationSubring => (x : F)) u.val_inv
    have hi : (((u⁻¹ : Units w.toValuationSubring) : w.toValuationSubring) : F) = s⁻¹ :=
      eq_inv_of_mul_eq_one_right hmul
    exact hinv (hi ▸ (u⁻¹).val.property)
  -- Evaluate inside the valuation subring using its inherited K-algebra structure.
  let E : Polynomial K →+* w.toValuationSubring := (Polynomial.aeval t).toRingHom
  have hE (q : Polynomial K) : (E q : F) = Polynomial.aeval s q := by
    exact (Polynomial.aeval_algHom_apply
      (IsScalarTower.toAlgHom K w.toValuationSubring F) t q).symm
  let J : Ideal (Polynomial K) := (IsLocalRing.maximalIdeal w.toValuationSubring).comap E
  have hJ : J ≠ ⊤ :=
    Ideal.comap_ne_top E (IsLocalRing.maximalIdeal.isMaximal w.toValuationSubring).ne_top
  have hX : (Polynomial.X : Polynomial K) ∈ J := by
    change E Polynomial.X ∈ IsLocalRing.maximalIdeal w.toValuationSubring
    change Polynomial.aeval t Polynomial.X ∈ IsLocalRing.maximalIdeal w.toValuationSubring
    rw [Polynomial.aeval_X, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact ht
  -- The proper contraction contains the maximal ideal (X), so they coincide.
  have hspan : Ideal.span ({Polynomial.X} : Set (Polynomial K)) = J :=
    (PrincipalIdealRing.isMaximal_of_irreducible Polynomial.irreducible_X).eq_of_le hJ
      (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hX))
  have hunit : IsUnit (E p) ↔ ¬ (Polynomial.X : Polynomial K) ∣ p := by
    rw [← IsLocalRing.notMem_maximalIdeal]
    change p ∉ J ↔ ¬ (Polynomial.X : Polynomial K) ∣ p
    rw [← hspan, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨u, hu⟩
    apply hunit.mp
    refine ⟨u, ?_⟩
    exact Subtype.ext (hu.trans (hE p).symm)
  · intro hp
    obtain ⟨u, hu⟩ := hunit.mpr hp
    exact ⟨u, (congrArg (fun x : w.toValuationSubring => (x : F)) hu).trans (hE p)⟩
/-- Membership of a unit times a parameter-power quotient forces nonnegative exponent. -/
theorem Submission.p06_9e0f5043ff_vfc_unit_power_quotient_exponents :
    ∀ (F : Type*) [Field F] (W : Subring F) (s : F), s ∈ W → s⁻¹ ∉ W →
      ∀ (u : Units W) (r k : ℕ), ((u : W) : F) * s ^ r / s ^ k ∈ W → k ≤ r := by
  intro F _ W s hs hsinv u r k hquot
  have hs0 : s ≠ 0 := by
    intro h
    apply hsinv
    simp [h]
  have hu : ((u : W) : F) * ((↑(u⁻¹) : W) : F) = 1 := by
    exact_mod_cast u.mul_inv
  by_contra hle
  let n := k - r - 1
  have hk : k = r + n + 1 := by
    dsimp [n]
    omega
  have hprod :
      (((u : W) : F) * s ^ r / s ^ k) * ((↑(u⁻¹) : W) : F) * s ^ n ∈ W :=
    W.mul_mem (W.mul_mem hquot (↑(u⁻¹) : W).property) (W.pow_mem hs n)
  have heq :
      (((u : W) : F) * s ^ r / s ^ k) * ((↑(u⁻¹) : W) : F) * s ^ n = s⁻¹ := by
    calc
      _ = (((u : W) : F) * ((↑(u⁻¹) : W) : F)) * (s ^ r * s ^ n) / s ^ k := by
        ring
      _ = s ^ (r + n) / s ^ (r + n + 1) := by
        rw [hu, one_mul, ← pow_add, hk]
      _ = s⁻¹ := by
        rw [pow_succ, div_mul_eq_div_div, div_self (pow_ne_zero _ hs0), one_div]
  exact hsinv (heq ▸ hprod)


namespace Submission
/-- The valuation ring in which the parameter is a nonunit consists exactly of
fractions whose denominator is not divisible by `X`. -/
theorem p06_9e0f5043ff_inf_valuation_fraction_characterization :
    ∀ (K F : Type*) [Field K] [Field F] [Algebra K F] (s : F),
      Transcendental K s →
      (∀ f : F, ∃ a b : Polynomial K, b ≠ 0 ∧
        f = Polynomial.aeval s a / Polynomial.aeval s b) →
      ∀ w : AlgebraicCurve.Place K F, s⁻¹ ∉ w.toValuationSubring →
      ∀ f : F, f ∈ w.toValuationSubring ↔
        ∃ a b : Polynomial K, ¬ (Polynomial.X : Polynomial K) ∣ b ∧
          f = Polynomial.aeval s a / Polynomial.aeval s b := by
  intro K F _ _ _ s hs hfrac w hsinv f
  classical
  let W : Subring F := w.toValuationSubring.toSubring
  have hsW : s ∈ W := (w.toValuationSubring.mem_or_inv_mem s).resolve_right hsinv
  have hs0 : s ≠ 0 := by
    intro h
    apply hsinv
    simp [h]
  have heval_mem (p : Polynomial K) : Polynomial.aeval s p ∈ W := by
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simpa only [map_add] using W.add_mem hp hq
    | monomial n a =>
      rw [Polynomial.aeval_monomial]
      exact W.mul_mem (w.algebraMap_mem' a) (W.pow_mem hsW n)
  have hunit_inv (u : Units W) :
      (((u⁻¹ : Units W) : W) : F) = (((u : W) : F))⁻¹ := by
    exact (Units.map W.subtype.toMonoidHom u).val_inv_eq_inv_val
  have heval_ne (p : Polynomial K) (hp : p ≠ 0) : Polynomial.aeval s p ≠ 0 := by
    intro h
    apply hp
    exact (transcendental_iff_injective.mp hs) (h.trans (map_zero _).symm)
  constructor
  · intro hf
    by_cases hf0 : f = 0
    · exact ⟨0, 1, by simp [Polynomial.X_dvd_iff], by simp [hf0]⟩
    obtain ⟨a, b, hb, hfab⟩ := hfrac f
    have ha : a ≠ 0 := by
      intro h
      apply hf0
      simpa [h] using hfab
    -- Remove all factors of X, leaving polynomials that evaluate to units.
    obtain ⟨a₀, ha_factor, ha₀⟩ :=
      Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd a ha 0
    obtain ⟨b₀, hb_factor, hb₀⟩ :=
      Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd b hb 0
    simp only [map_zero, sub_zero] at ha_factor ha₀ hb_factor hb₀
    obtain ⟨ua, hua⟩ :=
      (p06_9e0f5043ff_vfc_polynomial_unit_criterion K F s w hsinv a₀).mpr ha₀
    obtain ⟨ub, hub⟩ :=
      (p06_9e0f5043ff_vfc_polynomial_unit_criterion K F s w hsinv b₀).mpr hb₀
    let r := a.rootMultiplicity 0
    let k := b.rootMultiplicity 0
    let u : Units W := ua * ub⁻¹
    have hu : ((u : W) : F) = Polynomial.aeval s a₀ / Polynomial.aeval s b₀ := by
      change ((ua : W) : F) * (((ub⁻¹ : Units W) : W) : F) = _
      rw [hunit_inv, hua, hub, div_eq_mul_inv]
    have hnormalized : f = ((u : W) : F) * s ^ r / s ^ k := by
      rw [hfab, ha_factor, hb_factor, hu]
      simp only [map_mul, map_pow, Polynomial.aeval_X]
      dsimp only [r, k]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    -- Membership rules out a negative exponent of the nonunit parameter.
    have hkr : k ≤ r :=
      p06_9e0f5043ff_vfc_unit_power_quotient_exponents F W s hsW hsinv u r k
        (hnormalized ▸ hf)
    refine ⟨Polynomial.X ^ (r - k) * a₀, b₀, hb₀, ?_⟩
    have hb₀_ne : Polynomial.aeval s b₀ ≠ 0 :=
      heval_ne b₀ (fun h => hb₀ (by simp [h]))
    have hpow : s ^ r = s ^ (r - k) * s ^ k := by
      rw [← pow_add, Nat.sub_add_cancel hkr]
    rw [hnormalized, hu]
    simp only [map_mul, map_pow, Polynomial.aeval_X]
    rw [hpow]
    field_simp [hs0, hb₀_ne]
  · rintro ⟨a, b, hb, rfl⟩
    obtain ⟨u, hu⟩ :=
      (p06_9e0f5043ff_vfc_polynomial_unit_criterion K F s w hsinv b).mpr hb
    have hinv : (Polynomial.aeval s b)⁻¹ ∈ W := by
      rw [← hu, ← hunit_inv]
      exact ((u⁻¹ : Units W) : W).property
    change Polynomial.aeval s a / Polynomial.aeval s b ∈ W
    rw [div_eq_mul_inv]
    exact W.mul_mem (heval_mem a) hinv
/-- Fractions with denominators not divisible by an irreducible polynomial form a subalgebra. -/
theorem p06_9e0f5043ff_elp_fraction_subalgebra
    (K F : Type*) [Field K] [Field F] [Algebra K F] (x : F)
    (hx : Transcendental K x) (q : Polynomial K) (_hq : q.Monic)
    (hq : Irreducible q) :
    ∃ A : Subalgebra K F, ∀ f : F, f ∈ A ↔
      ∃ a b : Polynomial K, ¬ q ∣ b ∧
        f = Polynomial.aeval x a / Polynomial.aeval x b := by
  -- Irreducibility in K[T] gives the denominator product property from the accepted proof.
  have hprime : Prime q := hq.prime
  -- A permitted denominator cannot evaluate to zero at a transcendental element.
  have hden : ∀ b : Polynomial K, ¬ q ∣ b → Polynomial.aeval x b ≠ 0 := by
    intro b hb heval
    have hb0 : b = 0 := transcendental_iff.mp hx b heval
    exact hb (hb0 ▸ dvd_zero q)
  -- Subalgebra obtains negation closure by multiplying by the included constant -1.
  refine ⟨{
    carrier := {f | ∃ a b : Polynomial K, ¬ q ∣ b ∧
      f = Polynomial.aeval x a / Polynomial.aeval x b}
    algebraMap_mem' := by
      -- Constants use denominator one; Subalgebra derives zero and one membership.
      intro c
      exact ⟨Polynomial.C c, 1, hprime.not_dvd_one, by
        simp only [Polynomial.aeval_C, map_one, div_one]⟩
    add_mem' := by
      rintro _ _ ⟨a, b, hb, rfl⟩ ⟨c, d, hd, rfl⟩
      refine ⟨a * d + b * c, b * d, hprime.not_dvd_mul hb hd, ?_⟩
      simpa only [map_add, map_mul] using
        div_add_div (Polynomial.aeval x a) (Polynomial.aeval x c) (hden b hb) (hden d hd)
    mul_mem' := by
      rintro _ _ ⟨a, b, hb, rfl⟩ ⟨c, d, hd, rfl⟩
      refine ⟨a * c, b * d, hprime.not_dvd_mul hb hd, ?_⟩
      simp only [map_mul, div_mul_div_comm]
  }, fun _ => Iff.rfl⟩
/-- The exponent of an irreducible polynomial, realized by the pinned library's `multiplicity`.
The monicity hypothesis is retained from the frozen contract; irreducibility suffices for the proof. -/
theorem p06_9e0f5043ff_io_polynomial_exponent :
    ∀ (K : Type*) [Field K] (q : Polynomial K), q.Monic → Irreducible q →
      ∃ μ : Polynomial K → ℕ, μ 1 = 0 ∧ μ q = 1 ∧
        (∀ a b : Polynomial K, a ≠ 0 → b ≠ 0 → μ (a * b) = μ a + μ b) ∧
        (∀ a : Polynomial K, a ≠ 0 → (μ a = 0 ↔ ¬ q ∣ a)) ∧
        (∀ a : Polynomial K, a ≠ 0 → ∃ a₀ : Polynomial K,
          a₀ ≠ 0 ∧ ¬ q ∣ a₀ ∧ a = q ^ μ a * a₀) := by
  intro K _ q _ hq
  -- The library's degree-based well-founded divisibility supplies finite power extraction.
  have hfin (a : Polynomial K) (ha : a ≠ 0) : FiniteMultiplicity q a :=
    FiniteMultiplicity.of_not_isUnit hq.not_isUnit ha
  -- The frozen contract leaves μ 0 unconstrained, so the library's default value is admissible.
  refine ⟨multiplicity q, multiplicity_of_one_right hq.not_isUnit,
    multiplicity_self, ?_, ?_, ?_⟩
  · intro a b ha hb
    exact multiplicity_mul hq.prime (hfin (a * b) (mul_ne_zero ha hb))
  · intro a _
    exact multiplicity_eq_zero
  · intro a ha
    obtain ⟨a₀, hfactor, hfree⟩ := (hfin a ha).exists_eq_pow_mul_and_not_dvd
    exact ⟨a₀, right_ne_zero_of_mul (hfactor ▸ ha), hfree, hfactor⟩

end Submission

namespace Submission

/-- Extend an additive exponent on nonzero polynomials to integer orders on a field
represented by fractions of their evaluations at a transcendental element. -/
theorem p06_9e0f5043ff_io_fraction_extension :
    ∀ (K F : Type*) [Field K] [Field F] [Algebra K F] (x : F),
      Transcendental K x →
      (∀ f : F, ∃ a b : Polynomial K, b ≠ 0 ∧
        f = Polynomial.aeval x a / Polynomial.aeval x b) →
      ∀ μ : Polynomial K → ℕ,
        (∀ a b : Polynomial K, a ≠ 0 → b ≠ 0 → μ (a * b) = μ a + μ b) →
        ∃ ν : F → ℤ, ν 0 = 0 ∧
          (∀ a b : Polynomial K, a ≠ 0 → b ≠ 0 →
            ν (Polynomial.aeval x a / Polynomial.aeval x b) =
              (μ a : ℤ) - (μ b : ℤ)) ∧
          (∀ f g : F, f ≠ 0 → g ≠ 0 → ν (f / g) = ν f - ν g) := by
  intro K F _ _ _ x hx hrepr μ hμ
  classical
  let e := Polynomial.aeval (R := K) x
  have hinj : Function.Injective e := transcendental_iff_injective.mp hx
  have hne (a : Polynomial K) (ha : a ≠ 0) : e a ≠ 0 := by
    intro h
    exact ha (hinj (h.trans (map_zero e).symm))
  choose a b hb hab using hrepr
  have ha (f : F) (hf : f ≠ 0) : a f ≠ 0 := by
    intro h
    apply hf
    simpa [h] using hab f
  -- Equal nonzero fractions have the same integer difference.
  have hwell (p q r s : Polynomial K) (hp : p ≠ 0) (hq : q ≠ 0)
      (hr : r ≠ 0) (hs : s ≠ 0) (h : e p / e q = e r / e s) :
      (μ p : ℤ) - (μ q : ℤ) = (μ r : ℤ) - (μ s : ℤ) := by
    have hcross : p * s = r * q := by
      apply hinj
      simpa only [map_mul] using (div_eq_div_iff (hne q hq) (hne s hs)).mp h
    have hsum := congrArg μ hcross
    rw [hμ p s hp hs, hμ r q hr hq] at hsum
    omega
  -- The exponent at the zero polynomial is unrestricted, so define the value at zero separately.
  let ν : F → ℤ := fun f => if f = 0 then 0 else (μ (a f) : ℤ) - (μ (b f) : ℤ)
  have hformula (p q : Polynomial K) (hp : p ≠ 0) (hq : q ≠ 0) :
      ν (e p / e q) = (μ p : ℤ) - (μ q : ℤ) := by
    have hf : e p / e q ≠ 0 := div_ne_zero (hne p hp) (hne q hq)
    dsimp only [ν]
    rw [if_neg hf]
    exact hwell _ _ p q (ha _ hf) (hb _) hp hq (hab _).symm
  refine ⟨ν, ?_, hformula, ?_⟩
  · simp [ν]
  · intro f g hf hg
    have hquot : f / g = e (a f * b g) / e (b f * a g) := by
      calc
        f / g = (e (a f) / e (b f)) / (e (a g) / e (b g)) :=
          congrArg₂ (fun u v : F => u / v) (hab f) (hab g)
        _ = e (a f * b g) / e (b f * a g) := by
          simp only [map_mul, div_div_div_eq]
    rw [hquot, hformula _ _ (mul_ne_zero (ha f hf) (hb g))
      (mul_ne_zero (hb f) (ha g hg)), hμ _ _ (ha f hf) (hb g),
      hμ _ _ (hb f) (ha g hg)]
    simp only [ν, if_neg hf, if_neg hg, Nat.cast_add]
    ring

end Submission

namespace Submission

theorem p06_9e0f5043ff_elp_integer_order :
    ∀ (K F : Type*) [Field K] [Field F] [Algebra K F] (x : F),
      Transcendental K x →
      (∀ f : F, ∃ a b : Polynomial K,
        b ≠ 0 ∧ f = Polynomial.aeval x a / Polynomial.aeval x b) →
      ∀ q : Polynomial K, q.Monic → Irreducible q →
      ∃ ν : F → ℤ, ν 0 = 0 ∧ ν (Polynomial.aeval x q) = 1 ∧
        (∀ f g : F, f ≠ 0 → g ≠ 0 → ν (f / g) = ν f - ν g) ∧
        (∀ f : F, f ≠ 0 → (0 ≤ ν f ↔
          ∃ a b : Polynomial K, ¬ q ∣ b ∧
            f = Polynomial.aeval x a / Polynomial.aeval x b)) := by
  intro K F _ _ _ x hx hrepr q hqmonic hq
  obtain ⟨μ, hμone, hμq, hμmul, hμzero, hμfactor⟩ :=
    Submission.p06_9e0f5043ff_io_polynomial_exponent K q hqmonic hq
  obtain ⟨ν, hνzero, hνfraction, hνdiv⟩ :=
    Submission.p06_9e0f5043ff_io_fraction_extension K F x hx hrepr μ hμmul
  have hinj : Function.Injective (Polynomial.aeval x : Polynomial K →ₐ[K] F) :=
    transcendental_iff_injective.mp hx
  have heval_ne : ∀ a : Polynomial K, a ≠ 0 → Polynomial.aeval x a ≠ 0 := by
    intro a ha h
    apply ha
    apply hinj
    simpa only [map_zero] using h
  refine ⟨ν, hνzero, ?_, hνdiv, ?_⟩
  · simpa only [map_one, div_one, hμq, hμone, Nat.cast_one, Nat.cast_zero, sub_zero]
      using hνfraction q 1 hq.ne_zero one_ne_zero
  · intro f hf
    constructor
    · intro hnonneg
      obtain ⟨a, b, hb, hrep⟩ := hrepr f
      have ha : a ≠ 0 := by
        intro ha
        apply hf
        rw [hrep, ha, map_zero, zero_div]
      have horder : 0 ≤ (μ a : ℤ) - (μ b : ℤ) := by
        rwa [hrep, hνfraction a b ha hb] at hnonneg
      have hba : μ b ≤ μ a := by
        exact_mod_cast sub_nonneg.mp horder
      obtain ⟨a₀, _, _, hafactor⟩ := hμfactor a ha
      obtain ⟨b₀, _, hqb₀, hbfactor⟩ := hμfactor b hb
      refine ⟨q ^ (μ a - μ b) * a₀, b₀, hqb₀, ?_⟩
      calc
        f = Polynomial.aeval x a / Polynomial.aeval x b := hrep
        _ = Polynomial.aeval x (q ^ μ a * a₀) /
            Polynomial.aeval x (q ^ μ b * b₀) :=
          congrArg₂ (fun r s : Polynomial K =>
            Polynomial.aeval x r / Polynomial.aeval x s) hafactor hbfactor
        _ = Polynomial.aeval x (q ^ (μ a - μ b) * a₀) /
            Polynomial.aeval x b₀ := by
          simp only [map_mul, map_pow]
          rw [← pow_mul_pow_sub (Polynomial.aeval x q) hba, mul_assoc,
            mul_div_mul_left _ _ (pow_ne_zero _ (heval_ne q hq.ne_zero))]
    · rintro ⟨a, b, hqb, hrep⟩
      have hb : b ≠ 0 := by
        rintro rfl
        exact hqb (dvd_zero q)
      have ha : a ≠ 0 := by
        intro ha
        apply hf
        rw [hrep, ha, map_zero, zero_div]
      rw [hrep, hνfraction a b ha hb, (hμzero b hb).2 hqb, Nat.cast_zero, sub_zero]
      exact Nat.cast_nonneg _
/-- An integer order characterizing subring membership makes every ideal principal. -/
theorem p06_9e0f5043ff_elp_principal_ideals_of_order :
    ∀ (F : Type*) [Field F] (A : Subring F) (ν : F → ℤ),
      (∀ f g : F, f ≠ 0 → g ≠ 0 → ν (f / g) = ν f - ν g) →
      (∀ f : F, f ≠ 0 → (f ∈ A ↔ 0 ≤ ν f)) → IsPrincipalIdealRing A := by
  intro F _ A ν hdiv hmem
  classical
  constructor
  intro I
  by_cases hI : I = ⊥
  · subst I
    infer_instance
  obtain ⟨z, hzI, hz⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  -- Minimize natural orders; subring membership will recover their integer values.
  have hex : ∃ n : ℕ, ∃ h : A, h ∈ I ∧ (h : F) ≠ 0 ∧ (ν (h : F)).toNat = n :=
    ⟨_, z, hzI, fun h => hz (Subtype.ext h), rfl⟩
  obtain ⟨h, hhI, hh, hν⟩ := Nat.find_spec hex
  refine ⟨⟨h, le_antisymm ?_ ((Ideal.span_singleton_le_iff_mem I).mpr hhI)⟩⟩
  intro z hzI
  by_cases hz : (z : F) = 0
  · have hz' : z = 0 := Subtype.ext hz
    rw [hz']
    exact Ideal.zero_mem _
  have hh_nonneg : 0 ≤ ν (h : F) := (hmem _ hh).mp h.property
  have hz_nonneg : 0 ≤ ν (z : F) := (hmem _ hz).mp z.property
  have hmin : (ν (h : F)).toNat ≤ (ν (z : F)).toNat := by
    rw [hν]
    exact Nat.find_min' hex ⟨z, hzI, hz, rfl⟩
  have horder : ν (h : F) ≤ ν (z : F) := by
    simpa only [Int.toNat_of_nonneg hh_nonneg, Int.toNat_of_nonneg hz_nonneg] using
      (Int.ofNat_le.mpr hmin)
  -- Leastness makes the quotient an element of A, giving the required multiple of h.
  have hquot : (z : F) / (h : F) ∈ A := by
    apply (hmem _ (div_ne_zero hz hh)).mpr
    rw [hdiv _ _ hz hh]
    exact sub_nonneg.mpr horder
  apply Ideal.mem_span_singleton'.mpr
  refine ⟨⟨(z : F) / (h : F), hquot⟩, ?_⟩
  apply Subtype.ext
  exact div_mul_cancel₀ _ hh

end Submission

namespace Submission

/-- The finite place whose ring consists of fractions with denominator prime to `q`. -/
theorem p06_9e0f5043ff_fpm_exists_local_place
    (K F : Type*) [Field K] [Field F] [Algebra K F] (x : F)
    (hx : Transcendental K x)
    (hF : ∀ f : F, ∃ a b : Polynomial K, b ≠ 0 ∧
      f = Polynomial.aeval x a / Polynomial.aeval x b)
    (q : Polynomial K) (hqmonic : q.Monic) (hq : Irreducible q) :
    ∃ v : AlgebraicCurve.Place K F, ∀ f : F,
      f ∈ v.toValuationSubring ↔ ∃ a b : Polynomial K,
        ¬ q ∣ b ∧ f = Polynomial.aeval x a / Polynomial.aeval x b := by
  obtain ⟨A, hA⟩ := p06_9e0f5043ff_elp_fraction_subalgebra K F x hx q hqmonic hq
  obtain ⟨ν, hνzero, hνq, hνdiv, hνmem⟩ :=
    p06_9e0f5043ff_elp_integer_order K F x hx hF q hqmonic hq
  have hmem (f : F) (hf : f ≠ 0) : f ∈ A ↔ 0 ≤ ν f :=
    (hA f).trans (hνmem f hf).symm
  have hνone : ν 1 = 0 := by
    simpa only [div_self (one_ne_zero : (1 : F) ≠ 0), sub_self] using
      hνdiv 1 1 one_ne_zero one_ne_zero
  have hνinv (f : F) (hf : f ≠ 0) : ν f⁻¹ = -ν f := by
    simpa only [one_div, hνone, zero_sub] using hνdiv 1 f one_ne_zero hf
  -- The sign of the order gives the valuation-subring alternative.
  let V : ValuationSubring F :=
    { A.toSubring with
      mem_or_inv_mem' := by
        intro f
        change f ∈ A ∨ f⁻¹ ∈ A
        by_cases hf : f = 0
        · exact Or.inl (hf ▸ A.zero_mem)
        · by_cases hnonneg : 0 ≤ ν f
          · exact Or.inl ((hmem f hf).mpr hnonneg)
          · apply Or.inr
            apply (hmem f⁻¹ (inv_ne_zero hf)).mpr
            rw [hνinv f hf]
            omega }
  -- The inverse of q(x) has order -1, so this valuation subring is proper.
  have hqx : Polynomial.aeval x q ≠ 0 := by
    intro hzero
    rw [hzero, hνzero] at hνq
    omega
  have hVproper : V ≠ ⊤ := by
    intro htop
    have hin : (Polynomial.aeval x q)⁻¹ ∈ V := by
      rw [htop]
      exact ValuationSubring.mem_top _
    have hnonneg := (hmem _ (inv_ne_zero hqx)).mp hin
    rw [hνinv _ hqx, hνq] at hnonneg
    omega
  refine ⟨{
    toValuationSubring := V
    algebraMap_mem' := A.algebraMap_mem
    ne_top' := hVproper
    isPrincipalIdealRing' :=
      p06_9e0f5043ff_elp_principal_ideals_of_order F A.toSubring ν hνdiv hmem
  }, ?_⟩
  exact hA
namespace Submission

set_option warningAsError true

/-- In the given polynomial-fraction model of a place, a fraction is a unit exactly when
its numerator is not divisible by the defining irreducible polynomial. -/
theorem p06_9e0f5043ff_fno_fraction_isunit
    (K F : Type*) [Field K] [Field F] [Algebra K F] (x : F)
    (hx : Transcendental K x) (q : Polynomial K) (_hqmonic : q.Monic)
    (hq : Irreducible q) (v : AlgebraicCurve.Place K F)
    (hmem : ∀ f : F, f ∈ v.toValuationSubring ↔
      ∃ a b : Polynomial K, ¬ q ∣ b ∧
        f = Polynomial.aeval x a / Polynomial.aeval x b)
    (a b : Polynomial K) (z : v.toValuationSubring) (hb : ¬ q ∣ b)
    (hz : (z : F) = Polynomial.aeval x a / Polynomial.aeval x b) :
    IsUnit z ↔ ¬ q ∣ a := by
  -- Transcendence lets us recover polynomial identities from identities in F.
  have hinj : Function.Injective (Polynomial.aeval x : Polynomial K →ₐ[K] F) :=
    transcendental_iff_injective.mp hx
  have hnonzero : ∀ p : Polynomial K, ¬ q ∣ p → Polynomial.aeval x p ≠ 0 := by
    intro p hp he
    have hpzero : p = 0 := hinj (by simpa only [map_zero] using he)
    exact hp (hpzero ▸ dvd_zero q)
  have hbzero := hnonzero b hb
  constructor
  · intro hu hqa
    -- Represent a unit's inverse, clear denominators, and use primality of q.
    obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.mp hu
    obtain ⟨c, d, hd, hwd⟩ := (hmem (w : F)).mp w.property
    have hprod : Polynomial.aeval x a * Polynomial.aeval x c =
        Polynomial.aeval x b * Polynomial.aeval x d := by
      have heq : (z : F) * (w : F) = 1 :=
        congrArg (fun t : v.toValuationSubring => (t : F)) hw
      rw [hz, hwd, div_mul_div_comm] at heq
      exact (div_eq_one_iff_eq (mul_ne_zero hbzero (hnonzero d hd))).mp heq
    have hpoly : a * c = b * d := hinj (by simpa only [map_mul] using hprod)
    have hdiv : q ∣ b * d := hpoly ▸ dvd_mul_of_dvd_left hqa c
    exact (hq.prime.dvd_or_dvd hdiv).elim hb hd
  · intro ha
    -- The reversed fraction belongs to the valuation subring and is an inverse.
    have hwmem : Polynomial.aeval x b / Polynomial.aeval x a ∈ v.toValuationSubring :=
      (hmem _).mpr ⟨b, a, ha, rfl⟩
    apply isUnit_iff_exists_inv.mpr
    refine ⟨⟨_, hwmem⟩, ?_⟩
    apply Subtype.ext
    change (z : F) * (Polynomial.aeval x b / Polynomial.aeval x a) = 1
    rw [hz, div_mul_div_comm, mul_comm (Polynomial.aeval x b) (Polynomial.aeval x a)]
    exact div_self (mul_ne_zero (hnonzero a ha) hbzero)

end Submission


namespace Submission

set_option warningAsError true

theorem p06_9e0f5043ff_fno_irreducible_aeval
    (K F : Type*) [Field K] [Field F] [Algebra K F] (x : F)
    (hx : Transcendental K x) (q : Polynomial K) (hq : q.Monic)
    (hqi : Irreducible q) (v : AlgebraicCurve.Place K F)
    (hv : ∀ f : F, f ∈ v.toValuationSubring ↔
      ∃ a b : Polynomial K, ¬ q ∣ b ∧
        f = Polynomial.aeval x a / Polynomial.aeval x b) :
    ∃ π : v.toValuationSubring, (π : F) = Polynomial.aeval x q ∧ Irreducible π := by
  classical
  have hinj : Function.Injective (Polynomial.aeval x : Polynomial K →ₐ[K] F) :=
    transcendental_iff_injective.mp hx
  have hq1 : ¬ q ∣ (1 : Polynomial K) := hqi.not_dvd_one
  let π : v.toValuationSubring :=
    ⟨Polynomial.aeval x q, (hv _).mpr ⟨q, 1, hq1, by simp⟩⟩
  refine ⟨π, rfl, ?_⟩
  constructor
  · intro hunit
    have hnot :=
      (Submission.p06_9e0f5043ff_fno_fraction_isunit K F x hx q hq hqi v hv
        q 1 π hq1 (by simp [π])).mp hunit
    exact hnot (dvd_refl q)
  · intro y z hyz
    obtain ⟨a, b, hb, hy⟩ := (hv (y : F)).mp y.property
    obtain ⟨c, t, ht, hz⟩ := (hv (z : F)).mp z.property
    have hb0 : Polynomial.aeval x b ≠ 0 := by
      intro h
      have : b = 0 := hinj (by simpa only [map_zero] using h)
      exact hb (this.symm ▸ dvd_zero q)
    have ht0 : Polynomial.aeval x t ≠ 0 := by
      intro h
      have : t = 0 := hinj (by simpa only [map_zero] using h)
      exact ht (this.symm ▸ dvd_zero q)
    have hprod : Polynomial.aeval x q =
        (Polynomial.aeval x a / Polynomial.aeval x b) *
          (Polynomial.aeval x c / Polynomial.aeval x t) := by
      calc
        Polynomial.aeval x q = (π : F) := rfl
        _ = (y : F) * (z : F) :=
          congrArg (fun w : v.toValuationSubring => (w : F)) hyz
        _ = _ := by rw [hy, hz]
    have hac : a * c = q * (b * t) := by
      apply hinj
      rw [div_mul_div_comm, eq_div_iff (mul_ne_zero hb0 ht0)] at hprod
      simpa only [map_mul] using hprod.symm
    by_cases ha : q ∣ a
    · right
      apply (Submission.p06_9e0f5043ff_fno_fraction_isunit K F x hx q hq hqi v hv
        c t z ht hz).mpr
      intro hc
      obtain ⟨a₁, ha₁⟩ := ha
      obtain ⟨c₁, hc₁⟩ := hc
      have hcancel : q * (q * (a₁ * c₁)) = q * (b * t) := by
        calc
          q * (q * (a₁ * c₁)) = (q * a₁) * (q * c₁) := by ring
          _ = a * c := by rw [← ha₁, ← hc₁]
          _ = q * (b * t) := hac
      have hbt : q ∣ b * t :=
        ⟨a₁ * c₁, (mul_left_cancel₀ hqi.ne_zero hcancel).symm⟩
      exact (hqi.prime.dvd_or_dvd hbt).elim hb ht
    · left
      exact (Submission.p06_9e0f5043ff_fno_fraction_isunit K F x hx q hq hqi v hv
        a b y hb hy).mpr ha

end Submission

namespace Submission

set_option warningAsError true

theorem p06_9e0f5043ff_fpm_normalized_orders
    (K F : Type*) [Field K] [Field F] [Algebra K F] (x : F)
    (hx : Transcendental K x) (q : Polynomial K) (hq : q.Monic)
    (hqirr : Irreducible q) (v : AlgebraicCurve.Place K F)
    (hv : ∀ f : F, f ∈ v.toValuationSubring ↔
      ∃ a b : Polynomial K, ¬ q ∣ b ∧
        f = Polynomial.aeval x a / Polynomial.aeval x b) :
    v.ord (Polynomial.aeval x q) = 1 ∧
      (∀ a : Polynomial K, ¬ q ∣ a → v.ord (Polynomial.aeval x a) = 0) := by
  obtain ⟨π, hπ, hπirr⟩ :=
    Submission.p06_9e0f5043ff_fno_irreducible_aeval K F x hx q hq hqirr v hv
  constructor
  · simpa only [hπ] using v.ord_coe_irreducible hπirr
  · intro a ha
    have hqone : ¬ q ∣ (1 : Polynomial K) := hqirr.not_dvd_one
    have hamem : Polynomial.aeval x a ∈ v.toValuationSubring :=
      (hv _).mpr ⟨a, 1, hqone, by simp⟩
    let z : v.toValuationSubring := ⟨Polynomial.aeval x a, hamem⟩
    have hz : IsUnit z :=
      (Submission.p06_9e0f5043ff_fno_fraction_isunit K F x hx q hq hqirr v hv
        a 1 z hqone (by simp [z])).mpr ha
    simpa only [IsUnit.unit_spec] using v.ord_coe_unit hz.unit
/-- Polynomial evaluation at the finite place has residue kernel generated by `q`. -/
theorem p06_9e0f5043ff_fpm_rd_eval_kernel
    (K F : Type*) [Field K] [Field F] [Algebra K F] (x : F)
    (hx : Transcendental K x) (q : Polynomial K) (hq : Irreducible q)
    (v : AlgebraicCurve.Place K F)
    (hv : ∀ f : F, f ∈ v.toValuationSubring ↔
      ∃ a b : Polynomial K, ¬ q ∣ b ∧
        f = Polynomial.aeval x a / Polynomial.aeval x b) :
    ∃ e : Polynomial K →ₐ[K] v.toValuationSubring,
      (∀ a : Polynomial K, (e a : F) = Polynomial.aeval x a) ∧
      RingHom.ker ((IsLocalRing.residue v.toValuationSubring).comp e.toRingHom) =
        Ideal.span ({q} : Set (Polynomial K)) := by
  classical
  have hinj := transcendental_iff_injective.mp hx
  have hne (a : Polynomial K) (ha : a ≠ 0) : Polynomial.aeval x a ≠ 0 := by
    intro h
    exact ha (hinj (h.trans (map_zero (Polynomial.aeval x)).symm))
  -- Denominator 1 lifts every polynomial evaluation into the valuation ring.
  have hmem (a : Polynomial K) : Polynomial.aeval x a ∈ v.toValuationSubring :=
    (hv _).mpr ⟨a, 1, hq.not_dvd_one, by rw [map_one, div_one]⟩
  let e : Polynomial K →ₐ[K] v.toValuationSubring :=
    { toFun := fun a => ⟨Polynomial.aeval x a, hmem a⟩
      map_one' := Subtype.ext (map_one (Polynomial.aeval x))
      map_mul' := fun a b => Subtype.ext (map_mul (Polynomial.aeval x) a b)
      map_zero' := Subtype.ext (map_zero (Polynomial.aeval x))
      map_add' := fun a b => Subtype.ext (map_add (Polynomial.aeval x) a b)
      commutes' := fun c => Subtype.ext ((Polynomial.aeval x).commutes c) }
  have he (a : Polynomial K) : (e a : F) = Polynomial.aeval x a := rfl
  -- A polynomial not divisible by q has an inverse evaluation in the valuation ring.
  have hunit (a : Polynomial K) (ha : ¬ q ∣ a) : IsUnit (e a) := by
    have ha0 : Polynomial.aeval x a ≠ 0 := hne a (fun h => ha (h ▸ dvd_zero q))
    have hi : (Polynomial.aeval x a)⁻¹ ∈ v.toValuationSubring :=
      (hv _).mpr ⟨1, a, ha, by rw [map_one, one_div]⟩
    exact isUnit_iff_exists_inv.mpr
      ⟨⟨(Polynomial.aeval x a)⁻¹, hi⟩, Subtype.ext (mul_inv_cancel₀ ha0)⟩
  -- An inverse of q(x) would force q to divide an allowed denominator.
  have hq_nonunit : ¬ IsUnit (e q) := by
    intro hu
    obtain ⟨z, hz⟩ := isUnit_iff_exists_inv.mp hu
    have hmul : Polynomial.aeval x q * (z : F) = 1 :=
      congrArg (fun t : v.toValuationSubring => (t : F)) hz
    obtain ⟨a, b, hb, hzrep⟩ := (hv (z : F)).mp z.property
    have hb0 : Polynomial.aeval x b ≠ 0 := hne b (fun h => hb (h ▸ dvd_zero q))
    have hab : Polynomial.aeval x q * Polynomial.aeval x a = Polynomial.aeval x b := by
      calc
        Polynomial.aeval x q * Polynomial.aeval x a =
            (Polynomial.aeval x q * (z : F)) * Polynomial.aeval x b := by
          rw [hzrep, ← mul_div_assoc, div_mul_cancel₀ _ hb0]
        _ = Polynomial.aeval x b := by rw [hmul, one_mul]
    apply hb
    refine ⟨a, hinj ?_⟩
    rw [map_mul]
    exact hab.symm
  have hq_zero : IsLocalRing.residue v.toValuationSubring (e q) = 0 := by
    by_contra h
    exact hq_nonunit ((IsLocalRing.residue_ne_zero_iff_isUnit _).mp h)
  refine ⟨e, he, ?_⟩
  ext a
  rw [RingHom.mem_ker, Ideal.mem_span_singleton]
  change IsLocalRing.residue v.toValuationSubring (e a) = 0 ↔ q ∣ a
  constructor
  · intro ha
    by_contra hqa
    exact ((IsLocalRing.residue_ne_zero_iff_isUnit _).mpr (hunit a hqa)) ha
  · rintro ⟨b, rfl⟩
    rw [map_mul, map_mul, hq_zero, zero_mul]

end Submission
