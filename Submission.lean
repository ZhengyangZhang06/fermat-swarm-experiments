/-
Copyright 2026 Anthropic, PBC. Licensed under Apache-2.0; see LICENSE.
Source: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_AlgebraicCurve_hasPrincipalDivisors_of_transcendental.lean
Modified: replaced the proof with sorry and removed P2M proof imports.
Requires the upstream Definitions modules and their dependencies.
-/

import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Mathlib.RingTheory.Length
attribute [-instance] AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy
attribute [-simp] AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul
attribute [-simp] AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply

open AlgebraicCurve
theorem AlgebraicCurve.hasPrincipalDivisors_of_transcendental (K : Type*) [Field K] [CharZero K] {F : Type*} [Field F]
    [Algebra K F] (x : F) (hx : Transcendental K x)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F] : HasPrincipalDivisors K F := by
  sorry

namespace Submission

/-- Compute the length over `A` by summing the residue factors of a composition series over `B`.
The sum is in `ℕ∞`, so the factors need not have finite length over `A`. -/
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

open AlgebraicCurve
theorem AlgebraicCurve.hasPrincipalDivisors_of_transcendental (K : Type*) [Field K] [CharZero K] {F : Type*} [Field F]
    [Algebra K F] (x : F) (hx : Transcendental K x)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F] : HasPrincipalDivisors K F := by
  sorry

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

end Submission
