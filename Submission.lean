/-
Copyright 2026 Anthropic, PBC. Licensed under Apache-2.0; see LICENSE.
Source: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_AlgebraicCurve_hasPrincipalDivisors_of_transcendental.lean
Modified: replaced the proof with sorry and removed P2M proof imports.
Requires the upstream Definitions modules and their dependencies.
-/

import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.Localization.Module
import Mathlib.Algebra.Module.LocalizedModule.Exact
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
open scoped BigOperators

/-- Length after localization is the sum of the localized successive quotient lengths. -/
theorem p06_9e0f5043ff_llm_localized_series_sum
    (B M : Type*) [CommRing B] [AddCommGroup M] [Module B M]
    (T : Submonoid B) (s : CompositionSeries (Submodule B M))
    (hhead : s.head = ⊥) (hlast : s.last = ⊤) :
    Module.length (Localization T) (LocalizedModule T M) =
      Finset.sum Finset.univ (fun i : Fin s.length =>
        Module.length (Localization T)
          (LocalizedModule T (↥(s i.succ) ⧸ (s i.castSucc).comap (s i.succ).subtype))) := by
  classical
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
    exact Module.length_eq_add_of_exact (LocalizedModule.map T f) (LocalizedModule.map T g)
      (LocalizedModule.map_injective T f (Submodule.inclusion_injective hle))
      (LocalizedModule.map_surjective T g (Submodule.mkQ_surjective _))
      (LocalizedModule.map_exact T f g hex)
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

end Submission
