/-
Copyright 2026 Anthropic, PBC. Licensed under Apache-2.0; see LICENSE.
Source: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_AlgebraicCurve_hasPrincipalDivisors_of_transcendental.lean
Modified: implements the selected local length-order node in namespace Submission.
Requires the upstream Definitions modules and their dependencies.
-/

import Definitions.Def_AlgebraicCurve_PlacesOverDVR

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
  -- combines Module.length_quotient with coheight_pow_maximalIdeal, counting
  -- the uniformizer-power filtration from the accepted proof, also when m = 0.
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
