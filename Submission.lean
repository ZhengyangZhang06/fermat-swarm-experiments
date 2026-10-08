import Definitions.Def_AlgebraicCurve_PlacesOverDVR

open AlgebraicCurve
theorem AlgebraicCurve.hasPrincipalDivisors_of_transcendental (K : Type*) [Field K] [CharZero K] {F : Type*} [Field F]
    [Algebra K F] (x : F) (hx : Transcendental K x)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F] : HasPrincipalDivisors K F := by
  sorry

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
      rw [Polynomial.coeff_map]
      exact w.mem_restrict_iff.mp (hcoeff i)
    · simpa only [Polynomial.eval_map] using hx
  exact w.ord_coe_unit
    { val := ⟨f, mem_of_root P f hP hPcoeff hPf⟩
      inv := ⟨f⁻¹, mem_of_root Q f⁻¹ hQ hQcoeff hQf⟩
      val_inv := Subtype.ext (mul_inv_cancel₀ hf)
      inv_val := Subtype.ext (inv_mul_cancel₀ hf) }

end Submission
