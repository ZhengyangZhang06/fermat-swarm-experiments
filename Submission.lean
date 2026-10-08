import Definitions.Def_AlgebraicCurve_PlacesOverDVR

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
