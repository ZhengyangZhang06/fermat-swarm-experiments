import Definitions.Def_AlgebraicCurve_PlacesOverDVR

namespace Submission

/-- Monic equations for a nonzero element and its inverse over the restricted valuation ring
make the element a unit upstairs, so its order is zero. -/
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
  have hmem : f ∈ w.toValuationSubring := by
    apply w.mem_of_eval_monic_eq_zero (P := P.map (algebraMap E L)) (hP.map _)
    · intro i
      rw [Polynomial.coeff_map]
      exact w.mem_restrict_iff.mp (hPcoeff i)
    · simpa only [Polynomial.eval_map] using hPf
  have hinv : f⁻¹ ∈ w.toValuationSubring := by
    apply w.mem_of_eval_monic_eq_zero (P := Q.map (algebraMap E L)) (hQ.map _)
    · intro i
      rw [Polynomial.coeff_map]
      exact w.mem_restrict_iff.mp (hQcoeff i)
    · simpa only [Polynomial.eval_map] using hQf
  let u : w.toValuationSubringˣ :=
    { val := ⟨f, hmem⟩
      inv := ⟨f⁻¹, hinv⟩
      val_inv := Subtype.ext (mul_inv_cancel₀ hf)
      inv_val := Subtype.ext (inv_mul_cancel₀ hf) }
  exact w.ord_coe_unit u

end Submission
