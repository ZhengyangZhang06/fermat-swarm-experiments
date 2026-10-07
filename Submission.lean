import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity

namespace Submission

theorem p06_9e0f5043ff_io_polynomial_exponent :
    ∀ (K : Type*) [Field K] (q : Polynomial K), q.Monic → Irreducible q →
      ∃ μ : Polynomial K → ℕ, μ 1 = 0 ∧ μ q = 1 ∧
        (∀ a b : Polynomial K, a ≠ 0 → b ≠ 0 → μ (a * b) = μ a + μ b) ∧
        (∀ a : Polynomial K, a ≠ 0 → (μ a = 0 ↔ ¬ q ∣ a)) ∧
        (∀ a : Polynomial K, a ≠ 0 → ∃ a₀ : Polynomial K,
          a₀ ≠ 0 ∧ ¬ q ∣ a₀ ∧ a = q ^ μ a * a₀) := by
  intro K _ q _ hq
  have hfin (a : Polynomial K) (ha : a ≠ 0) : FiniteMultiplicity q a :=
    FiniteMultiplicity.of_not_isUnit hq.not_isUnit ha
  refine ⟨multiplicity q, multiplicity_of_one_right hq.not_isUnit,
    multiplicity_self, ?_, ?_, ?_⟩
  · intro a b ha hb
    exact multiplicity_mul hq.prime (hfin (a * b) (mul_ne_zero ha hb))
  · intro a _
    exact multiplicity_eq_zero
  · intro a ha
    obtain ⟨a₀, hfactor, hfree⟩ := (hfin a ha).exists_eq_pow_mul_and_not_dvd
    refine ⟨a₀, ?_, hfree, hfactor⟩
    intro hzero
    apply ha
    simpa [hzero] using hfactor

end Submission
