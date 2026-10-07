import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity

namespace Submission

open AlgebraicCurve
theorem AlgebraicCurve.hasPrincipalDivisors_of_transcendental (K : Type*) [Field K] [CharZero K] {F : Type*} [Field F]
    [Algebra K F] (x : F) (hx : Transcendental K x)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F] : HasPrincipalDivisors K F := by
  sorry

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
    exact ⟨a₀, right_ne_zero_of_mul (hfactor ▸ ha), hfree, hfactor⟩

end Submission
