import Definitions.Def_AlgebraicCurve_PlacesOverDVR

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
  refine ⟨multiplicity q, multiplicity_of_one_right hq.not_isUnit,
    multiplicity_self, ?_, ?_, ?_⟩
  · intro a b ha hb
    exact multiplicity_mul hq.prime (hfin (a * b) (mul_ne_zero ha hb))
  · intro a _
    exact multiplicity_eq_zero
  · intro a ha
    obtain ⟨a₀, hfactor, hfree⟩ := (hfin a ha).exists_eq_pow_mul_and_not_dvd
    exact ⟨a₀, right_ne_zero_of_mul (hfactor ▸ ha), hfree, hfactor⟩
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
