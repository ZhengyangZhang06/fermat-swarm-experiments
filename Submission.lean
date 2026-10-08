import Mathlib.RingTheory.Algebraic.Basic

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
  refine ⟨{
    carrier := {f | ∃ a b : Polynomial K, ¬ q ∣ b ∧
      f = Polynomial.aeval x a / Polynomial.aeval x b}
    algebraMap_mem' := by
      -- Constants use denominator one; Subalgebra derives zero and one membership.
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

end Submission
