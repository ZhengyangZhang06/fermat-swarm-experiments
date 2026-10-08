/-
Copyright 2026 Anthropic, PBC. Licensed under Apache-2.0; see LICENSE.
Source: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_AlgebraicCurve_hasPrincipalDivisors_of_transcendental.lean
Modified: implements the selected fraction-unit criterion in namespace Submission.
Requires the upstream Definitions modules and their dependencies.
-/

import Definitions.Def_AlgebraicCurve_PlacesOverDVR

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

end Submission

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

namespace Submission

theorem p06_9e0f5043ff_elp_integer_order :
    ∀ (K F : Type*) [Field K] [Field F] [Algebra K F] (x : F),
      Transcendental K x →
      (∀ f : F, ∃ a b : Polynomial K,
        b ≠ 0 ∧ f = Polynomial.aeval x a / Polynomial.aeval x b) →
      ∀ q : Polynomial K, q.Monic → Irreducible q →
      ∃ ν : F → ℤ, ν 0 = 0 ∧ ν (Polynomial.aeval x q) = 1 ∧
        (∀ f g : F, f ≠ 0 → g ≠ 0 → ν (f / g) = ν f - ν g) ∧
        (∀ f : F, f ≠ 0 → (0 ≤ ν f ↔
          ∃ a b : Polynomial K, ¬ q ∣ b ∧
            f = Polynomial.aeval x a / Polynomial.aeval x b)) := by
  intro K F _ _ _ x hx hrepr q hqmonic hq
  obtain ⟨μ, hμone, hμq, hμmul, hμzero, hμfactor⟩ :=
    Submission.p06_9e0f5043ff_io_polynomial_exponent K q hqmonic hq
  obtain ⟨ν, hνzero, hνfraction, hνdiv⟩ :=
    Submission.p06_9e0f5043ff_io_fraction_extension K F x hx hrepr μ hμmul
  have hinj : Function.Injective (Polynomial.aeval x : Polynomial K →ₐ[K] F) :=
    transcendental_iff_injective.mp hx
  have heval_ne : ∀ a : Polynomial K, a ≠ 0 → Polynomial.aeval x a ≠ 0 := by
    intro a ha h
    apply ha
    apply hinj
    simpa only [map_zero] using h
  refine ⟨ν, hνzero, ?_, hνdiv, ?_⟩
  · simpa only [map_one, div_one, hμq, hμone, Nat.cast_one, Nat.cast_zero, sub_zero]
      using hνfraction q 1 hq.ne_zero one_ne_zero
  · intro f hf
    constructor
    · intro hnonneg
      obtain ⟨a, b, hb, hrep⟩ := hrepr f
      have ha : a ≠ 0 := by
        intro ha
        apply hf
        rw [hrep, ha, map_zero, zero_div]
      have horder : 0 ≤ (μ a : ℤ) - (μ b : ℤ) := by
        rwa [hrep, hνfraction a b ha hb] at hnonneg
      have hba : μ b ≤ μ a := by
        exact_mod_cast sub_nonneg.mp horder
      obtain ⟨a₀, _, _, hafactor⟩ := hμfactor a ha
      obtain ⟨b₀, _, hqb₀, hbfactor⟩ := hμfactor b hb
      refine ⟨q ^ (μ a - μ b) * a₀, b₀, hqb₀, ?_⟩
      calc
        f = Polynomial.aeval x a / Polynomial.aeval x b := hrep
        _ = Polynomial.aeval x (q ^ μ a * a₀) /
            Polynomial.aeval x (q ^ μ b * b₀) :=
          congrArg₂ (fun r s : Polynomial K =>
            Polynomial.aeval x r / Polynomial.aeval x s) hafactor hbfactor
        _ = Polynomial.aeval x (q ^ (μ a - μ b) * a₀) /
            Polynomial.aeval x b₀ := by
          simp only [map_mul, map_pow]
          rw [← pow_mul_pow_sub (Polynomial.aeval x q) hba, mul_assoc,
            mul_div_mul_left _ _ (pow_ne_zero _ (heval_ne q hq.ne_zero))]
    · rintro ⟨a, b, hqb, hrep⟩
      have hb : b ≠ 0 := by
        rintro rfl
        exact hqb (dvd_zero q)
      have ha : a ≠ 0 := by
        intro ha
        apply hf
        rw [hrep, ha, map_zero, zero_div]
      rw [hrep, hνfraction a b ha hb, (hμzero b hb).2 hqb, Nat.cast_zero, sub_zero]
      exact Nat.cast_nonneg _
/-- An integer order characterizing subring membership makes every ideal principal. -/
theorem p06_9e0f5043ff_elp_principal_ideals_of_order :
    ∀ (F : Type*) [Field F] (A : Subring F) (ν : F → ℤ),
      (∀ f g : F, f ≠ 0 → g ≠ 0 → ν (f / g) = ν f - ν g) →
      (∀ f : F, f ≠ 0 → (f ∈ A ↔ 0 ≤ ν f)) → IsPrincipalIdealRing A := by
  intro F _ A ν hdiv hmem
  classical
  constructor
  intro I
  by_cases hI : I = ⊥
  · subst I
    infer_instance
  obtain ⟨z, hzI, hz⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  -- Minimize natural orders; subring membership will recover their integer values.
  have hex : ∃ n : ℕ, ∃ h : A, h ∈ I ∧ (h : F) ≠ 0 ∧ (ν (h : F)).toNat = n :=
    ⟨_, z, hzI, fun h => hz (Subtype.ext h), rfl⟩
  obtain ⟨h, hhI, hh, hν⟩ := Nat.find_spec hex
  refine ⟨⟨h, le_antisymm ?_ ((Ideal.span_singleton_le_iff_mem I).mpr hhI)⟩⟩
  intro z hzI
  by_cases hz : (z : F) = 0
  · have hz' : z = 0 := Subtype.ext hz
    rw [hz']
    exact Ideal.zero_mem _
  have hh_nonneg : 0 ≤ ν (h : F) := (hmem _ hh).mp h.property
  have hz_nonneg : 0 ≤ ν (z : F) := (hmem _ hz).mp z.property
  have hmin : (ν (h : F)).toNat ≤ (ν (z : F)).toNat := by
    rw [hν]
    exact Nat.find_min' hex ⟨z, hzI, hz, rfl⟩
  have horder : ν (h : F) ≤ ν (z : F) := by
    simpa only [Int.toNat_of_nonneg hh_nonneg, Int.toNat_of_nonneg hz_nonneg] using
      (Int.ofNat_le.mpr hmin)
  -- Leastness makes the quotient an element of A, giving the required multiple of h.
  have hquot : (z : F) / (h : F) ∈ A := by
    apply (hmem _ (div_ne_zero hz hh)).mpr
    rw [hdiv _ _ hz hh]
    exact sub_nonneg.mpr horder
  apply Ideal.mem_span_singleton'.mpr
  refine ⟨⟨(z : F) / (h : F), hquot⟩, ?_⟩
  apply Subtype.ext
  exact div_mul_cancel₀ _ hh

end Submission

namespace Submission

/-- The finite place whose ring consists of fractions with denominator prime to `q`. -/
theorem p06_9e0f5043ff_fpm_exists_local_place
    (K F : Type*) [Field K] [Field F] [Algebra K F] (x : F)
    (hx : Transcendental K x)
    (hF : ∀ f : F, ∃ a b : Polynomial K, b ≠ 0 ∧
      f = Polynomial.aeval x a / Polynomial.aeval x b)
    (q : Polynomial K) (hqmonic : q.Monic) (hq : Irreducible q) :
    ∃ v : AlgebraicCurve.Place K F, ∀ f : F,
      f ∈ v.toValuationSubring ↔ ∃ a b : Polynomial K,
        ¬ q ∣ b ∧ f = Polynomial.aeval x a / Polynomial.aeval x b := by
  obtain ⟨A, hA⟩ := p06_9e0f5043ff_elp_fraction_subalgebra K F x hx q hqmonic hq
  obtain ⟨ν, hνzero, hνq, hνdiv, hνmem⟩ :=
    p06_9e0f5043ff_elp_integer_order K F x hx hF q hqmonic hq
  have hmem (f : F) (hf : f ≠ 0) : f ∈ A ↔ 0 ≤ ν f :=
    (hA f).trans (hνmem f hf).symm
  have hνone : ν 1 = 0 := by
    simpa only [div_self (one_ne_zero : (1 : F) ≠ 0), sub_self] using
      hνdiv 1 1 one_ne_zero one_ne_zero
  have hνinv (f : F) (hf : f ≠ 0) : ν f⁻¹ = -ν f := by
    simpa only [one_div, hνone, zero_sub] using hνdiv 1 f one_ne_zero hf
  -- The sign of the order gives the valuation-subring alternative.
  let V : ValuationSubring F :=
    { A.toSubring with
      mem_or_inv_mem' := by
        intro f
        change f ∈ A ∨ f⁻¹ ∈ A
        by_cases hf : f = 0
        · exact Or.inl (hf ▸ A.zero_mem)
        · by_cases hnonneg : 0 ≤ ν f
          · exact Or.inl ((hmem f hf).mpr hnonneg)
          · apply Or.inr
            apply (hmem f⁻¹ (inv_ne_zero hf)).mpr
            rw [hνinv f hf]
            omega }
  -- The inverse of q(x) has order -1, so this valuation subring is proper.
  have hqx : Polynomial.aeval x q ≠ 0 := by
    intro hzero
    rw [hzero, hνzero] at hνq
    omega
  have hVproper : V ≠ ⊤ := by
    intro htop
    have hin : (Polynomial.aeval x q)⁻¹ ∈ V := by
      rw [htop]
      exact ValuationSubring.mem_top _
    have hnonneg := (hmem _ (inv_ne_zero hqx)).mp hin
    rw [hνinv _ hqx, hνq] at hnonneg
    omega
  refine ⟨{
    toValuationSubring := V
    algebraMap_mem' := A.algebraMap_mem
    ne_top' := hVproper
    isPrincipalIdealRing' :=
      p06_9e0f5043ff_elp_principal_ideals_of_order F A.toSubring ν hνdiv hmem
  }, ?_⟩
  exact hA
namespace Submission

set_option warningAsError true

/-- In the given polynomial-fraction model of a place, a fraction is a unit exactly when
its numerator is not divisible by the defining irreducible polynomial. -/
namespace Submission

set_option warningAsError true

/-- In the given polynomial-fraction model of a place, a fraction is a unit exactly when
its numerator is not divisible by the defining irreducible polynomial. -/
theorem p06_9e0f5043ff_fno_fraction_isunit
    (K F : Type*) [Field K] [Field F] [Algebra K F] (x : F)
    (hx : Transcendental K x) (q : Polynomial K) (_hqmonic : q.Monic)
    (hq : Irreducible q) (v : AlgebraicCurve.Place K F)
    (hmem : ∀ f : F, f ∈ v.toValuationSubring ↔
      ∃ a b : Polynomial K, ¬ q ∣ b ∧
        f = Polynomial.aeval x a / Polynomial.aeval x b)
    (a b : Polynomial K) (z : v.toValuationSubring) (hb : ¬ q ∣ b)
    (hz : (z : F) = Polynomial.aeval x a / Polynomial.aeval x b) :
    IsUnit z ↔ ¬ q ∣ a := by
  -- Transcendence lets us recover polynomial identities from identities in F.
  have hinj : Function.Injective (Polynomial.aeval x : Polynomial K →ₐ[K] F) :=
    transcendental_iff_injective.mp hx
  have hnonzero : ∀ p : Polynomial K, ¬ q ∣ p → Polynomial.aeval x p ≠ 0 := by
    intro p hp he
    have hpzero : p = 0 := hinj (by simpa only [map_zero] using he)
    exact hp (hpzero ▸ dvd_zero q)
  have hbzero := hnonzero b hb
  constructor
  · intro hu hqa
    -- Represent a unit's inverse, clear denominators, and use primality of q.
    obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.mp hu
    obtain ⟨c, d, hd, hwd⟩ := (hmem (w : F)).mp w.property
    have hprod : Polynomial.aeval x a * Polynomial.aeval x c =
        Polynomial.aeval x b * Polynomial.aeval x d := by
      have heq : (z : F) * (w : F) = 1 :=
        congrArg (fun t : v.toValuationSubring => (t : F)) hw
      rw [hz, hwd, div_mul_div_comm] at heq
      exact (div_eq_one_iff_eq (mul_ne_zero hbzero (hnonzero d hd))).mp heq
    have hpoly : a * c = b * d := hinj (by simpa only [map_mul] using hprod)
    have hdiv : q ∣ b * d := hpoly ▸ dvd_mul_of_dvd_left hqa c
    exact (hq.prime.dvd_or_dvd hdiv).elim hb hd
  · intro ha
    -- The reversed fraction belongs to the valuation subring and is an inverse.
    have hwmem : Polynomial.aeval x b / Polynomial.aeval x a ∈ v.toValuationSubring :=
      (hmem _).mpr ⟨b, a, ha, rfl⟩
    apply isUnit_iff_exists_inv.mpr
    refine ⟨⟨_, hwmem⟩, ?_⟩
    apply Subtype.ext
    change (z : F) * (Polynomial.aeval x b / Polynomial.aeval x a) = 1
    rw [hz, div_mul_div_comm, mul_comm (Polynomial.aeval x b) (Polynomial.aeval x a)]
    exact div_self (mul_ne_zero (hnonzero a ha) hbzero)

end Submission
