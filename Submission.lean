import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity

namespace Submission

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

end Submission

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


namespace Submission

set_option warningAsError true

theorem p06_9e0f5043ff_fno_irreducible_aeval
    (K F : Type*) [Field K] [Field F] [Algebra K F] (x : F)
    (hx : Transcendental K x) (q : Polynomial K) (hq : q.Monic)
    (hqi : Irreducible q) (v : AlgebraicCurve.Place K F)
    (hv : ∀ f : F, f ∈ v.toValuationSubring ↔
      ∃ a b : Polynomial K, ¬ q ∣ b ∧
        f = Polynomial.aeval x a / Polynomial.aeval x b) :
    ∃ π : v.toValuationSubring, (π : F) = Polynomial.aeval x q ∧ Irreducible π := by
  classical
  have hinj : Function.Injective (Polynomial.aeval x : Polynomial K →ₐ[K] F) :=
    transcendental_iff_injective.mp hx
  have hq1 : ¬ q ∣ (1 : Polynomial K) := hqi.not_dvd_one
  let π : v.toValuationSubring :=
    ⟨Polynomial.aeval x q, (hv _).mpr ⟨q, 1, hq1, by simp⟩⟩
  refine ⟨π, rfl, ?_⟩
  constructor
  · intro hunit
    have hnot :=
      (Submission.p06_9e0f5043ff_fno_fraction_isunit K F x hx q hq hqi v hv
        q 1 π hq1 (by simp [π])).mp hunit
    exact hnot (dvd_refl q)
  · intro y z hyz
    obtain ⟨a, b, hb, hy⟩ := (hv (y : F)).mp y.property
    obtain ⟨c, t, ht, hz⟩ := (hv (z : F)).mp z.property
    have hb0 : Polynomial.aeval x b ≠ 0 := by
      intro h
      have : b = 0 := hinj (by simpa only [map_zero] using h)
      exact hb (this.symm ▸ dvd_zero q)
    have ht0 : Polynomial.aeval x t ≠ 0 := by
      intro h
      have : t = 0 := hinj (by simpa only [map_zero] using h)
      exact ht (this.symm ▸ dvd_zero q)
    have hprod : Polynomial.aeval x q =
        (Polynomial.aeval x a / Polynomial.aeval x b) *
          (Polynomial.aeval x c / Polynomial.aeval x t) := by
      calc
        Polynomial.aeval x q = (π : F) := rfl
        _ = (y : F) * (z : F) :=
          congrArg (fun w : v.toValuationSubring => (w : F)) hyz
        _ = _ := by rw [hy, hz]
    have hac : a * c = q * (b * t) := by
      apply hinj
      rw [div_mul_div_comm, eq_div_iff (mul_ne_zero hb0 ht0)] at hprod
      simpa only [map_mul] using hprod.symm
    by_cases ha : q ∣ a
    · right
      apply (Submission.p06_9e0f5043ff_fno_fraction_isunit K F x hx q hq hqi v hv
        c t z ht hz).mpr
      intro hc
      obtain ⟨a₁, ha₁⟩ := ha
      obtain ⟨c₁, hc₁⟩ := hc
      have hcancel : q * (q * (a₁ * c₁)) = q * (b * t) := by
        calc
          q * (q * (a₁ * c₁)) = (q * a₁) * (q * c₁) := by ring
          _ = a * c := by rw [← ha₁, ← hc₁]
          _ = q * (b * t) := hac
      have hbt : q ∣ b * t :=
        ⟨a₁ * c₁, (mul_left_cancel₀ hqi.ne_zero hcancel).symm⟩
      exact (hqi.prime.dvd_or_dvd hbt).elim hb ht
    · left
      exact (Submission.p06_9e0f5043ff_fno_fraction_isunit K F x hx q hq hqi v hv
        a b y hb hy).mpr ha

end Submission

namespace Submission

set_option warningAsError true

theorem p06_9e0f5043ff_fpm_normalized_orders
    (K F : Type*) [Field K] [Field F] [Algebra K F] (x : F)
    (hx : Transcendental K x) (q : Polynomial K) (hq : q.Monic)
    (hqirr : Irreducible q) (v : AlgebraicCurve.Place K F)
    (hv : ∀ f : F, f ∈ v.toValuationSubring ↔
      ∃ a b : Polynomial K, ¬ q ∣ b ∧
        f = Polynomial.aeval x a / Polynomial.aeval x b) :
    v.ord (Polynomial.aeval x q) = 1 ∧
      (∀ a : Polynomial K, ¬ q ∣ a → v.ord (Polynomial.aeval x a) = 0) := by
  obtain ⟨π, hπ, hπirr⟩ :=
    Submission.p06_9e0f5043ff_fno_irreducible_aeval K F x hx q hq hqirr v hv
  constructor
  · simpa only [hπ] using v.ord_coe_irreducible hπirr
  · intro a ha
    have hqone : ¬ q ∣ (1 : Polynomial K) := hqirr.not_dvd_one
    have hamem : Polynomial.aeval x a ∈ v.toValuationSubring :=
      (hv _).mpr ⟨a, 1, hqone, by simp⟩
    let z : v.toValuationSubring := ⟨Polynomial.aeval x a, hamem⟩
    have hz : IsUnit z :=
      (Submission.p06_9e0f5043ff_fno_fraction_isunit K F x hx q hq hqirr v hv
        a 1 z hqone (by simp [z])).mpr ha
    simpa only [IsUnit.unit_spec] using v.ord_coe_unit hz.unit
/-- Polynomial evaluation at the finite place has residue kernel generated by `q`. -/
theorem p06_9e0f5043ff_fpm_rd_eval_kernel
    (K F : Type*) [Field K] [Field F] [Algebra K F] (x : F)
    (hx : Transcendental K x) (q : Polynomial K) (hq : Irreducible q)
    (v : AlgebraicCurve.Place K F)
    (hv : ∀ f : F, f ∈ v.toValuationSubring ↔
      ∃ a b : Polynomial K, ¬ q ∣ b ∧
        f = Polynomial.aeval x a / Polynomial.aeval x b) :
    ∃ e : Polynomial K →ₐ[K] v.toValuationSubring,
      (∀ a : Polynomial K, (e a : F) = Polynomial.aeval x a) ∧
      RingHom.ker ((IsLocalRing.residue v.toValuationSubring).comp e.toRingHom) =
        Ideal.span ({q} : Set (Polynomial K)) := by
  classical
  have hinj := transcendental_iff_injective.mp hx
  have hne (a : Polynomial K) (ha : a ≠ 0) : Polynomial.aeval x a ≠ 0 := by
    intro h
    exact ha (hinj (h.trans (map_zero (Polynomial.aeval x)).symm))
  -- Denominator 1 lifts every polynomial evaluation into the valuation ring.
  have hmem (a : Polynomial K) : Polynomial.aeval x a ∈ v.toValuationSubring :=
    (hv _).mpr ⟨a, 1, hq.not_dvd_one, by rw [map_one, div_one]⟩
  let e : Polynomial K →ₐ[K] v.toValuationSubring :=
    { toFun := fun a => ⟨Polynomial.aeval x a, hmem a⟩
      map_one' := Subtype.ext (map_one (Polynomial.aeval x))
      map_mul' := fun a b => Subtype.ext (map_mul (Polynomial.aeval x) a b)
      map_zero' := Subtype.ext (map_zero (Polynomial.aeval x))
      map_add' := fun a b => Subtype.ext (map_add (Polynomial.aeval x) a b)
      commutes' := fun c => Subtype.ext ((Polynomial.aeval x).commutes c) }
  have he (a : Polynomial K) : (e a : F) = Polynomial.aeval x a := rfl
  -- A polynomial not divisible by q has an inverse evaluation in the valuation ring.
  have hunit (a : Polynomial K) (ha : ¬ q ∣ a) : IsUnit (e a) := by
    have ha0 : Polynomial.aeval x a ≠ 0 := hne a (fun h => ha (h ▸ dvd_zero q))
    have hi : (Polynomial.aeval x a)⁻¹ ∈ v.toValuationSubring :=
      (hv _).mpr ⟨1, a, ha, by rw [map_one, one_div]⟩
    exact isUnit_iff_exists_inv.mpr
      ⟨⟨(Polynomial.aeval x a)⁻¹, hi⟩, Subtype.ext (mul_inv_cancel₀ ha0)⟩
  -- An inverse of q(x) would force q to divide an allowed denominator.
  have hq_nonunit : ¬ IsUnit (e q) := by
    intro hu
    obtain ⟨z, hz⟩ := isUnit_iff_exists_inv.mp hu
    have hmul : Polynomial.aeval x q * (z : F) = 1 :=
      congrArg (fun t : v.toValuationSubring => (t : F)) hz
    obtain ⟨a, b, hb, hzrep⟩ := (hv (z : F)).mp z.property
    have hb0 : Polynomial.aeval x b ≠ 0 := hne b (fun h => hb (h ▸ dvd_zero q))
    have hab : Polynomial.aeval x q * Polynomial.aeval x a = Polynomial.aeval x b := by
      calc
        Polynomial.aeval x q * Polynomial.aeval x a =
            (Polynomial.aeval x q * (z : F)) * Polynomial.aeval x b := by
          rw [hzrep, ← mul_div_assoc, div_mul_cancel₀ _ hb0]
        _ = Polynomial.aeval x b := by rw [hmul, one_mul]
    apply hb
    refine ⟨a, hinj ?_⟩
    rw [map_mul]
    exact hab.symm
  have hq_zero : IsLocalRing.residue v.toValuationSubring (e q) = 0 := by
    by_contra h
    exact hq_nonunit ((IsLocalRing.residue_ne_zero_iff_isUnit _).mp h)
  refine ⟨e, he, ?_⟩
  ext a
  rw [RingHom.mem_ker, Ideal.mem_span_singleton]
  change IsLocalRing.residue v.toValuationSubring (e a) = 0 ↔ q ∣ a
  constructor
  · intro ha
    by_contra hqa
    exact ((IsLocalRing.residue_ne_zero_iff_isUnit _).mpr (hunit a hqa)) ha
  · rintro ⟨b, rfl⟩
    rw [map_mul, map_mul, hq_zero, zero_mul]
theorem p06_9e0f5043ff_fpm_rd_residue_surjective
    (K F : Type*) [Field K] [Field F] [Algebra K F] (x : F)
    (hx : Transcendental K x) (q : Polynomial K) (hq : Irreducible q)
    (v : AlgebraicCurve.Place K F)
    (hrep : ∀ h : v.toValuationSubring, ∃ a b : Polynomial K,
      ¬ q ∣ b ∧ (h : F) = Polynomial.aeval x a / Polynomial.aeval x b)
    (e : Polynomial K →ₐ[K] v.toValuationSubring)
    (he : ∀ a : Polynomial K, (e a : F) = Polynomial.aeval x a)
    (heq : IsLocalRing.residue v.toValuationSubring (e q) = 0) :
    Function.Surjective ((IsLocalRing.residue v.toValuationSubring).comp e.toRingHom) := by
  let ρ := IsLocalRing.residue v.toValuationSubring
  let φ := ρ.comp e.toRingHom
  intro r
  obtain ⟨h, rfl⟩ := IsLocalRing.residue_surjective (R := v.toValuationSubring) r
  obtain ⟨a, b, hb, hab⟩ := hrep h
  have hb0 : b ≠ 0 := fun hb0 => hb (hb0 ▸ dvd_zero q)
  have heb0 : Polynomial.aeval x b ≠ 0 := by
    intro heb0
    apply hb0
    exact (transcendental_iff_injective.mp hx) (by simpa using heb0)
  obtain ⟨u, t, hut⟩ := hq.coprime_iff_not_dvd.mpr hb
  have htb : φ t * φ b = 1 := by
    have hφq : φ q = 0 := heq
    simpa only [map_add, map_mul, map_one, hφq, mul_zero, zero_add]
      using congrArg φ hut
  have hmul : h * e b = e a := by
    apply Subtype.ext
    change (h : F) * (e b : F) = (e a : F)
    rw [he, he, hab, div_mul_cancel₀ _ heb0]
  have hres : ρ h * φ b = φ a := by
    change ρ h * ρ (e b) = ρ (e a)
    simpa only [map_mul] using congrArg ρ hmul
  refine ⟨a * t, ?_⟩
  change φ (a * t) = ρ h
  calc
    φ (a * t) = φ a * φ t := map_mul φ a t
    _ = (ρ h * φ b) * φ t := by rw [hres]
    _ = ρ h := by rw [mul_assoc, mul_comm (φ b) (φ t), htb, mul_one]

end Submission


namespace Submission

theorem p06_9e0f5043ff_fpm_residue_degree
    (K F : Type*) [Field K] [Field F] [Algebra K F] (x : F)
    (hx : Transcendental K x) (q : Polynomial K) (_hq : q.Monic)
    (hqi : Irreducible q) (v : AlgebraicCurve.Place K F)
    (hv : ∀ f : F, f ∈ v.toValuationSubring ↔
      ∃ a b : Polynomial K, ¬ q ∣ b ∧
        f = Polynomial.aeval x a / Polynomial.aeval x b) :
    v.deg = q.natDegree := by
  obtain ⟨e, he, hker⟩ :=
    Submission.p06_9e0f5043ff_fpm_rd_eval_kernel K F x hx q hqi v hv
  have hqzero : IsLocalRing.residue v.toValuationSubring (e q) = 0 := by
    change q ∈ RingHom.ker ((IsLocalRing.residue v.toValuationSubring).comp e.toRingHom)
    rw [hker]
    exact Ideal.subset_span (Set.mem_singleton q)
  have hsurj := Submission.p06_9e0f5043ff_fpm_rd_residue_surjective
    K F x hx q hqi v (fun h => (hv (h : F)).mp h.property) e he hqzero
  let φ : Polynomial K →ₐ[K] v.ResidueField :=
    (IsScalarTower.toAlgHom K v.toValuationSubring v.ResidueField).comp e
  have hkerφ : RingHom.ker φ = Ideal.span ({q} : Set (Polynomial K)) := hker
  have hsurjφ : Function.Surjective φ := hsurj
  have hdim :=
    ((Ideal.quotientEquivAlgOfEq K hkerφ.symm).trans
      (Ideal.quotientKerAlgEquivOfSurjective (f := φ) hsurjφ)).toLinearEquiv.finrank_eq
  exact hdim.symm.trans finrank_quotient_span_eq_natDegree

/-- Assemble the finite place, its residue degree, and its normalized orders. -/
theorem p06_9e0f5043ff_rmp_finite_place_model
    (K F : Type*) [Field K] [Field F] [Algebra K F] (x : F)
    (hx : Transcendental K x)
    (hfrac : ∀ f : F, ∃ a b : Polynomial K,
      b ≠ 0 ∧ f = Polynomial.aeval x a / Polynomial.aeval x b)
    (q : Polynomial K) (hq : q.Monic) (hirr : Irreducible q) :
    ∃ v : AlgebraicCurve.Place K F,
      (∀ f : F, f ∈ v.toValuationSubring ↔ ∃ a b : Polynomial K,
        ¬ q ∣ b ∧ f = Polynomial.aeval x a / Polynomial.aeval x b) ∧
      v.deg = q.natDegree ∧
      v.ord (Polynomial.aeval x q) = 1 ∧
      (∀ a : Polynomial K, ¬ q ∣ a → v.ord (Polynomial.aeval x a) = 0) := by
  obtain ⟨v, hv⟩ :=
    Submission.p06_9e0f5043ff_fpm_exists_local_place K F x hx hfrac q hq hirr
  exact ⟨v, hv,
    Submission.p06_9e0f5043ff_fpm_residue_degree K F x hx q hq hirr v hv,
    Submission.p06_9e0f5043ff_fpm_normalized_orders K F x hx q hq hirr v hv⟩
set_option warningAsError true

namespace Submission

/-- A place containing the polynomial coordinate is the localization at a monic
irreducible polynomial. The frozen proof base supplies `Place.center_ne_bot`
for the nonzero prime center and `Place.toValuationSubring_eq_of_forall_mem`
for its localization in `Definitions.Def_AlgebraicCurve_PlacesOverDVR`. -/
theorem p06_9e0f5043ff_rmp_finite_place_classification
    (K : Type*) [Field K]
    (v : AlgebraicCurve.Place K (FractionRing (Polynomial K)))
    (hX : algebraMap (Polynomial K) (FractionRing (Polynomial K)) Polynomial.X ∈
      v.toValuationSubring) :
    ∃ q : Polynomial K, q.Monic ∧ Irreducible q ∧
      (∀ f : FractionRing (Polynomial K), f ∈ v.toValuationSubring ↔
        ∃ a b : Polynomial K, ¬ q ∣ b ∧
          f = algebraMap (Polynomial K) (FractionRing (Polynomial K)) a /
            algebraMap (Polynomial K) (FractionRing (Polynomial K)) b) := by
  classical
  -- Constants and the coordinate generate the polynomial ring.
  have hpoly : ∀ p : Polynomial K,
      algebraMap (Polynomial K) (FractionRing (Polynomial K)) p ∈
        v.toValuationSubring := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p r hp hr => simpa only [map_add] using add_mem hp hr
    | monomial n a =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow]
      apply mul_mem
      · rw [Polynomial.C_eq_algebraMap, ← IsScalarTower.algebraMap_apply]
        exact v.algebraMap_mem' a
      · exact pow_mem hX n
  -- Normalize the generator of the nonzero prime center.
  obtain ⟨q, hnorm, hspan⟩ := Ideal.exists_normalized_span_of_isPrincipal
    (AlgebraicCurve.Place.center (Polynomial K) v hpoly)
  have hq0 : q ≠ 0 := by
    intro hq
    apply v.center_ne_bot hpoly
    simpa only [hq, Ideal.span_singleton_zero] using hspan
  have hprime : (Ideal.span {q}).IsPrime := by
    rw [← hspan]
    infer_instance
  refine ⟨q, (Polynomial.normalize_eq_self_iff_monic hq0).mp hnorm,
    ((Ideal.span_singleton_prime hq0).mp hprime).irreducible, ?_⟩
  intro f
  -- The inherited localization theorem supplies both membership directions.
  -- Since the center is (q), its complement consists of denominators not divisible by q.
  rw [v.toValuationSubring_eq_of_forall_mem hpoly]
  change (∃ (a b : Polynomial K)
    (_ : b ∉ AlgebraicCurve.Place.center (Polynomial K) v hpoly),
      f = algebraMap (Polynomial K) (FractionRing (Polynomial K)) a *
        (algebraMap (Polynomial K) (FractionRing (Polynomial K)) b)⁻¹) ↔ _
  simp only [hspan, Ideal.mem_span_singleton, exists_prop, div_eq_mul_inv]

end Submission
/-- Clear the first row by an invertible column operation, preserving the trailing block.
The correction matrix squares to zero, so `1 - M` has the explicit inverse `1 + M`.
Divisibility supplies the coefficients without requiring the pivot to be nonzero or a unit. -/
theorem p06_9e0f5043ff_sdp_clear_first_row :
    ∀ (R : Type*) [CommRing R] (m : ℕ)
      (H : Matrix (Fin (m + 1)) (Fin (m + 1)) R),
      (∀ i : Fin m, H i.succ 0 = 0) →
      (∀ j : Fin m, H 0 0 ∣ H 0 j.succ) →
      ∃ V : Matrix (Fin (m + 1)) (Fin (m + 1)) R,
        IsUnit V ∧ H * V = Matrix.of (fun i j =>
          Fin.cases (Fin.cases (H 0 0) (fun _ => 0) j)
            (fun i' => Fin.cases 0 (fun j' => H i'.succ j'.succ) j) i) := by
  classical
  intro R _ m H hcol hdiv
  choose b hb using hdiv
  let M : Matrix (Fin (m + 1)) (Fin (m + 1)) R :=
    Matrix.of (fun i j => Fin.cases (Fin.cases 0 b j) (fun _ => 0) i)
  have hM0 (i : Fin (m + 1)) : M i 0 = 0 := by
    refine Fin.cases ?_ (fun _ => ?_) i <;> rfl
  have hMs (i : Fin m) (j : Fin (m + 1)) : M i.succ j = 0 := rfl
  have hMM : M * M = 0 := by
    ext i j
    simp [Matrix.mul_apply, Fin.sum_univ_succ, hM0, hMs]
  have hHM (i j : Fin (m + 1)) :
      (H * M) i j = H i 0 * Fin.cases 0 b j := by
    simp [Matrix.mul_apply, Fin.sum_univ_succ, M]
  refine ⟨1 - M, ?_, ?_⟩
  · refine ⟨⟨1 - M, 1 + M, ?_, ?_⟩, rfl⟩
    · simp [sub_mul, mul_add, hMM]
    · simp [mul_sub, add_mul, hMM]
  · rw [mul_sub, mul_one]
    ext i j
    refine Fin.cases ?_ (fun i' => ?_) i <;>
      refine Fin.cases ?_ (fun j' => ?_) j <;>
      simp [Matrix.sub_apply, hHM, hcol, hb]
/-- Clear the first column below a divisible pivot by a unit that preserves the first row. -/
theorem p06_9e0f5043ff_sdp_clear_first_column
    (R : Type*) [CommRing R] (m : ℕ)
    (B : Matrix (Fin (m + 1)) (Fin (m + 1)) R)
    (h : ∀ i : Fin m, B 0 0 ∣ B i.succ 0) :
    ∃ U : Matrix (Fin (m + 1)) (Fin (m + 1)) R,
      IsUnit U ∧ (∀ j : Fin (m + 1), (U * B) 0 j = B 0 j) ∧
        (∀ i : Fin m, (U * B) i.succ 0 = 0) := by
  classical
  choose a ha using h
  -- Extend the chosen coefficients by zero so the first row is unchanged.
  let c : Fin (m + 1) → R := Fin.cases 0 a
  let N : Matrix (Fin (m + 1)) (Fin (m + 1)) R :=
    Matrix.of fun i j => if j = 0 then c i else 0
  have hmul (M : Matrix (Fin (m + 1)) (Fin (m + 1)) R)
      (i j : Fin (m + 1)) : (N * M) i j = c i * M 0 j := by
    simp [Matrix.mul_apply, N]
  have hsq : N * N = 0 := by
    ext i j
    simp [hmul, N, c]
  -- Since N² = 0, the clearing matrix 1 - N has two-sided inverse 1 + N.
  refine ⟨1 - N, ?_, ?_, ?_⟩
  · refine ⟨⟨1 - N, 1 + N, ?_, ?_⟩, rfl⟩
    · simp [sub_mul, mul_add, hsq]
    · simp [mul_sub, add_mul, hsq]
  · intro j
    simp [sub_mul, hmul, c]
  · intro i
    simp [sub_mul, hmul, c, ha i, mul_comm]

end Submission

/-- The reciprocal of the fraction-ring variable is transcendental and presents every fraction. -/
theorem Submission.p06_9e0f5043ff_inf_reciprocal_presentation :
    ∀ (K : Type*) [Field K],
      Transcendental K
        ((algebraMap (Polynomial K) (FractionRing (Polynomial K)) Polynomial.X)⁻¹) ∧
      (∀ f : FractionRing (Polynomial K), ∃ a b : Polynomial K, b ≠ 0 ∧
        f = Polynomial.aeval
          ((algebraMap (Polynomial K) (FractionRing (Polynomial K)) Polynomial.X)⁻¹) a /
          Polynomial.aeval
          ((algebraMap (Polynomial K) (FractionRing (Polynomial K)) Polynomial.X)⁻¹) b) := by
  intro K _
  let t : FractionRing (Polynomial K) :=
    algebraMap (Polynomial K) (FractionRing (Polynomial K)) Polynomial.X
  have hinj := IsFractionRing.injective (Polynomial K) (FractionRing (Polynomial K))
  have ht : t ≠ 0 := by
    exact fun h => Polynomial.X_ne_zero (hinj (h.trans (map_zero _).symm))
  have heval (p : Polynomial K) :
      Polynomial.aeval t p = algebraMap (Polynomial K) (FractionRing (Polynomial K)) p := by
    simp [t, Polynomial.aeval_algebraMap_apply]
  have htrans : Transcendental K t :=
    (transcendental_algebraMap_iff hinj).mpr (Polynomial.transcendental_X K)
  have hs : Transcendental K t⁻¹ := by
    intro h
    exact htrans (IsAlgebraic.inv_iff.mp h)
  refine ⟨hs, ?_⟩
  intro f
  change ∃ a b : Polynomial K, b ≠ 0 ∧
    f = Polynomial.aeval t⁻¹ a / Polynomial.aeval t⁻¹ b
  by_cases hf : f = 0
  · exact ⟨0, 1, one_ne_zero, by simp [hf]⟩
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (Polynomial K) f
  have hb0 : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
  have hbr : b.reverse ≠ 0 := by simpa using hb0
  have hbev : Polynomial.aeval t⁻¹ b.reverse ≠ 0 := by
    exact fun h => hbr ((transcendental_iff_injective.mp hs) (by simpa using h))
  let : Invertible t := invertibleOfNonzero ht
  have hreverse (p : Polynomial K) :
      algebraMap (Polynomial K) (FractionRing (Polynomial K)) p =
        Polynomial.aeval t⁻¹ p.reverse / (t⁻¹) ^ p.natDegree := by
    have h := Polynomial.eval₂_reverse_mul_pow
      (algebraMap K (FractionRing (Polynomial K))) t p
    simpa only [invOf_eq_inv, ← Polynomial.aeval_def, heval, inv_pow,
      div_inv_eq_mul] using h.symm
  rw [← hab, hreverse a, hreverse b]
  by_cases hdeg : a.natDegree ≤ b.natDegree
  · refine ⟨Polynomial.X ^ (b.natDegree - a.natDegree) * a.reverse,
      b.reverse, hbr, ?_⟩
    rw [map_mul, map_pow, Polynomial.aeval_X, pow_sub₀ _ (inv_ne_zero ht) hdeg]
    field_simp
  · refine ⟨a.reverse, Polynomial.X ^ (a.natDegree - b.natDegree) * b.reverse,
      mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) hbr, ?_⟩
    rw [map_mul, map_pow, Polynomial.aeval_X,
      pow_sub₀ _ (inv_ne_zero ht) (Nat.le_of_lt (Nat.lt_of_not_ge hdeg))]
    field_simp
/-- Reciprocal evaluation has order minus the degree at the place above the origin. -/
theorem Submission.p06_9e0f5043ff_inf_reciprocal_polynomial_order :
    ∀ (K F : Type*) [Field K] [Field F] [Algebra K F] (s : F),
      Transcendental K s → ∀ v : AlgebraicCurve.Place K F, v.ord s = 1 →
      (∀ c : Polynomial K, ¬ (Polynomial.X : Polynomial K) ∣ c →
        v.ord (Polynomial.aeval s c) = 0) →
      ∀ a : Polynomial K, a ≠ 0 →
        v.ord (Polynomial.aeval s⁻¹ a) = -(a.natDegree : ℤ) := by
  intro K F _ _ _ s hs v hv hzero a ha
  have hs0 : s ≠ 0 := by
    intro h
    exact hs ⟨Polynomial.X, Polynomial.X_ne_zero, by simpa using h⟩
  have hrev : a.reverse ≠ 0 := fun h => ha (Polynomial.reverse_eq_zero.mp h)
  have heval : Polynomial.aeval s a.reverse ≠ 0 := fun h => hs ⟨a.reverse, hrev, h⟩
  have hnot : ¬ (Polynomial.X : Polynomial K) ∣ a.reverse := by
    simpa only [Polynomial.X_dvd_iff, Polynomial.coeff_zero_reverse,
      Polynomial.leadingCoeff_eq_zero] using ha
  have horder : v.ord (Polynomial.aeval s a.reverse) = 0 := hzero _ hnot
  -- Reversal writes reciprocal evaluation as a negative power times a unit at v.
  have hidentity : Polynomial.aeval s⁻¹ a =
      s ^ (-(a.natDegree : ℤ)) * Polynomial.aeval s a.reverse := by
    let : Invertible s⁻¹ := invertibleOfNonzero (inv_ne_zero hs0)
    simpa only [invOf_eq_inv, inv_inv, ← Polynomial.aeval_def, zpow_neg,
      zpow_natCast, inv_pow, mul_comm] using
      (Polynomial.eval₂_reverse_mul_pow (algebraMap K F) s⁻¹ a).symm
  rw [hidentity, v.ord_mul (zpow_ne_zero _ hs0) heval, v.ord_zpow, hv,
    horder, mul_one, add_zero]
/-- Polynomial evaluation at a nonunit of a place is a unit exactly away from `(X)`. -/
theorem Submission.p06_9e0f5043ff_vfc_polynomial_unit_criterion :
    ∀ (K F : Type*) [Field K] [Field F] [Algebra K F]
      (s : F) (w : AlgebraicCurve.Place K F),
      s⁻¹ ∉ w.toValuationSubring → ∀ p : Polynomial K,
        (∃ u : Units w.toValuationSubring,
          ((u : w.toValuationSubring) : F) = Polynomial.aeval s p) ↔
        ¬ (Polynomial.X : Polynomial K) ∣ p := by
  intro K F _ _ _ s w hinv p
  have hs : s ∈ w.toValuationSubring :=
    (w.toValuationSubring.mem_or_inv_mem s).resolve_right hinv
  let t : w.toValuationSubring := ⟨s, hs⟩
  have ht : ¬ IsUnit t := by
    rintro ⟨u, hu⟩
    have hmul : s * (((u⁻¹ : Units w.toValuationSubring) : w.toValuationSubring) : F) = 1 := by
      change (t : F) * _ = 1
      rw [← hu]
      exact congrArg (fun x : w.toValuationSubring => (x : F)) u.val_inv
    have hi : (((u⁻¹ : Units w.toValuationSubring) : w.toValuationSubring) : F) = s⁻¹ :=
      eq_inv_of_mul_eq_one_right hmul
    exact hinv (hi ▸ (u⁻¹).val.property)
  -- Evaluate inside the valuation subring using its inherited K-algebra structure.
  let E : Polynomial K →+* w.toValuationSubring := (Polynomial.aeval t).toRingHom
  have hE (q : Polynomial K) : (E q : F) = Polynomial.aeval s q := by
    exact (Polynomial.aeval_algHom_apply
      (IsScalarTower.toAlgHom K w.toValuationSubring F) t q).symm
  let J : Ideal (Polynomial K) := (IsLocalRing.maximalIdeal w.toValuationSubring).comap E
  have hJ : J ≠ ⊤ :=
    Ideal.comap_ne_top E (IsLocalRing.maximalIdeal.isMaximal w.toValuationSubring).ne_top
  have hX : (Polynomial.X : Polynomial K) ∈ J := by
    change E Polynomial.X ∈ IsLocalRing.maximalIdeal w.toValuationSubring
    change Polynomial.aeval t Polynomial.X ∈ IsLocalRing.maximalIdeal w.toValuationSubring
    rw [Polynomial.aeval_X, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact ht
  -- The proper contraction contains the maximal ideal (X), so they coincide.
  have hspan : Ideal.span ({Polynomial.X} : Set (Polynomial K)) = J :=
    (PrincipalIdealRing.isMaximal_of_irreducible Polynomial.irreducible_X).eq_of_le hJ
      (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hX))
  have hunit : IsUnit (E p) ↔ ¬ (Polynomial.X : Polynomial K) ∣ p := by
    rw [← IsLocalRing.notMem_maximalIdeal]
    change p ∉ J ↔ ¬ (Polynomial.X : Polynomial K) ∣ p
    rw [← hspan, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨u, hu⟩
    apply hunit.mp
    refine ⟨u, ?_⟩
    exact Subtype.ext (hu.trans (hE p).symm)
  · intro hp
    obtain ⟨u, hu⟩ := hunit.mpr hp
    exact ⟨u, (congrArg (fun x : w.toValuationSubring => (x : F)) hu).trans (hE p)⟩
/-- Membership of a unit times a parameter-power quotient forces nonnegative exponent. -/
theorem Submission.p06_9e0f5043ff_vfc_unit_power_quotient_exponents :
    ∀ (F : Type*) [Field F] (W : Subring F) (s : F), s ∈ W → s⁻¹ ∉ W →
      ∀ (u : Units W) (r k : ℕ), ((u : W) : F) * s ^ r / s ^ k ∈ W → k ≤ r := by
  intro F _ W s hs hsinv u r k hquot
  have hs0 : s ≠ 0 := by
    intro h
    apply hsinv
    simp [h]
  have hu : ((u : W) : F) * ((↑(u⁻¹) : W) : F) = 1 := by
    exact_mod_cast u.mul_inv
  by_contra hle
  let n := k - r - 1
  have hk : k = r + n + 1 := by
    dsimp [n]
    omega
  have hprod :
      (((u : W) : F) * s ^ r / s ^ k) * ((↑(u⁻¹) : W) : F) * s ^ n ∈ W :=
    W.mul_mem (W.mul_mem hquot (↑(u⁻¹) : W).property) (W.pow_mem hs n)
  have heq :
      (((u : W) : F) * s ^ r / s ^ k) * ((↑(u⁻¹) : W) : F) * s ^ n = s⁻¹ := by
    calc
      _ = (((u : W) : F) * ((↑(u⁻¹) : W) : F)) * (s ^ r * s ^ n) / s ^ k := by
        ring
      _ = s ^ (r + n) / s ^ (r + n + 1) := by
        rw [hu, one_mul, ← pow_add, hk]
      _ = s⁻¹ := by
        rw [pow_succ, div_mul_eq_div_div, div_self (pow_ne_zero _ hs0), one_div]
  exact hsinv (heq ▸ hprod)


namespace Submission
/-- The valuation ring in which the parameter is a nonunit consists exactly of
fractions whose denominator is not divisible by `X`. -/
theorem p06_9e0f5043ff_inf_valuation_fraction_characterization :
    ∀ (K F : Type*) [Field K] [Field F] [Algebra K F] (s : F),
      Transcendental K s →
      (∀ f : F, ∃ a b : Polynomial K, b ≠ 0 ∧
        f = Polynomial.aeval s a / Polynomial.aeval s b) →
      ∀ w : AlgebraicCurve.Place K F, s⁻¹ ∉ w.toValuationSubring →
      ∀ f : F, f ∈ w.toValuationSubring ↔
        ∃ a b : Polynomial K, ¬ (Polynomial.X : Polynomial K) ∣ b ∧
          f = Polynomial.aeval s a / Polynomial.aeval s b := by
  intro K F _ _ _ s hs hfrac w hsinv f
  classical
  let W : Subring F := w.toValuationSubring.toSubring
  have hsW : s ∈ W := (w.toValuationSubring.mem_or_inv_mem s).resolve_right hsinv
  have hs0 : s ≠ 0 := by
    intro h
    apply hsinv
    simp [h]
  have heval_mem (p : Polynomial K) : Polynomial.aeval s p ∈ W := by
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simpa only [map_add] using W.add_mem hp hq
    | monomial n a =>
      rw [Polynomial.aeval_monomial]
      exact W.mul_mem (w.algebraMap_mem' a) (W.pow_mem hsW n)
  have hunit_inv (u : Units W) :
      (((u⁻¹ : Units W) : W) : F) = (((u : W) : F))⁻¹ := by
    exact (Units.map W.subtype.toMonoidHom u).val_inv_eq_inv_val
  have heval_ne (p : Polynomial K) (hp : p ≠ 0) : Polynomial.aeval s p ≠ 0 := by
    intro h
    apply hp
    exact (transcendental_iff_injective.mp hs) (h.trans (map_zero _).symm)
  constructor
  · intro hf
    by_cases hf0 : f = 0
    · exact ⟨0, 1, by simp [Polynomial.X_dvd_iff], by simp [hf0]⟩
    obtain ⟨a, b, hb, hfab⟩ := hfrac f
    have ha : a ≠ 0 := by
      intro h
      apply hf0
      simpa [h] using hfab
    -- Remove all factors of X, leaving polynomials that evaluate to units.
    obtain ⟨a₀, ha_factor, ha₀⟩ :=
      Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd a ha 0
    obtain ⟨b₀, hb_factor, hb₀⟩ :=
      Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd b hb 0
    simp only [map_zero, sub_zero] at ha_factor ha₀ hb_factor hb₀
    obtain ⟨ua, hua⟩ :=
      (p06_9e0f5043ff_vfc_polynomial_unit_criterion K F s w hsinv a₀).mpr ha₀
    obtain ⟨ub, hub⟩ :=
      (p06_9e0f5043ff_vfc_polynomial_unit_criterion K F s w hsinv b₀).mpr hb₀
    let r := a.rootMultiplicity 0
    let k := b.rootMultiplicity 0
    let u : Units W := ua * ub⁻¹
    have hu : ((u : W) : F) = Polynomial.aeval s a₀ / Polynomial.aeval s b₀ := by
      change ((ua : W) : F) * (((ub⁻¹ : Units W) : W) : F) = _
      rw [hunit_inv, hua, hub, div_eq_mul_inv]
    have hnormalized : f = ((u : W) : F) * s ^ r / s ^ k := by
      rw [hfab, ha_factor, hb_factor, hu]
      simp only [map_mul, map_pow, Polynomial.aeval_X]
      dsimp only [r, k]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    -- Membership rules out a negative exponent of the nonunit parameter.
    have hkr : k ≤ r :=
      p06_9e0f5043ff_vfc_unit_power_quotient_exponents F W s hsW hsinv u r k
        (hnormalized ▸ hf)
    refine ⟨Polynomial.X ^ (r - k) * a₀, b₀, hb₀, ?_⟩
    have hb₀_ne : Polynomial.aeval s b₀ ≠ 0 :=
      heval_ne b₀ (fun h => hb₀ (by simp [h]))
    have hpow : s ^ r = s ^ (r - k) * s ^ k := by
      rw [← pow_add, Nat.sub_add_cancel hkr]
    rw [hnormalized, hu]
    simp only [map_mul, map_pow, Polynomial.aeval_X]
    rw [hpow]
    field_simp [hs0, hb₀_ne]
  · rintro ⟨a, b, hb, rfl⟩
    obtain ⟨u, hu⟩ :=
      (p06_9e0f5043ff_vfc_polynomial_unit_criterion K F s w hsinv b).mpr hb
    have hinv : (Polynomial.aeval s b)⁻¹ ∈ W := by
      rw [← hu, ← hunit_inv]
      exact ((u⁻¹ : Units W) : W).property
    change Polynomial.aeval s a / Polynomial.aeval s b ∈ W
    rw [div_eq_mul_inv]
    exact W.mul_mem (heval_mem a) hinv
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

end Submission
