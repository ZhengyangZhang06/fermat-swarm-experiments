import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Mathlib.RingTheory.Length

namespace Submission

theorem p06_9e0f5043ff_wll_residue_composition_series :
    ∀ (A B : Type*) [CommRing A] [CommRing B] [IsDedekindDomain B] [Algebra A B]
      (b : B), b ≠ 0 → ∀ n : ℕ,
      Module.length A (B ⧸ Ideal.span ({b} : Set B)) = (n : ℕ∞) →
      ∃ s : CompositionSeries (Submodule B (B ⧸ Ideal.span ({b} : Set B))),
        s.head = ⊥ ∧ s.last = ⊤ ∧
        ∃ p : Fin s.length → IsDedekindDomain.HeightOneSpectrum B,
          ∀ i : Fin s.length,
            Nonempty ((↥(s i.succ) ⧸ (s i.castSucc).comap (s i.succ).subtype) ≃ₗ[B]
              (B ⧸ (p i).asIdeal)) := by
  intro A B _ _ _ _ b hb n hn
  classical
  let C := B ⧸ Ideal.span ({b} : Set B)
  have hfinite : IsFiniteLength A C := Module.length_ne_top_iff.mp (by
    rw [hn]
    exact ENat.natCast_ne_top n)
  obtain ⟨hnoeth, hart⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp hfinite
  have : IsNoetherian B C := isNoetherian_of_tower A hnoeth
  have : IsArtinian B C := isArtinian_of_tower A hart
  obtain ⟨s, hs_head, hs_last⟩ := exists_compositionSeries_of_isNoetherian_isArtinian B C
  refine ⟨s, hs_head, hs_last, ?_⟩
  have hbC : b ∈ Module.annihilator B C := by
    rw [Ideal.annihilator_quotient]
    exact Ideal.subset_span (Set.mem_singleton b)
  have factors : ∀ i : Fin s.length, ∃ p : IsDedekindDomain.HeightOneSpectrum B,
      Nonempty ((↥(s i.succ) ⧸ (s i.castSucc).comap (s i.succ).subtype) ≃ₗ[B]
        (B ⧸ p.asIdeal)) := by
    intro i
    let N := (s i.castSucc).comap (s i.succ).subtype
    have hsimple : IsSimpleModule B (↥(s i.succ) ⧸ N) :=
      (covBy_iff_quot_is_simple (s.step i).le).mp (s.step i)
    obtain ⟨m, hm, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp hsimple
    have hbN : b ∈ Module.annihilator B (s i.succ) :=
      (s i.succ).subtype.annihilator_le_of_injective (Submodule.injective_subtype _) hbC
    have hbS : b ∈ Module.annihilator B (↥(s i.succ) ⧸ N) :=
      N.mkQ.annihilator_le_of_surjective N.mkQ_surjective hbN
    have hbm : b ∈ m := by
      rwa [e.annihilator_eq, Ideal.annihilator_quotient] at hbS
    have hm_ne : m ≠ ⊥ := by
      intro hm_bot
      exact hb (by simpa [hm_bot] using hbm)
    exact ⟨⟨m, hm.isPrime, hm_ne⟩, ⟨e⟩⟩
  choose p hp using factors
  exact ⟨p, hp⟩

open AlgebraicCurve
theorem AlgebraicCurve.hasPrincipalDivisors_of_transcendental (K : Type*) [Field K] [CharZero K] {F : Type*} [Field F]
    [Algebra K F] (x : F) (hx : Transcendental K x)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F] : HasPrincipalDivisors K F := by
  sorry

namespace Submission

/-- Compute the length over `A` by summing the residue factors of a composition series over `B`.
The sum is in `ℕ∞`, so the factors need not have finite length over `A`.
Apply `Module.length_eq_add_of_exact` after restricting scalars, then induct on the
number of factors using `Fin.sum_univ_castSucc`, including the empty series. -/
theorem p06_9e0f5043ff_wll_length_sum_factors
    (A B M : Type*) [CommRing A] [CommRing B] [IsDedekindDomain B] [Algebra A B]
    [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
    (s : CompositionSeries (Submodule B M))
    (p : Fin s.length → IsDedekindDomain.HeightOneSpectrum B)
    (hhead : s.head = ⊥) (hlast : s.last = ⊤)
    (hfactors : ∀ i : Fin s.length,
      Nonempty ((↥(s i.succ) ⧸ (s i.castSucc).comap (s i.succ).subtype) ≃ₗ[B]
        (B ⧸ (p i).asIdeal))) :
    Module.length A M =
      Finset.sum Finset.univ (fun i : Fin s.length => Module.length A (B ⧸ (p i).asIdeal)) := by
  -- Restrict each short exact sequence and its factor equivalence to A.
  have hstep (i : Fin s.length) :
      Module.length A (s i.succ) =
        Module.length A (s i.castSucc) + Module.length A (B ⧸ (p i).asIdeal) := by
    obtain ⟨e⟩ := hfactors i
    let N := (s i.castSucc).comap (s i.succ).subtype
    have h := Module.length_eq_add_of_exact
      (N.subtype.restrictScalars A) (N.mkQ.restrictScalars A)
      N.subtype_injective N.mkQ_surjective (LinearMap.exact_subtype_mkQ N)
    rw [(Submodule.comapSubtypeEquivOfLe (s.lt_succ i).le).restrictScalars A |>.length_eq,
      (e.restrictScalars A).length_eq] at h
    exact h
  -- Sum by induction in ℕ∞; cancellation would require extra finiteness.
  have hsum : ∀ (n : ℕ) (f : Fin (n + 1) → ℕ∞) (g : Fin n → ℕ∞),
      (∀ i, f i.succ = f i.castSucc + g i) →
      f (Fin.last n) = f 0 + ∑ i, g i := by
    intro n
    induction n with
    | zero =>
      intro f g h
      simp
    | succ n ih =>
      intro f g h
      change f (Fin.last n).succ = _
      rw [h (Fin.last n), ih (fun i => f i.castSucc) (fun i => g i.castSucc)
        (fun i => h i.castSucc), Fin.sum_univ_castSucc, add_assoc, Fin.castSucc_zero]
  -- Identify the zero and top endpoints with the zero module and M.
  have h := hsum s.length (fun i => Module.length A (s i))
    (fun i => Module.length A (B ⧸ (p i).asIdeal)) hstep
  change Module.length A s.last = Module.length A s.head + _ at h
  rw [hhead, hlast, Module.length_eq_zero (R := A) (M := (⊥ : Submodule B M)), zero_add] at h
  rw [← (Submodule.topEquiv (R := B) (M := M)).restrictScalars A |>.length_eq]
  exact h

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
/-- A finite family in a DVR with a nonzero entry has a nonzero member dividing every entry.
Choose a member of minimum uniformizer exponent among the nonzero entries. Unit factors
do not affect divisibility, and the minimum power divides every other power. -/
theorem p06_9e0f5043ff_dmd_finite_family_dividing_member
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (ι : Type*) [Fintype ι] (a : ι → A) (ha : ∃ i, a i ≠ 0) :
    ∃ i, a i ≠ 0 ∧ ∀ j, a i ∣ a j := by
  classical
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  let S := {i : ι // a i ≠ 0}
  have hfactor : ∀ i : S, ∃ (n : ℕ) (u : Aˣ), a i = u * π ^ n :=
    fun i => IsDiscreteValuationRing.eq_unit_mul_pow_irreducible i.property hπ
  choose e u he using hfactor
  have hS : (Finset.univ : Finset S).Nonempty := by
    obtain ⟨i, hi⟩ := ha
    exact ⟨⟨i, hi⟩, Finset.mem_univ _⟩
  -- Minimize the uniformizer exponent among the nonzero entries.
  obtain ⟨i, _, hmin⟩ := Finset.exists_min_image Finset.univ e hS
  refine ⟨i.val, i.property, ?_⟩
  intro j
  by_cases hj : a j = 0
  · rw [hj]
    exact dvd_zero _
  · rw [he i, he ⟨j, hj⟩, Units.mul_left_dvd, Units.dvd_mul_left]
    exact pow_dvd_pow π (hmin ⟨j, hj⟩ (Finset.mem_univ _))
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
  -- A denominator coprime to q supplies an inverse in the valuation ring.
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
open scoped BigOperators

/-- Length after localization is the sum of the localized successive quotient lengths.
The equality is in `ℕ∞`; the proof uses addition only and needs no finite-length hypothesis. -/
theorem p06_9e0f5043ff_llm_localized_series_sum
    (B M : Type*) [CommRing B] [AddCommGroup M] [Module B M]
    (T : Submonoid B) (s : CompositionSeries (Submodule B M))
    (hhead : s.head = ⊥) (hlast : s.last = ⊤) :
    Module.length (Localization T) (LocalizedModule T M) =
      Finset.sum Finset.univ (fun i : Fin s.length =>
        Module.length (Localization T)
          (LocalizedModule T (↥(s i.succ) ⧸ (s i.castSucc).comap (s i.succ).subtype))) := by
  -- Localize each short exact sequence of successive terms.
  have hstep (i : Fin s.length) :
      Module.length (Localization T) (LocalizedModule T (s i.succ)) =
        Module.length (Localization T) (LocalizedModule T (s i.castSucc)) +
          Module.length (Localization T)
            (LocalizedModule T (↥(s i.succ) ⧸ (s i.castSucc).comap (s i.succ).subtype)) := by
    let hle : s i.castSucc ≤ s i.succ := s.strictMono.monotone (Fin.castSucc_le_succ i)
    let f := Submodule.inclusion hle
    let g := ((s i.castSucc).comap (s i.succ).subtype).mkQ
    have hex : Function.Exact f g := by
      rw [LinearMap.exact_iff, Submodule.ker_mkQ, Submodule.range_inclusion]
    -- The localized maps are linear over `Localization T`. Clear a denominator
    -- to lift each localized kernel element through the original exact sequence.
    refine Module.length_eq_add_of_exact (LocalizedModule.map T f) (LocalizedModule.map T g)
      (LocalizedModule.map_injective T f (Submodule.inclusion_injective hle))
      (LocalizedModule.map_surjective T g (Submodule.mkQ_surjective _)) ?_
    intro y
    constructor
    · refine LocalizedModule.induction_on (fun m u hy => ?_) y
      rw [LocalizedModule.map_mk, ← LocalizedModule.zero_mk (1 : T),
        LocalizedModule.mk_eq, one_smul, smul_zero] at hy
      obtain ⟨a, haT, ha⟩ := Subtype.exists.1 hy
      rw [smul_zero, Submonoid.mk_smul, ← map_smul, hex (a • m)] at ha
      obtain ⟨x, hx⟩ := ha
      use LocalizedModule.mk x (⟨a, haT⟩ * u)
      rw [LocalizedModule.map_mk, hx,
        ← LocalizedModule.mk_cancel_common_left ⟨a, haT⟩ u m, Submonoid.mk_smul]
    · rintro ⟨x, hx⟩
      revert hx
      refine LocalizedModule.induction_on (fun m u hx => ?_) x
      rw [← hx, LocalizedModule.map_mk, LocalizedModule.map_mk,
        (hex (f m)).2 ⟨m, rfl⟩, LocalizedModule.zero_mk]
  -- Add the recurrences without subtracting or cancelling infinite lengths.
  have hsum : ∀ (n : ℕ) (l : Fin (n + 1) → ℕ∞) (q : Fin n → ℕ∞),
      (∀ i, l i.succ = l i.castSucc + q i) →
        l (Fin.last n) = l 0 + ∑ i, q i := by
    intro n
    induction n with
    | zero => intro l q h; simp
    | succ n ih =>
      intro l q h
      rw [← Fin.succ_last, h (Fin.last n), Fin.sum_univ_castSucc]
      have hprefix := ih (fun i => l i.castSucc) (fun i => q i.castSucc)
        (fun i => by simpa only [Fin.succ_castSucc] using h i.castSucc)
      rw [hprefix, Fin.castSucc_zero, add_assoc]
  have hzero : Module.length (Localization T) (LocalizedModule T (s 0)) = 0 := by
    change Module.length (Localization T) (LocalizedModule T s.head) = 0
    rw [hhead]
    exact Module.length_eq_zero
  have htop : Module.length (Localization T) (LocalizedModule T (s (Fin.last s.length))) =
      Module.length (Localization T) (LocalizedModule T M) := by
    change Module.length (Localization T) (LocalizedModule T s.last) = _
    rw [hlast]
    exact (IsLocalizedModule.mapEquiv T (LocalizedModule.mkLinearMap T (⊤ : Submodule B M))
      (LocalizedModule.mkLinearMap T M) (Localization T) (Submodule.topEquiv)).length_eq
  have h := hsum s.length
    (fun i => Module.length (Localization T) (LocalizedModule T (s i)))
    (fun i => Module.length (Localization T)
      (LocalizedModule T (↥(s i.succ) ⧸ (s i.castSucc).comap (s i.succ).subtype))) hstep
  simpa only [htop, hzero, zero_add] using h
/-- The uniformizer exponent of a nonzero scalar is both its quotient length and its place order. -/
theorem p06_9e0f5043ff_dlen_scalar_quotient
    (K E : Type*) [Field K] [Field E] [Algebra K E]
    (v : AlgebraicCurve.Place K E) (a : v.toValuationSubring) (ha : a ≠ 0) :
    ∃ n : ℕ,
      Module.length v.toValuationSubring
        (v.toValuationSubring ⧸ Ideal.span ({a} : Set v.toValuationSubring)) = (n : ℕ∞) ∧
      v.ord (algebraMap v.toValuationSubring E a) = (n : ℤ) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ
  refine ⟨n, ?_, ?_⟩
  · rw [Ideal.span_singleton_mul_left_unit u.isUnit, ← Ideal.span_singleton_pow,
      ← hπ.maximalIdeal_eq]
    exact IsDiscreteValuationRing.length_quotient_pow_maximalIdeal v.toValuationSubring n
  · change v.ord (((u : v.toValuationSubring) : E) * (π : E) ^ n) = (n : ℤ)
    simpa only [zpow_natCast] using v.ord_unit_smul_zpow u hπ (n : ℤ)
/-- The cokernel of a diagonal matrix is the product of its coordinate principal quotients. -/
theorem p06_9e0f5043ff_dmc_diagonal_quotient
    (R : Type*) [CommRing R] (m : ℕ) (d : Fin m → R) :
    Nonempty (((Fin m → R) ⧸ LinearMap.range (Matrix.mulVecLin (Matrix.diagonal d)))
      ≃ₗ[R] ((i : Fin m) → R ⧸ Ideal.span ({d i} : Set R))) := by
  classical
  -- Reduce each coordinate modulo the corresponding principal ideal.
  let C : (Fin m → R) →ₗ[R] ((i : Fin m) → R ⧸ Ideal.span ({d i} : Set R)) :=
    LinearMap.pi fun i => (Ideal.span ({d i} : Set R)).mkQ.comp (LinearMap.proj i)
  have hker : LinearMap.ker C = LinearMap.range (Matrix.mulVecLin (Matrix.diagonal d)) := by
    ext y
    simp only [LinearMap.mem_ker, LinearMap.mem_range]
    constructor
    · intro hy
      have hyi : ∀ i, d i ∣ y i := by
        intro i
        apply Ideal.mem_span_singleton.mp
        apply (Submodule.Quotient.mk_eq_zero _).mp
        exact congrFun hy i
      choose z hz using hyi
      exact ⟨z, funext fun i => (Matrix.mulVec_diagonal d z i).trans (hz i).symm⟩
    · rintro ⟨z, rfl⟩
      funext i
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      exact Ideal.mem_span_singleton.mpr ⟨z i, Matrix.mulVec_diagonal d z i⟩
  have hsurj : Function.Surjective C := by
    intro w
    choose y hy using fun i => (Ideal.span ({d i} : Set R)).mkQ_surjective (w i)
    exact ⟨y, funext hy⟩
  -- The first isomorphism theorem supplies the induced bijection and its linear inverse.
  exact ⟨(Submodule.quotEquivOfEq _ _ hker.symm).trans (C.quotKerEquivOfSurjective hsurj)⟩
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
