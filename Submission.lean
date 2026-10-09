/-
Copyright 2026 Anthropic, PBC. Licensed under Apache-2.0; see LICENSE.
Source: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_GaloisRepAdic_exists_quadraticRelation_forall_of_frobenius.lean
Modified: replaced the proof with sorry and removed P2M proof imports.
Requires the upstream Definitions modules and their dependencies.
-/

import Mathlib
import Definitions.Def_GaloisRep_Adic
attribute [-instance] AlgebraicClosure.Rat.isGalois FrobeniusDensity.liesOver_ratBelow FrobeniusDensity.isMaximal_ratPrimeIdeal Deep.NTSupply.instNormalRayClassSubgroup NumberField.NormResidueChar.fintype_G NumberField.NormResidueChar.finite_G
attribute [-simp] TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec

set_option autoImplicit false

open IsLocalRing

theorem GaloisRepAdic.exists_quadraticRelation_forall_of_frobenius
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [CharZero 𝒪]
    (p : ℕ) [Fact p.Prime] (hp𝒪 : (p : 𝒪) ∈ maximalIdeal 𝒪)
    {R : Type} [CommRing R] [IsLocalRing R] [Algebra 𝒪 R] [Module.Finite 𝒪 R]
    (hl : IsLocalHom (algebraMap 𝒪 R))
    (ρ : GaloisRepAdic R)
    {Y : Type} [AddCommGroup Y] [Module R Y] [Module 𝒪 Y] [IsScalarTower 𝒪 R Y] [Module.Finite 𝒪 Y]
    (ρY : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Module.End R Y)
    (hcont : ∀ n : ℕ, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ F, σ x = x) →
        ∀ y : Y, ρY σ y - y ∈ (Ideal.span {(p : R)} ^ n • (⊤ : Submodule R Y)))
    (L : ℕ) [NeZero L] (D : (ZMod L)ˣ →* Module.End R Y)
    (hD : ∀ (u : (ZMod L)ˣ) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), D u * ρY σ = ρY σ * D u)
    (S₀ : Finset ℕ)
    (hES : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S₀ → ∀ (hℓL : ¬ ℓ ∣ L), ℓ ≠ p →
      ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ ℓ →
          ρY σ * ρY σ - (ρ.trace σ) • ρY σ
            + (ℓ : R) • D (ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓL)) = 0) :
    ∃ (c : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Rˣ)
      (χ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (ZMod L)ˣ),
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
        ρY σ * ρY σ - (ρ.trace σ) • ρY σ + ((c σ : Rˣ) : R) • D (χ σ) = 0 := by
  sorry


theorem Submission.p09_af497904fe_quadratic_congruence :
    ∀ {C M : Type} [CommRing C] [AddCommGroup M] [Module C M]
      (J : Ideal C) (a b d : Module.End C M) (s r u v : C),
      (∀ y : M, (a - b) y ∈ J • (⊤ : Submodule C M)) →
      s - r ∈ J → u - v ∈ J → ∀ y : M,
      ((a * a - s • a + u • d) - (b * b - r • b + v • d)) y ∈
        J • (⊤ : Submodule C M) := by
  intro C M _ _ _ J a b d s r u v hab hsr huv y
  have ha : a ((a - b) y) ∈ J • (⊤ : Submodule C M) := by
    refine Submodule.smul_induction_on (hab y) ?_ ?_
    · intro c hc z _
      rw [map_smul]
      exact Submodule.smul_mem_smul hc (Submodule.mem_top : a z ∈ (⊤ : Submodule C M))
    · intro x z hx hz
      rw [map_add]
      exact Submodule.add_mem _ hx hz
  have hs : s • ((a - b) y) ∈ J • (⊤ : Submodule C M) :=
    Submodule.smul_mem _ s (hab y)
  have hsb : (s - r) • b y ∈ J • (⊤ : Submodule C M) :=
    Submodule.smul_mem_smul hsr (Submodule.mem_top : b y ∈ (⊤ : Submodule C M))
  have hud : (u - v) • d y ∈ J • (⊤ : Submodule C M) :=
    Submodule.smul_mem_smul huv (Submodule.mem_top : d y ∈ (⊤ : Submodule C M))
  have heq :
      ((a * a - s • a + u • d) - (b * b - r • b + v • d)) y =
        a ((a - b) y) + (a - b) (b y) - s • ((a - b) y) -
          (s - r) • b y + (u - v) • d y := by
    simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply,
      Module.End.mul_apply, map_sub, smul_sub, sub_smul]
    abel
  rw [heq]
  exact Submodule.add_mem _
    (Submodule.sub_mem _ (Submodule.sub_mem _ (Submodule.add_mem _ ha (hab (b y))) hs) hsb)
    hud
theorem Submission.p09_af497904fe_action_congruence :
    ∀ {C M : Type} [CommRing C] [AddCommGroup M] [Module C M]
      (J : Ideal C)
      (U : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Module.End C M)
      (F : IntermediateField ℚ (AlgebraicClosure ℚ)),
      (∀ δ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
        (∀ x ∈ F, δ x = x) → ∀ y : M, U δ y - y ∈ J • (⊤ : Submodule C M)) →
      ∀ σ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
        (∀ x ∈ F, σ x = τ x) →
        ∀ y : M, (U σ - U τ) y ∈ J • (⊤ : Submodule C M) := by
  intro C M _ _ _ J U F hU σ τ hστ y
  have hpres (v : Module.End C M) {z : M}
      (hz : z ∈ J • (⊤ : Submodule C M)) :
      v z ∈ J • (⊤ : Submodule C M) := by
    refine Submodule.smul_induction_on
      (p := fun z => v z ∈ J • (⊤ : Submodule C M)) hz ?_ ?_
    · intro a ha z _
      rw [map_smul]
      exact Submodule.smul_mem_smul ha Submodule.mem_top
    · intro x z hx hz
      rw [map_add]
      exact Submodule.add_mem _ hx hz
  have hfix : ∀ x ∈ F, (τ⁻¹ * σ) x = x := by
    intro x hx
    change τ.symm (σ x) = x
    rw [hστ x hx, τ.symm_apply_apply]
  have h := hpres (U τ) (hU (τ⁻¹ * σ) hfix y)
  have hcomp : U τ (U (τ⁻¹ * σ) y) = U σ y := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
  simpa only [map_sub, hcomp, LinearMap.sub_apply] using h
theorem Submission.p09_af497904fe_adic_character_lift :
    ∀ {C G : Type} [CommRing C] [Group G] (J : Ideal C) [IsAdicComplete J C]
      (a : ℕ → G → C),
      (∀ (n m : ℕ), n ≤ m → ∀ g : G, a m g - a n g ∈ J ^ n) →
      (∀ n : ℕ, a n 1 - 1 ∈ J ^ n) →
      (∀ (n : ℕ) (g h : G), a n (g * h) - a n g * a n h ∈ J ^ n) →
      ∃! b : G →* Cˣ, ∀ (n : ℕ) (g : G), (b g : C) - a n g ∈ J ^ n := by
  intro C G _ _ J _ a hcompat hone hmul
  classical
  have htop (n : ℕ) : (J ^ n • ⊤ : Submodule C C) = J ^ n := by
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
  have hsep {x y : C} (hxy : ∀ n : ℕ, x - y ∈ J ^ n) : x = y := by
    apply (IsHausdorff.eq_iff_smodEq (I := J)).2
    intro n
    rw [SModEq.sub_mem, htop]
    exact hxy n
  have hlim (g : G) : ∃ c : C, ∀ n : ℕ, c - a n g ∈ J ^ n := by
    obtain ⟨c, hc⟩ := IsPrecomplete.prec (inferInstance : IsPrecomplete J C)
      (f := fun n => a n g) (by
        intro n m hnm
        apply SModEq.symm
        rw [SModEq.sub_mem, htop]
        exact hcompat n m hnm g)
    refine ⟨c, fun n => ?_⟩
    simpa only [SModEq.sub_mem, htop] using (hc n).symm
  choose β hβ using hlim
  have hβone : β 1 = 1 := by
    apply hsep
    intro n
    convert (J ^ n).add_mem (hβ 1 n) (hone n) using 1
    ring
  have hβmul (g h : G) : β (g * h) = β g * β h := by
    apply hsep
    intro n
    convert (J ^ n).sub_mem
      ((J ^ n).add_mem (hβ (g * h) n) (hmul n g h))
      ((J ^ n).add_mem
        (Ideal.mul_mem_right (a n h) (J ^ n) (hβ g n))
        ((J ^ n).mul_mem_left (β g) (hβ h n))) using 1
    ring
  let b : G →* Cˣ :=
    { toFun := fun g =>
        { val := β g
          inv := β g⁻¹
          val_inv := by rw [← hβmul, mul_inv_cancel, hβone]
          inv_val := by rw [← hβmul, inv_mul_cancel, hβone] }
      map_one' := by
        apply Units.ext
        exact hβone
      map_mul' := fun g h => by
        apply Units.ext
        exact hβmul g h }
  refine ⟨b, ?_, ?_⟩
  · intro n g
    exact hβ g n
  · intro b' hb'
    apply MonoidHom.ext
    intro g
    apply Units.ext
    apply hsep
    intro n
    change (b' g : C) - β g ∈ J ^ n
    convert (J ^ n).sub_mem (hb' n g) (hβ g n) using 1
    ring
theorem Submission.p09_af497904fe_trace_congruence :
    ∀ {C W : Type} [CommRing C] [AddCommGroup W] [Module C W]
      [Module.Free C W] [Module.Finite C W] (J : Ideal C) (u v : Module.End C W),
      (∀ w : W, (u - v) w ∈ J • (⊤ : Submodule C W)) →
        LinearMap.trace C W u - LinearMap.trace C W v ∈ J := by
  intro C W _ _ _ _ _ J u v h
  classical
  let b := Module.Free.chooseBasis C W
  rw [← map_sub, LinearMap.trace_eq_matrix_trace C b]
  unfold Matrix.trace
  apply J.sum_mem
  intro i _
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply]
  change b.coord i ((u - v) (b i)) ∈ J
  refine Submodule.smul_induction_on (p := fun w => b.coord i w ∈ J) (h (b i)) ?_ ?_
  · intro a ha w _
    rw [map_smul, smul_eq_mul]
    exact J.mul_mem_right _ ha
  · intro x y hx hy
    rw [map_add]
    exact J.add_mem hx hy
theorem Submission.p09_af497904fe_finite_inverse_limit
    (X : ℕ → Type) [∀ i : ℕ, Finite (X i)] [∀ i : ℕ, Nonempty (X i)]
    (r : ∀ i j : ℕ, i ≤ j → X j → X i)
    (hself : ∀ (i : ℕ) (x : X i), r i i (Nat.le_refl i) x = x)
    (hcomp : ∀ (i j k : ℕ) (hij : i ≤ j) (hjk : j ≤ k) (x : X k),
      r i k (Nat.le_trans hij hjk) x = r i j hij (r j k hjk x)) :
    ∃ x : ∀ i : ℕ, X i, ∀ (i j : ℕ) (hij : i ≤ j), r i j hij (x j) = x i := by
  classical
  let F : CategoryTheory.Functor (Opposite ℕ) (Type) :=
    { obj := fun n => X n.unop
      map := fun {i j} f => TypeCat.ofHom (r j.unop i.unop
        (CategoryTheory.leOfHom f.unop))
      map_id := fun i => by
        apply CategoryTheory.ConcreteCategory.ext_apply
        exact hself i.unop
      map_comp := fun {i j k} f g => by
        apply CategoryTheory.ConcreteCategory.ext_apply
        exact hcomp k.unop j.unop i.unop
          (CategoryTheory.leOfHom g.unop) (CategoryTheory.leOfHom f.unop) }
  have : ∀ n, Finite (F.obj n) := fun n => inferInstanceAs (Finite (X n.unop))
  have : ∀ n, Nonempty (F.obj n) := fun n => inferInstanceAs (Nonempty (X n.unop))
  -- Finite transition images stabilize; their intersections are nonempty.
  have hstable : F.IsMittagLeffler :=
    F.isMittagLeffler_of_exists_finite_range fun j =>
      ⟨j, (CategoryTheory.homOfLE (Nat.le_refl j.unop)).op, Set.toFinite _⟩
  let Y : ℕ → Type := fun n => F.toEventualRanges.obj (Opposite.op n)
  have hzero : Nonempty (Y 0) := F.toEventualRanges_nonempty hstable _
  -- The adjacent transition maps are surjective on the stable images.
  have hlift : ∀ (n : ℕ) (y : Y n),
      ∃ z : Y (n + 1), r n (n + 1) (Nat.le_succ n) z.val = y.val := by
    intro n y
    obtain ⟨z, hz⟩ := F.surjective_toEventualRanges hstable
      (CategoryTheory.homOfLE (Nat.le_succ n)).op y
    exact ⟨z, congrArg Subtype.val hz⟩
  let lift : ∀ n, Y n → Y (n + 1) := fun n y => Classical.choose (hlift n y)
  let y : ∀ n, Y n := Nat.rec (Classical.choice hzero) (fun n yn => lift n yn)
  have hadj (n : ℕ) : r n (n + 1) (Nat.le_succ n) (y (n + 1)).val = (y n).val :=
    Classical.choose_spec (hlift n (y n))
  refine ⟨fun n => (y n).val, ?_⟩
  intro i j hij
  induction j, hij using Nat.le_induction with
  | base => exact hself i (y i).val
  | succ j hij ih =>
      rw [hcomp i j (j + 1) hij (Nat.le_succ j), hadj j]
      exact ih


theorem Submission.p09_af497904fe_fcc_character_finite_action :
    ∀ (N : ℕ) [NeZero N],
      ∃ (χ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (ZMod N)ˣ)
        (F : IntermediateField ℚ (AlgebraicClosure ℚ)),
        FiniteDimensional ℚ F ∧
        (∀ σ τ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
          (∀ x ∈ F, σ x = τ x) → χ σ = χ τ) ∧
        (∀ (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
          (ζ : AlgebraicClosure ℚ),
          ζ ^ N = 1 → σ ζ = ζ ^ ((χ σ : ZMod N).val)) := by
  classical
  intro N _
  obtain ⟨ζ₀, hζ₀⟩ :=
    HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) N
  refine ⟨hζ₀.autToPow ℚ, IntermediateField.adjoin ℚ {ζ₀},
    IntermediateField.adjoin.finiteDimensional
      ((hζ₀.isIntegral (NeZero.pos N)).tower_top), ?_, ?_⟩
  · intro σ τ hστ
    apply Units.ext
    apply ZMod.val_injective
    apply hζ₀.pow_inj (ZMod.val_lt _) (ZMod.val_lt _)
    rw [hζ₀.autToPow_spec ℚ σ, hζ₀.autToPow_spec ℚ τ]
    exact hστ ζ₀ (IntermediateField.mem_adjoin_simple_self ℚ ζ₀)
  · intro σ ζ hζ
    obtain ⟨b, _, rfl⟩ := hζ₀.eq_pow_of_pow_eq_one hζ
    rw [map_pow, ← hζ₀.autToPow_spec ℚ σ, pow_right_comm]
theorem Submission.p09_af497904fe_fcc_fra_roots_mem_inv :
    ∀ (N : ℕ) [NeZero N] (P : ValuationSubring (AlgebraicClosure ℚ))
      (ζ : AlgebraicClosure ℚ), ζ ^ N = 1 → ζ ∈ P ∧ ζ⁻¹ ∈ P := by
  intro N _ P ζ hζ
  have hinv : ζ ^ (N - 1) = ζ⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [pow_sub_one_mul (NeZero.ne N), hζ]
  have hback : (ζ⁻¹) ^ (N - 1) = ζ := by
    rw [inv_pow, hinv, inv_inv]
  have hmem : ζ ∈ P := by
    rcases P.mem_or_inv_mem ζ with h | h
    · exact h
    · rw [← hback]
      exact pow_mem h (N - 1)
  refine ⟨hmem, ?_⟩
  rw [← hinv]
  exact pow_mem hmem (N - 1)
theorem Submission.p09_af497904fe_fcc_fra_residue_injective :
    ∀ (N : ℕ) [NeZero N] (ℓ : ℕ), ℓ.Prime → ¬ ℓ ∣ N →
      ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
        ∀ x y : P, x ^ N = 1 → y ^ N = 1 →
          IsLocalRing.residue P x = IsLocalRing.residue P y → x = y := by
  intro N _ ℓ hℓ hN P hP x y hx hy hxy
  have hℓP : (ℓ : P) ∈ IsLocalRing.maximalIdeal P :=
    ValuationSubring.coe_mem_nonunits_iff.mp (by simpa [ValuationSubring.LiesOverPrime] using hP)
  have hℓk : (ℓ : IsLocalRing.ResidueField P) = 0 := by
    rw [← map_natCast (IsLocalRing.residue P) ℓ]
    exact (IsLocalRing.residue_eq_zero_iff _).mpr hℓP
  have : CharP (IsLocalRing.ResidueField P) ℓ :=
    (CharP.charP_iff_prime_eq_zero hℓ).mpr hℓk
  have hNk : (N : IsLocalRing.ResidueField P) ≠ 0 :=
    fun h => hN ((CharP.cast_eq_zero_iff (IsLocalRing.ResidueField P) ℓ N).mp h)
  have hone (t : P) (ht : t ^ N = 1)
      (hred : IsLocalRing.residue P t = 1) : t = 1 := by
    by_contra h
    have hs : (∑ i ∈ Finset.range N, t ^ i) = 0 :=
      (mul_eq_zero.mp ((geom_sum_mul t N).trans (by rw [ht, sub_self]))).resolve_right
        (sub_ne_zero.mpr h)
    have hr := congrArg (IsLocalRing.residue P) hs
    apply hNk
    simpa [map_sum, map_pow, hred] using hr
  have hpos : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  let v : P := y ^ (N - 1)
  have hyv : y * v = 1 := by
    dsimp [v]
    rw [← pow_succ', Nat.sub_add_cancel hpos, hy]
  have hvy : v * y = 1 := by rw [mul_comm, hyv]
  have hv : v ^ N = 1 := by
    dsimp [v]
    rw [← pow_mul, Nat.mul_comm, pow_mul, hy, one_pow]
  have htv : x * v = 1 := by
    apply hone
    · rw [mul_pow, hx, hv, one_mul]
    · rw [map_mul, hxy, ← map_mul, hyv, map_one]
  calc
    x = x * (v * y) := by rw [hvy, mul_one]
    _ = (x * v) * y := (mul_assoc x v y).symm
    _ = y := by rw [htv, one_mul]


theorem Submission.p09_af497904fe_ffe_prime_frobenius_congruence :
    ∀ (E : IntermediateField ℚ (AlgebraicClosure ℚ))
      [FiniteDimensional ℚ E] [IsGalois ℚ E] (ℓ : ℕ), ℓ.Prime →
      ∀ q : Ideal (NumberField.RingOfIntegers E), q.IsPrime →
        (ℓ : NumberField.RingOfIntegers E) ∈ q →
        Finite (NumberField.RingOfIntegers E ⧸ q) →
        ∃ g : E ≃ₐ[ℚ] E, ∀ a : NumberField.RingOfIntegers E,
          NumberField.RingOfIntegers.mapRingEquiv g.toRingEquiv a - a ^ ℓ ∈ q := by
  intro E _ _ ℓ hℓ q hq hℓq hfin
  let : q.IsPrime := hq
  let : Finite (NumberField.RingOfIntegers E ⧸ q) := hfin
  let : Fact ℓ.Prime := ⟨hℓ⟩
  let : CharP (NumberField.RingOfIntegers E ⧸ q) ℓ :=
    (CharP.charP_iff_prime_eq_zero hℓ).mpr (by
      simpa only [map_natCast] using (Ideal.Quotient.eq_zero_iff_mem.mpr hℓq))
  -- A fixed algebraic integer descends to an integral rational, hence an integer.
  let : Algebra.IsInvariant ℤ (NumberField.RingOfIntegers E) (E ≃ₐ[ℚ] E) := by
    constructor
    intro a ha
    obtain ⟨r, hr⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (F := ℚ) (a : E)).mpr
      (fun g ↦ congrArg (fun b : NumberField.RingOfIntegers E ↦ (b : E)) (ha g))
    have hi : IsIntegral ℤ r :=
      (isIntegral_algebraMap_iff (algebraMap ℚ E).injective).mp
        (hr.symm ▸ NumberField.RingOfIntegers.isIntegral_coe a)
    obtain ⟨z, hz⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hi
    refine ⟨z, NumberField.RingOfIntegers.ext ?_⟩
    change algebraMap ℤ E z = (a : E)
    rw [← hr, ← hz, IsScalarTower.algebraMap_apply ℤ ℚ E]
  -- Frobenius fixes the quotient of the integers and lifts through the stabilizer.
  let P : Ideal ℤ := q.under ℤ
  let φ : (NumberField.RingOfIntegers E ⧸ q) ≃ₐ[ℤ ⧸ P]
      (NumberField.RingOfIntegers E ⧸ q) :=
    AlgEquiv.ofRingEquiv (f := frobeniusEquiv (NumberField.RingOfIntegers E ⧸ q) ℓ) (by
      intro z
      obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
      change (frobeniusEquiv (NumberField.RingOfIntegers E ⧸ q) ℓ)
        (z : NumberField.RingOfIntegers E ⧸ q) = (z : NumberField.RingOfIntegers E ⧸ q)
      exact map_intCast _ z)
  obtain ⟨g, hg⟩ := Ideal.Quotient.stabilizerHom_surjective (E ≃ₐ[ℚ] E) P q φ
  refine ⟨g.val, fun a ↦ ?_⟩
  have h := congrArg (fun σ : (NumberField.RingOfIntegers E ⧸ q) ≃ₐ[ℤ ⧸ P]
    (NumberField.RingOfIntegers E ⧸ q) ↦ σ (Ideal.Quotient.mk q a)) hg
  change Ideal.Quotient.mk q
      (NumberField.RingOfIntegers.mapRingEquiv g.val.toRingEquiv a) =
    (Ideal.Quotient.mk q a) ^ ℓ at h
  rw [← map_pow] at h
  exact Ideal.Quotient.eq.mp h
theorem Submission.p09_af497904fe_ffe_localized_frobenius :
    ∀ (E : IntermediateField ℚ (AlgebraicClosure ℚ)) (ℓ : ℕ), ℓ.Prime →
      ∀ (V : ValuationSubring E) (q : Ideal (NumberField.RingOfIntegers E)),
      q.IsPrime →
      (∀ x : E, x ∈ V ↔ ∃ a b : NumberField.RingOfIntegers E,
        b ∉ q ∧ x = (a : E) / (b : E)) →
      (∀ a : NumberField.RingOfIntegers E, (a : E) ∈ V.nonunits ↔ a ∈ q) →
      ∀ g : E ≃ₐ[ℚ] E,
      (∀ a : NumberField.RingOfIntegers E,
        NumberField.RingOfIntegers.mapRingEquiv g.toRingEquiv a - a ^ ℓ ∈ q) →
      V.IsFrobeniusAt g ℓ := by
  intro E ℓ hℓ V q hq hloc hnon g hcong
  let γ := NumberField.RingOfIntegers.mapRingEquiv g.toRingEquiv
  have hγ (a : NumberField.RingOfIntegers E) : γ a ∈ q ↔ a ∈ q := by
    constructor
    · intro ha
      apply hq.mem_of_pow_mem ℓ
      simpa only [γ, sub_sub_cancel] using q.sub_mem ha (hcong a)
    · intro ha
      simpa only [sub_add_cancel] using
        q.add_mem (hcong a) (q.pow_mem_of_mem ha ℓ hℓ.pos)
  have hγinv (a : NumberField.RingOfIntegers E) : γ.symm a ∈ q ↔ a ∈ q := by
    simpa only [RingEquiv.apply_symm_apply] using (hγ (γ.symm a)).symm
  have hforward (x : E) (hx : x ∈ V) : g x ∈ V := by
    obtain ⟨a, b, hb, rfl⟩ := (hloc x).mp hx
    apply (hloc _).mpr
    refine ⟨γ a, γ b, fun h => hb ((hγ b).mp h), ?_⟩
    exact map_div₀ g _ _
  have hbackward (x : E) (hx : x ∈ V) : g.symm x ∈ V := by
    obtain ⟨a, b, hb, rfl⟩ := (hloc x).mp hx
    apply (hloc _).mpr
    refine ⟨γ.symm a, γ.symm b, fun h => hb ((hγinv b).mp h), ?_⟩
    exact map_div₀ g.symm _ _
  have hg : g ∈ V.decompositionSubgroup ℚ := by
    let := ValuationSubring.pointwiseMulAction (G := E ≃ₐ[ℚ] E) (K := E)
    rw [MulAction.mem_stabilizer_iff]
    ext x
    rw [ValuationSubring.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hforward y hy
    · intro hx
      exact ⟨g.symm x, hbackward x hx, g.apply_symm_apply x⟩
  have hint (a : NumberField.RingOfIntegers E) : (a : E) ∈ V :=
    (hloc _).mpr ⟨a, 1, hq.one_notMem, by simp⟩
  let i : NumberField.RingOfIntegers E →+* V :=
    { toFun := fun a => ⟨(a : E), hint a⟩
      map_one' := by apply Subtype.ext; exact map_one (algebraMap _ _)
      map_mul' := fun a b => by apply Subtype.ext; exact map_mul (algebraMap _ _) a b
      map_zero' := by apply Subtype.ext; exact map_zero (algebraMap _ _)
      map_add' := fun a b => by apply Subtype.ext; exact map_add (algebraMap _ _) a b }
  let κ : NumberField.RingOfIntegers E →+* IsLocalRing.ResidueField V :=
    (IsLocalRing.residue V).comp i
  have hker (a : NumberField.RingOfIntegers E) : κ a = 0 ↔ a ∈ q := by
    change IsLocalRing.residue V (i a) = 0 ↔ a ∈ q
    rw [IsLocalRing.residue_eq_zero_iff, ← ValuationSubring.coe_mem_nonunits_iff]
    exact hnon a
  have hκ (a : NumberField.RingOfIntegers E) : κ (γ a) = κ a ^ ℓ := by
    have h := (hker (γ a - a ^ ℓ)).mpr (hcong a)
    rw [map_sub, map_pow, sub_eq_zero] at h
    exact h
  have hfrac (v : V) (a b : NumberField.RingOfIntegers E) (hb : b ∉ q)
      (hv : (v : E) = (a : E) / (b : E)) :
      IsLocalRing.residue V v = κ a / κ b := by
    have hbE : (b : E) ≠ 0 := by
      intro hb0
      apply hb
      have : b = 0 := by
        apply NumberField.RingOfIntegers.ext
        exact hb0
      simpa only [this] using q.zero_mem
    have hmul : v * i b = i a := by
      apply Subtype.ext
      change (v : E) * (b : E) = (a : E)
      exact (eq_div_iff hbE).mp hv
    apply (eq_div_iff (fun h => hb ((hker b).mp h))).mpr
    exact (map_mul (IsLocalRing.residue V) v (i b)).symm.trans
      (congrArg (IsLocalRing.residue V) hmul)
  refine ⟨hg, ?_⟩
  intro z
  obtain ⟨v, rfl⟩ := IsLocalRing.residue_surjective (R := V) z
  obtain ⟨a, b, hb, hv⟩ := (hloc (v : E)).mp v.property
  rw [← IsLocalRing.ResidueField.residue_smul]
  have hgv : (((⟨g, hg⟩ : V.decompositionSubgroup ℚ) • v : V) : E) =
      (γ a : E) / (γ b : E) := by
    change g (v : E) = g (a : E) / g (b : E)
    rw [hv, map_div₀]
  rw [hfrac _ (γ a) (γ b) (fun h => hb ((hγ b).mp h)) hgv,
    hfrac v a b hb hv, hκ a, hκ b, div_pow]
