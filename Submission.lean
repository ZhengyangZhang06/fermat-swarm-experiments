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


theorem Submission.p09_af497904fe_fcc_frobenius_roots_action :
    ∀ (N : ℕ) [NeZero N] (ℓ : ℕ), ℓ.Prime → ¬ ℓ ∣ N →
      ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
        ∀ σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), P.IsFrobeniusAt σ ℓ →
          ∀ ζ : AlgebraicClosure ℚ, ζ ^ N = 1 → σ ζ = ζ ^ ℓ := by
  intro N _ ℓ hℓ hℓN P hP σ hσ ζ hζ
  obtain ⟨hσ, hfrob⟩ := hσ
  let g : P.decompositionSubgroup ℚ := ⟨σ, hσ⟩
  let z : P := ⟨ζ, (Submission.p09_af497904fe_fcc_fra_roots_mem_inv N P ζ hζ).1⟩
  have hx : (g • z : P) ^ N = 1 := by
    apply Subtype.ext
    change (σ ζ) ^ N = 1
    rw [← map_pow, hζ, map_one]
  have hy : (z ^ ℓ) ^ N = 1 := by
    apply Subtype.ext
    change (ζ ^ ℓ) ^ N = 1
    rw [pow_right_comm, hζ, one_pow]
  have hred : residue P (g • z) = residue P (z ^ ℓ) := by
    calc
      residue P (g • z) = g • residue P z :=
        ResidueField.residue_smul (P.decompositionSubgroup ℚ) g z
      _ = residue P z ^ ℓ := hfrob (residue P z)
      _ = residue P (z ^ ℓ) := (map_pow (residue P) z ℓ).symm
  exact congrArg Subtype.val
    (Submission.p09_af497904fe_fcc_fra_residue_injective
      N ℓ hℓ hℓN P hP (g • z) (z ^ ℓ) hx hy hred)


theorem Submission.p09_af497904fe_finite_cyclotomic_character
    (N : ℕ) [NeZero N] :
    ∃ (χ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (ZMod N)ˣ)
      (F : IntermediateField ℚ (AlgebraicClosure ℚ)),
      FiniteDimensional ℚ F ∧
      (∀ σ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
        (∀ x ∈ F, σ x = τ x) → χ σ = χ τ) ∧
      (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (ζ : AlgebraicClosure ℚ),
        ζ ^ N = 1 → σ ζ = ζ ^ ((χ σ : ZMod N).val)) ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N)
        (P : ValuationSubring (AlgebraicClosure ℚ)), P.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
          P.IsFrobeniusAt σ ℓ →
          χ σ = ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓN)) := by
  obtain ⟨χ, F, hF, hagree, hχ⟩ :=
    Submission.p09_af497904fe_fcc_character_finite_action N
  refine ⟨χ, F, hF, hagree, hχ, ?_⟩
  intro ℓ hℓ hℓN P hP σ hσ
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) N
  apply Units.ext
  apply ZMod.val_injective
  apply hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _)
  calc
    ζ ^ ((χ σ : ZMod N).val) = σ ζ := (hχ σ ζ hζ.pow_eq_one).symm
    _ = ζ ^ ℓ :=
      Submission.p09_af497904fe_fcc_frobenius_roots_action N ℓ hℓ hℓN P hP σ hσ ζ
        hζ.pow_eq_one
    _ = ζ ^ ((ZMod.unitOfCoprime ℓ
        ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓN) : ZMod N).val) := by
      rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast]
      exact pow_eq_pow_mod ℓ hζ.pow_eq_one
theorem Submission.p09_af497904fe_vloc_fraction_characterization :
    ∀ (E : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ E]
      (V : ValuationSubring E) (q : Ideal (NumberField.RingOfIntegers E)),
      q.IsPrime → q ≠ ⊥ →
      (∀ a : NumberField.RingOfIntegers E, (a : E) ∈ V) →
      (∀ a : NumberField.RingOfIntegers E, (a : E) ∈ V.nonunits ↔ a ∈ q) →
      ∀ x : E, x ∈ V ↔ ∃ a b : NumberField.RingOfIntegers E,
        b ∉ q ∧ x = (a : E) / (b : E) := by
  classical
  intro E _ V q hq hq0 hOV hcenter
  let : NumberField E := NumberField.of_module_finite ℚ E
  let : q.IsPrime := hq
  let A := Localization.subalgebra.ofField E q.primeCompl q.primeCompl_le_nonZeroDivisors
  let : IsDiscreteValuationRing A :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
      (NumberField.RingOfIntegers E) hq0 A
  have hA (x : E) : x ∈ A ↔ ∃ a b : NumberField.RingOfIntegers E,
      b ∉ q ∧ x = (a : E) / (b : E) := by
    change (∃ a b, ∃ _ : b ∈ q.primeCompl,
      x = algebraMap (NumberField.RingOfIntegers E) E a *
        (algebraMap (NumberField.RingOfIntegers E) E b)⁻¹) ↔ _
    simp only [Ideal.mem_primeCompl_iff, exists_prop, div_eq_mul_inv]
  have hinv (b : NumberField.RingOfIntegers E) (hb : b ∉ q) : (b : E)⁻¹ ∈ V := by
    by_contra h
    exact hb ((hcenter b).mp ((V.mem_nonunits_iff_or).mpr (Or.inr h)))
  have hAV (x : E) (hx : x ∈ A) : x ∈ V := by
    obtain ⟨a, b, hb, rfl⟩ := (hA x).mp hx
    simpa only [div_eq_mul_inv] using mul_mem (hOV a) (hinv b hb)
  intro x
  rw [← hA x]
  refine ⟨?_, hAV x⟩
  intro hx
  by_cases hx0 : x = 0
  · simpa only [hx0] using A.zero_mem
  rcases ValuationRing.isInteger_or_isInteger A x with ⟨a, ha⟩ | ⟨a, ha⟩
  · exact ha ▸ a.property
  have hxi : x⁻¹ ∈ A := ha ▸ a.property
  obtain ⟨a, b, hb, hab⟩ := (hA x⁻¹).mp hxi
  by_cases haq : a ∈ q
  · have ha0 : (a : E) ≠ 0 := by
      intro h
      rw [h, zero_div] at hab
      exact hx0 (inv_eq_zero.mp hab)
    have hainv : (a : E)⁻¹ ∈ V := by
      have heq : (a : E)⁻¹ = x * (b : E)⁻¹ := by
        have hb0 : (b : E) ≠ 0 := by
          intro h
          have hbzero : b = 0 := NumberField.RingOfIntegers.coe_eq_zero_iff.mp h
          apply hb
          rw [hbzero]
          exact q.zero_mem
        rw [← div_eq_mul_inv, eq_div_iff hb0]
        have h : x = (b : E) / (a : E) := by
          simpa only [inv_inv, inv_div] using congrArg Inv.inv hab
        simpa only [div_eq_mul_inv, mul_comm] using h.symm
      rw [heq]
      exact mul_mem hx (hinv b hb)
    exact False.elim (((V.mem_nonunits_iff_or).mp ((hcenter a).mpr haq)).elim
      ha0 (fun h => h hainv))
  · apply (hA x).mpr
    refine ⟨b, a, haq, ?_⟩
    simpa only [inv_inv, inv_div] using congrArg Inv.inv hab
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
theorem Submission.p09_af497904fe_ftl_compatible_automorphisms_glue :
    ∀ (F : ℕ → IntermediateField ℚ (AlgebraicClosure ℚ)) (hmono : Monotone F),
      (∀ x : AlgebraicClosure ℚ, ∃ i : ℕ, x ∈ F i) →
      ∀ g : (i : ℕ) → F i ≃ₐ[ℚ] F i,
        (∀ (i j : ℕ) (hij : i ≤ j) (x : F i),
          IntermediateField.inclusion (hmono hij) (g i x) =
            g j (IntermediateField.inclusion (hmono hij) x)) →
        ∃ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
          ∀ (i : ℕ) (x : F i),
            τ (x : AlgebraicClosure ℚ) = ((g i x : F i) : AlgebraicClosure ℚ) := by
  classical
  intro F hmono hcover g hcompat
  choose stage hstage using (fun x => hcover x)
  let lift (a : (i : ℕ) → F i ≃ₐ[ℚ] F i) (x : AlgebraicClosure ℚ) :
      AlgebraicClosure ℚ := a (stage x) ⟨x, hstage x⟩
  have hlift (a : (i : ℕ) → F i ≃ₐ[ℚ] F i)
      (ha : ∀ (i j : ℕ) (hij : i ≤ j) (x : F i),
        IntermediateField.inclusion (hmono hij) (a i x) =
          a j (IntermediateField.inclusion (hmono hij) x))
      (i : ℕ) (x : F i) : lift a (x : AlgebraicClosure ℚ) =
        ((a i x : F i) : AlgebraicClosure ℚ) := by
    let k := max (stage (x : AlgebraicClosure ℚ)) i
    have hleft := congrArg (fun z : F k => (z : AlgebraicClosure ℚ))
      (ha (stage (x : AlgebraicClosure ℚ)) k (Nat.le_max_left _ _)
        ⟨(x : AlgebraicClosure ℚ), hstage (x : AlgebraicClosure ℚ)⟩)
    have hright := congrArg (fun z : F k => (z : AlgebraicClosure ℚ))
      (ha i k (Nat.le_max_right _ _) x)
    exact hleft.trans hright.symm
  have hinv (i j : ℕ) (hij : i ≤ j) (x : F i) :
      IntermediateField.inclusion (hmono hij) ((g i).symm x) =
        (g j).symm (IntermediateField.inclusion (hmono hij) x) := by
    apply (g j).injective
    simpa using (hcompat i j hij ((g i).symm x)).symm
  let t := lift g
  let u := lift (fun i => (g i).symm)
  have ht (i : ℕ) (x : F i) :
      t (x : AlgebraicClosure ℚ) = ((g i x : F i) : AlgebraicClosure ℚ) :=
    hlift g hcompat i x
  have hu (i : ℕ) (x : F i) :
      u (x : AlgebraicClosure ℚ) = (((g i).symm x : F i) : AlgebraicClosure ℚ) :=
    hlift (fun i => (g i).symm) hinv i x
  have hleft (x : AlgebraicClosure ℚ) : u (t x) = x := by
    obtain ⟨i, hi⟩ := hcover x
    rw [ht i ⟨x, hi⟩, hu i (g i ⟨x, hi⟩), (g i).symm_apply_apply]
  have hright (x : AlgebraicClosure ℚ) : t (u x) = x := by
    obtain ⟨i, hi⟩ := hcover x
    rw [hu i ⟨x, hi⟩, ht i ((g i).symm ⟨x, hi⟩), (g i).apply_symm_apply]
  have hcommon (x y : AlgebraicClosure ℚ) : ∃ i, x ∈ F i ∧ y ∈ F i := by
    obtain ⟨i, hi⟩ := hcover x
    obtain ⟨j, hj⟩ := hcover y
    exact ⟨max i j, hmono (Nat.le_max_left _ _) hi,
      hmono (Nat.le_max_right _ _) hj⟩
  refine ⟨{
    toFun := t
    invFun := u
    left_inv := hleft
    right_inv := hright
    map_mul' := ?_
    map_add' := ?_
    commutes' := ?_ }, ht⟩
  · intro x y
    obtain ⟨i, hx, hy⟩ := hcommon x y
    change t (((⟨x, hx⟩ : F i) * ⟨y, hy⟩ : F i) : AlgebraicClosure ℚ) = _
    rw [ht, map_mul, IntermediateField.coe_mul, ht i ⟨x, hx⟩, ht i ⟨y, hy⟩]
  · intro x y
    obtain ⟨i, hx, hy⟩ := hcommon x y
    change t (((⟨x, hx⟩ : F i) + ⟨y, hy⟩ : F i) : AlgebraicClosure ℚ) = _
    rw [ht, map_add, IntermediateField.coe_add, ht i ⟨x, hx⟩, ht i ⟨y, hy⟩]
  · intro r
    change t ((algebraMap ℚ (F 0) r : F 0) : AlgebraicClosure ℚ) = _
    rw [ht, (g 0).commutes]
    rfl
theorem Submission.p09_af497904fe_ftl_normal_frobenius_restriction :
    ∀ (E F : IntermediateField ℚ (AlgebraicClosure ℚ)) [IsGalois ℚ E]
      (hEF : E ≤ F) (V : ValuationSubring E) (W : ValuationSubring F) (ℓ : ℕ),
      (∀ x : E, IntermediateField.inclusion hEF x ∈ W ↔ x ∈ V) →
      ∀ g : F ≃ₐ[ℚ] F, W.IsFrobeniusAt g ℓ →
        ∃! e : E ≃ₐ[ℚ] E, V.IsFrobeniusAt e ℓ ∧
          ∀ x : E, IntermediateField.inclusion hEF (e x) =
            g (IntermediateField.inclusion hEF x) := by
  intro E F _ hEF V W ℓ hVW g hg
  let : Algebra E F := (IntermediateField.inclusion hEF).toRingHom.toAlgebra
  let : IsScalarTower ℚ E F := IsScalarTower.of_algHom (IntermediateField.inclusion hEF)
  let e : E ≃ₐ[ℚ] E := g.restrictNormal E
  have he (x : E) : IntermediateField.inclusion hEF (e x) =
      g (IntermediateField.inclusion hEF x) := g.restrictNormal_commutes E x
  let d : W.decompositionSubgroup ℚ := ⟨g, hg.mem_decompositionSubgroup⟩
  have hgmem (x : F) : g x ∈ W ↔ x ∈ W := by
    constructor
    · intro hx
      have h := (d⁻¹ • (⟨g x, hx⟩ : W)).property
      change g.symm (g x) ∈ W at h
      simpa only [g.symm_apply_apply] using h
    · intro hx
      exact (d • (⟨x, hx⟩ : W)).property
  have hemem (x : E) : e x ∈ V ↔ x ∈ V := by
    rw [← hVW, he, hgmem, hVW]
  have heV : e ∈ V.decompositionSubgroup ℚ := by
    apply SetLike.ext
    intro x
    change (∃ y : E, y ∈ V ∧ e y = x) ↔ x ∈ V
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (hemem y).mpr hy
    · intro hx
      refine ⟨e.symm x, (hemem _).mp ?_, e.apply_symm_apply x⟩
      simpa only [e.apply_symm_apply] using hx
  have hnon (x : E) : IntermediateField.inclusion hEF x ∈ W.nonunits ↔
      x ∈ V.nonunits := by
    rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or,
      map_eq_zero_iff _ (IntermediateField.inclusion_injective hEF), ← map_inv₀, hVW]
  refine ⟨e, ⟨⟨heV, ?_⟩, he⟩, ?_⟩
  · intro z
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective z
    rw [← IsLocalRing.ResidueField.residue_smul, ← map_pow, ← sub_eq_zero, ← map_sub,
      IsLocalRing.residue_eq_zero_iff]
    apply ValuationSubring.coe_mem_nonunits_iff.mp
    apply (hnon _).mp
    let y : W := ⟨IntermediateField.inclusion hEF (x : E), (hVW _).mpr x.property⟩
    have hy : IsLocalRing.residue W (d • y - y ^ ℓ) = 0 := by
      rw [map_sub, map_pow, IsLocalRing.ResidueField.residue_smul]
      exact sub_eq_zero.mpr (hg.smul_residue_eq _)
    have hy' := ValuationSubring.coe_mem_nonunits_iff.mpr
      ((IsLocalRing.residue_eq_zero_iff _).mp hy)
    change g (IntermediateField.inclusion hEF (x : E)) -
      (IntermediateField.inclusion hEF (x : E)) ^ ℓ ∈ W.nonunits at hy'
    change IntermediateField.inclusion hEF (e (x : E) - (x : E) ^ ℓ) ∈ W.nonunits
    simpa only [map_sub, map_pow, he] using hy'
  · intro e' he'
    apply AlgEquiv.ext
    intro x
    apply IntermediateField.inclusion_injective hEF
    exact (he'.2 x).trans (he x).symm
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
theorem Submission.p09_af497904fe_ic_integer_mem_valuation :
    ∀ (E : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ E]
      (V : ValuationSubring E), ∀ a : NumberField.RingOfIntegers E, (a : E) ∈ V := by
  intro E _ V a
  apply (Subring.isIntegrallyClosed_iff (S := V)).mp inferInstance
  exact (NumberField.RingOfIntegers.isIntegral_coe a).tower_top
theorem Submission.p09_af497904fe_ic_prime_center_of_containment :
    ∀ (E : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ E]
      (ℓ : ℕ), ℓ.Prime → ∀ (V : ValuationSubring E), V.LiesOverPrime ℓ →
      (∀ a : NumberField.RingOfIntegers E, (a : E) ∈ V) →
      ∃ q : Ideal (NumberField.RingOfIntegers E),
        q.IsPrime ∧ q ≠ ⊥ ∧ (ℓ : NumberField.RingOfIntegers E) ∈ q ∧
        Finite (NumberField.RingOfIntegers E ⧸ q) ∧
        (∀ a : NumberField.RingOfIntegers E, (a : E) ∈ V.nonunits ↔ a ∈ q) := by
  intro E _ ℓ hℓ V hV hcontain
  let : NumberField E := NumberField.of_module_finite ℚ E
  letI : NumberField E := NumberField.of_module_finite ℚ E
  let f : NumberField.RingOfIntegers E →+* V :=
    { toFun := fun a => ⟨(a : E), hcontain a⟩
      map_zero' := Subtype.ext (map_zero (algebraMap (NumberField.RingOfIntegers E) E))
      map_one' := Subtype.ext (map_one (algebraMap (NumberField.RingOfIntegers E) E))
      map_add' := fun a b =>
        Subtype.ext (map_add (algebraMap (NumberField.RingOfIntegers E) E) a b)
      map_mul' := fun a b =>
        Subtype.ext (map_mul (algebraMap (NumberField.RingOfIntegers E) E) a b) }
  let q : Ideal (NumberField.RingOfIntegers E) :=
    Ideal.comap f (IsLocalRing.maximalIdeal V)
  have hprime : q.IsPrime := (IsLocalRing.maximalIdeal V).comap_isPrime f
  have hmem (a : NumberField.RingOfIntegers E) :
      (a : E) ∈ V.nonunits ↔ a ∈ q :=
    ValuationSubring.coe_mem_nonunits_iff (a := f a)
  have hℓq : (ℓ : NumberField.RingOfIntegers E) ∈ q := by
    apply (hmem _).mp
    simpa only [ValuationSubring.LiesOverPrime, NumberField.RingOfIntegers.val,
      map_natCast] using hV
    simpa only [NumberField.RingOfIntegers.val, map_natCast] using hV
  have hne : q ≠ ⊥ := by
    intro hq
    have hz : (ℓ : NumberField.RingOfIntegers E) = 0 := by
      simpa only [hq, Ideal.mem_bot] using hℓq
    exact hℓ.ne_zero (Nat.cast_eq_zero.mp hz)
  exact ⟨q, hprime, hne, hℓq, Ring.HasFiniteQuotients.finiteQuotient hne, hmem⟩
theorem Submission.p09_af497904fe_fvu_compatible_valuation_gluing :
    ∀ (F : ℕ → IntermediateField ℚ (AlgebraicClosure ℚ)) (hmono : Monotone F),
      (∀ x : AlgebraicClosure ℚ, ∃ i : ℕ, x ∈ F i) →
      ∀ (V : (i : ℕ) → ValuationSubring (F i)) (ℓ : ℕ),
        (∀ i : ℕ, (V i).LiesOverPrime ℓ) →
        (∀ (i j : ℕ) (hij : i ≤ j) (x : F i),
          IntermediateField.inclusion (hmono hij) x ∈ V j ↔ x ∈ V i) →
        ∃ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ ∧
          (∀ (i : ℕ) (x : F i), (x : AlgebraicClosure ℚ) ∈ P ↔ x ∈ V i) := by
  intro F hmono hexhaust V ℓ hprime hcompat
  let P : ValuationSubring (AlgebraicClosure ℚ) :=
    { carrier := {z | ∃ (i : ℕ) (x : F i), x ∈ V i ∧ (x : AlgebraicClosure ℚ) = z}
      zero_mem' := ⟨0, 0, (V 0).zero_mem, rfl⟩
      one_mem' := ⟨0, 1, (V 0).one_mem, rfl⟩
      add_mem' := by
        rintro a b ⟨i, x, hx, rfl⟩ ⟨j, y, hy, rfl⟩
        refine ⟨max i j,
          IntermediateField.inclusion (hmono (le_max_left i j)) x +
            IntermediateField.inclusion (hmono (le_max_right i j)) y, ?_, rfl⟩
        exact (V (max i j)).add_mem _ _
          ((hcompat i (max i j) (le_max_left i j) x).mpr hx)
          ((hcompat j (max i j) (le_max_right i j) y).mpr hy)
      mul_mem' := by
        rintro a b ⟨i, x, hx, rfl⟩ ⟨j, y, hy, rfl⟩
        refine ⟨max i j,
          IntermediateField.inclusion (hmono (le_max_left i j)) x *
            IntermediateField.inclusion (hmono (le_max_right i j)) y, ?_, rfl⟩
        exact (V (max i j)).mul_mem _ _
          ((hcompat i (max i j) (le_max_left i j) x).mpr hx)
          ((hcompat j (max i j) (le_max_right i j) y).mpr hy)
      neg_mem' := by
        rintro a ⟨i, x, hx, rfl⟩
        exact ⟨i, -x, (V i).neg_mem x hx, rfl⟩
      mem_or_inv_mem' := by
        intro z
        obtain ⟨i, hi⟩ := hexhaust z
        rcases (V i).mem_or_inv_mem ⟨z, hi⟩ with hz | hz
        · exact Or.inl ⟨i, ⟨z, hi⟩, hz, rfl⟩
        · exact Or.inr ⟨i, (⟨z, hi⟩ : F i)⁻¹, hz, rfl⟩ }
  have hrestrict (i : ℕ) (x : F i) :
      (x : AlgebraicClosure ℚ) ∈ P ↔ x ∈ V i := by
    change (∃ (j : ℕ) (y : F j), y ∈ V j ∧
      (y : AlgebraicClosure ℚ) = (x : AlgebraicClosure ℚ)) ↔ x ∈ V i
    constructor
    · rintro ⟨j, y, hy, heq⟩
      have heq' : IntermediateField.inclusion (hmono (le_max_left i j)) x =
          IntermediateField.inclusion (hmono (le_max_right i j)) y :=
        Subtype.ext heq.symm
      apply (hcompat i (max i j) (le_max_left i j) x).mp
      rw [heq']
      exact (hcompat j (max i j) (le_max_right i j) y).mpr hy
    · intro hx
      exact ⟨i, x, hx, rfl⟩
  have hnonunits (i : ℕ) (x : F i) :
      (x : AlgebraicClosure ℚ) ∈ P.nonunits ↔ x ∈ (V i).nonunits := by
    rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or]
    change ((x : AlgebraicClosure ℚ) = 0 ∨ ((x⁻¹ : F i) : AlgebraicClosure ℚ) ∉ P) ↔
      x = 0 ∨ x⁻¹ ∉ V i
    rw [hrestrict]
    exact or_congr (by exact_mod_cast (Iff.rfl : x = 0 ↔ x = 0)) Iff.rfl
  refine ⟨P, ?_, hrestrict⟩
  change (ℓ : AlgebraicClosure ℚ) ∈ P.nonunits
  exact (hnonunits 0 (ℓ : F 0)).mpr (hprime 0)
theorem Submission.p09_af497904fe_ce_fixed_field_generator :
    ∀ (M : IntermediateField ℚ (AlgebraicClosure ℚ))
      [FiniteDimensional ℚ M] [IsGalois ℚ M] (u : M ≃ₐ[ℚ] M) (ζ : M),
      (∀ n : ℕ, (u ^ n) ζ = ζ → u ^ n = 1) →
      ∃ (F : IntermediateField ℚ M) (h : M ≃ₐ[F] M),
        IntermediateField.adjoin F ({ζ} : Set M) = ⊤ ∧ ∀ x : M, h x = u x := by
  intro M _ _ u ζ hu
  let F := IntermediateField.fixedField (Subgroup.zpowers u)
  let h : M ≃ₐ[F] M :=
    { u.toRingEquiv with
      commutes' := fun x =>
        (IntermediateField.mem_fixedField_iff _ _).mp x.property u (Subgroup.mem_zpowers u) }
  let K := IntermediateField.adjoin F ({ζ} : Set M)
  have hfix : (K.restrictScalars ℚ).fixingSubgroup = ⊥ := by
    apply le_antisymm ?_ bot_le
    intro σ hσ
    rw [Subgroup.mem_bot]
    have hσF : σ ∈ F.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff] at hσ ⊢
      intro x hx
      exact hσ x (K.algebraMap_mem ⟨x, hx⟩)
    have hσH : σ ∈ Subgroup.zpowers u := by
      simpa only [F, IntermediateField.fixingSubgroup_fixedField] using hσF
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp
      (mem_powers_iff_mem_zpowers.mpr hσH)
    have hσζ := (IntermediateField.mem_fixingSubgroup_iff _ _).mp hσ ζ
      (IntermediateField.mem_adjoin_simple_self F ζ)
    rw [← hn] at hσζ ⊢
    exact hu n hσζ
  refine ⟨F, h, ?_, fun _ => rfl⟩
  apply (IntermediateField.restrictScalars_eq_top_iff (K := ℚ)).mp
  change K.restrictScalars ℚ = ⊤
  rw [← IsGalois.fixedField_fixingSubgroup (K.restrictScalars ℚ), hfix,
    IntermediateField.fixedField_bot]
theorem Submission.p09_af497904fe_fvu_frobenius_from_exhaustive_restrictions :
    ∀ (F : ℕ → IntermediateField ℚ (AlgebraicClosure ℚ)),
      (∀ x : AlgebraicClosure ℚ, ∃ i : ℕ, x ∈ F i) →
      ∀ (V : (i : ℕ) → ValuationSubring (F i))
        (P : ValuationSubring (AlgebraicClosure ℚ)),
      (∀ (i : ℕ) (x : F i), (x : AlgebraicClosure ℚ) ∈ P ↔ x ∈ V i) →
      ∀ (ℓ : ℕ) (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
      (∀ i : ℕ, ∃ g : F i ≃ₐ[ℚ] F i, (V i).IsFrobeniusAt g ℓ ∧
        ∀ x : F i, τ (x : AlgebraicClosure ℚ) =
          ((g x : F i) : AlgebraicClosure ℚ)) → P.IsFrobeniusAt τ ℓ := by
  intro F hF V P hV ℓ τ h
  classical
  choose g hg hagree using h
  let d (i : ℕ) : (V i).decompositionSubgroup ℚ :=
    ⟨g i, (hg i).mem_decompositionSubgroup⟩
  have hinv (i : ℕ) (x : F i) :
      τ.symm (x : AlgebraicClosure ℚ) =
        ((g i).symm x : AlgebraicClosure ℚ) := by
    apply τ.injective
    rw [τ.apply_symm_apply, hagree, (g i).apply_symm_apply]
  have hforward (z : AlgebraicClosure ℚ) (hz : z ∈ P) : τ z ∈ P := by
    obtain ⟨i, hi⟩ := hF z
    let x : F i := ⟨z, hi⟩
    rw [hagree i x]
    apply (hV i (g i x)).mpr
    exact (d i • (⟨x, (hV i x).mp hz⟩ : V i) : V i).property
  have hbackward (z : AlgebraicClosure ℚ) (hz : z ∈ P) : τ.symm z ∈ P := by
    obtain ⟨i, hi⟩ := hF z
    let x : F i := ⟨z, hi⟩
    rw [hinv i x]
    apply (hV i ((g i).symm x)).mpr
    exact ((d i)⁻¹ • (⟨x, (hV i x).mp hz⟩ : V i) : V i).property
  have hτ : τ ∈ P.decompositionSubgroup ℚ := by
    let : MulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
        (ValuationSubring (AlgebraicClosure ℚ)) := ValuationSubring.pointwiseMulAction
    apply MulAction.mem_stabilizer_iff.mpr
    apply le_antisymm
    · intro z hz
      obtain ⟨x, hx, rfl⟩ := (ValuationSubring.mem_smul_pointwise_iff_exists τ z P).mp hz
      exact hforward x hx
    · intro z hz
      apply (ValuationSubring.mem_smul_pointwise_iff_exists τ z P).mpr
      exact ⟨τ.symm z, hbackward z hz, τ.apply_symm_apply z⟩
  have hnonunits (i : ℕ) (x : F i) :
      (x : AlgebraicClosure ℚ) ∈ P.nonunits ↔ x ∈ (V i).nonunits := by
    rw [P.mem_nonunits_iff_or, (V i).mem_nonunits_iff_or]
    apply or_congr
    · exact ⟨fun hx => Subtype.ext hx, fun hx => congrArg Subtype.val hx⟩
    · exact not_congr (hV i (x⁻¹))
  have hdifference (z : P) : τ (z : AlgebraicClosure ℚ) -
      (z : AlgebraicClosure ℚ) ^ ℓ ∈ P.nonunits := by
    obtain ⟨i, hi⟩ := hF (z : AlgebraicClosure ℚ)
    let x : F i := ⟨z, hi⟩
    let y : V i := ⟨x, (hV i x).mp z.property⟩
    have hres : residue (V i) (d i • y - y ^ ℓ) = 0 := by
      rw [map_sub, ResidueField.residue_smul, map_pow]
      exact sub_eq_zero.mpr ((hg i).smul_residue_eq (residue (V i) y))
    have hnon : (g i x - x ^ ℓ : F i) ∈ (V i).nonunits :=
      ValuationSubring.coe_mem_nonunits_iff.mpr ((residue_eq_zero_iff _).mp hres)
    have htransport := (hnonunits i (g i x - x ^ ℓ)).mpr hnon
    change (g i x : AlgebraicClosure ℚ) - (x : AlgebraicClosure ℚ) ^ ℓ ∈
      P.nonunits at htransport
    rw [← hagree i x] at htransport
    exact htransport
  refine ⟨hτ, ?_⟩
  intro a
  obtain ⟨z, rfl⟩ := residue_surjective a
  let t : P.decompositionSubgroup ℚ := ⟨τ, hτ⟩
  have hzero : residue P (t • z - z ^ ℓ) = 0 :=
    (residue_eq_zero_iff _).mpr (ValuationSubring.coe_mem_nonunits_iff.mp (hdifference z))
  rw [map_sub, ResidueField.residue_smul, map_pow] at hzero
  exact sub_eq_zero.mp hzero


theorem Submission.p09_af497904fe_vloc_integral_center :
    ∀ (E : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ E]
      (ℓ : ℕ), ℓ.Prime → ∀ (V : ValuationSubring E), V.LiesOverPrime ℓ →
      (∀ a : NumberField.RingOfIntegers E, (a : E) ∈ V) ∧
        ∃ q : Ideal (NumberField.RingOfIntegers E),
          q.IsPrime ∧ q ≠ ⊥ ∧ (ℓ : NumberField.RingOfIntegers E) ∈ q ∧
            Finite (NumberField.RingOfIntegers E ⧸ q) ∧
            (∀ a : NumberField.RingOfIntegers E, (a : E) ∈ V.nonunits ↔ a ∈ q) := by
  intro E _ ℓ hℓ V hV
  have hmem := Submission.p09_af497904fe_ic_integer_mem_valuation E V
  exact ⟨hmem, Submission.p09_af497904fe_ic_prime_center_of_containment E ℓ hℓ V hV hmem⟩
theorem Submission.p09_af497904fe_fie_integral_primitive :
    ∀ (E : IntermediateField ℚ (AlgebraicClosure ℚ))
      [FiniteDimensional ℚ E] [IsGalois ℚ E],
      ∃ α : E, IsIntegral ℤ α ∧ IntermediateField.adjoin ℚ ({α} : Set E) = ⊤ := by
  intro E _ _
  obtain ⟨θ, hθ⟩ := Field.exists_primitive_element ℚ E
  obtain ⟨m, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
    (nonZeroDivisors ℤ) θ (IsIntegral.of_finite ℚ θ)
  refine ⟨(m : ℤ) • θ, hm, ?_⟩
  apply top_unique
  rw [← hθ]
  apply IntermediateField.adjoin_simple_le_iff.mpr
  let F := IntermediateField.adjoin ℚ ({(m : ℤ) • θ} : Set E)
  have hm0 : ((m : ℤ) : E) ≠ 0 :=
    Int.cast_ne_zero.mpr (nonZeroDivisors.coe_ne_zero m)
  have hrecover : ((m : ℤ) : E)⁻¹ * ((m : ℤ) • θ) = θ := by
    rw [zsmul_eq_mul, inv_mul_cancel_left₀ hm0]
  change θ ∈ F
  rw [← hrecover]
  exact F.mul_mem (F.inv_mem (F.intCast_mem (m : ℤ)))
    (IntermediateField.mem_adjoin_simple_self ℚ ((m : ℤ) • θ))
theorem Submission.p09_af497904fe_cfs_bounded_euler_logarithm :
    ∀ (E L : ℝ → ℂ), ContinuousOn E (Set.Ioo 1 2) →
      ContinuousWithinAt L (Set.Ici 1) 1 → L 1 ≠ 0 →
      (∀ s : ℝ, s ∈ Set.Ioo 1 2 → Complex.exp (E s) = L s) →
      ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∃ C : ℝ, 0 ≤ C ∧
        ∀ s : ℝ, 1 < s → s < 1 + ε → ‖E s‖ ≤ C := by
  intro E L hE hL hL₁ hexp
  let N : ℝ → ℂ := fun s => L s / L 1
  have hN₁ : N 1 = 1 := div_self hL₁
  have hN : ContinuousWithinAt N (Set.Ici 1) 1 := hL.div_const (L 1)
  have hslit₁ : N 1 ∈ Complex.slitPlane := by rw [hN₁]; exact Complex.one_mem_slitPlane
  have hlog : ContinuousWithinAt (fun s => Complex.log (N s)) (Set.Ici 1) 1 :=
    hN.clog hslit₁
  have hev : ∀ᶠ s in nhdsWithin 1 (Set.Ici 1),
      N s ∈ Complex.slitPlane ∧ ‖Complex.log (N s)‖ < 1 := by
    have ha := hN.preimage_mem_nhdsWithin (Complex.isOpen_slitPlane.mem_nhds hslit₁)
    have hb := hlog.norm.eventually (gt_mem_nhds (show ‖Complex.log (N 1)‖ < 1 by
      simp [hN₁]))
    exact Filter.Eventually.and ha hb
  obtain ⟨δ, hδ, hδprop⟩ := Metric.mem_nhdsWithin_iff.mp hev
  let ε := min δ 1
  have hε : 0 < ε := lt_min hδ zero_lt_one
  have hε₁ : ε ≤ 1 := min_le_right _ _
  have hsmall (s : ℝ) (hs : s ∈ Set.Ioo 1 (1 + ε)) :
      N s ∈ Complex.slitPlane ∧ ‖Complex.log (N s)‖ < 1 := by
    apply hδprop
    refine ⟨?_, le_of_lt hs.1⟩
    change dist s 1 < δ
    rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hs.1)]
    have : ε ≤ δ := min_le_left _ _
    linarith [hs.2]
  have hsub : Set.Ioo 1 (1 + ε) ⊆ Set.Ioo (1 : ℝ) 2 := by
    intro s hs
    exact ⟨hs.1, by linarith [hs.2]⟩
  have hLc : ContinuousOn L (Set.Ioo 1 (1 + ε)) :=
    (Complex.continuous_exp.comp_continuousOn (hE.mono hsub)).congr
      (fun s hs => (hexp s (hsub hs)).symm)
  let H : ℝ → ℂ := fun s => Complex.log (L 1) + Complex.log (N s)
  have hH : ContinuousOn H (Set.Ioo 1 (1 + ε)) :=
    continuousOn_const.add ((hLc.div_const (L 1)).clog (fun s hs => (hsmall s hs).1))
  have hHexp (s : ℝ) (hs : s ∈ Set.Ioo 1 (1 + ε)) : Complex.exp (H s) = L s := by
    dsimp [H]
    rw [Complex.exp_add, Complex.exp_log hL₁,
      Complex.exp_log (Complex.slitPlane_ne_zero (hsmall s hs).1)]
    dsimp [N]
    exact mul_div_cancel₀ (L s) hL₁
  let D : ℝ → ℂ := fun s => E s - H s
  have hD : ContinuousOn D (Set.Ioo 1 (1 + ε)) := (hE.mono hsub).sub hH
  have hDexp (s : ℝ) (hs : s ∈ Set.Ioo 1 (1 + ε)) : Complex.exp (D s) = 1 :=
    Complex.exp_eq_exp_iff_exp_sub_eq_one.mp ((hexp s (hsub hs)).trans (hHexp s hs).symm)
  have hcount : (Complex.exp ⁻¹' ({1} : Set ℂ)).Countable :=
    (Set.countable_singleton (1 : ℂ)).preimage_cexp
  have himage : (D '' Set.Ioo 1 (1 + ε)).Subsingleton := by
    apply hcount.isTotallyDisconnected
    · rintro z ⟨s, hs, rfl⟩
      exact hDexp s hs
    · exact isPreconnected_Ioo.image D hD
  let s₀ : ℝ := 1 + ε / 2
  have hs₀ : s₀ ∈ Set.Ioo 1 (1 + ε) := by
    dsimp [s₀]
    constructor <;> linarith
  refine ⟨ε, hε, hε₁, ‖Complex.log (L 1)‖ + 1 + ‖D s₀‖, by positivity, ?_⟩
  intro s hs hs'
  have hmem : s ∈ Set.Ioo 1 (1 + ε) := ⟨hs, hs'⟩
  have hconst : D s = D s₀ := himage ⟨s, hmem, rfl⟩ ⟨s₀, hs₀, rfl⟩
  have hdecomp : E s = H s + D s₀ := by rw [← hconst]; dsimp [D]; ring
  calc
    ‖E s‖ = ‖H s + D s₀‖ := congrArg norm hdecomp
    _ ≤ ‖H s‖ + ‖D s₀‖ := norm_add_le _ _
    _ ≤ ‖Complex.log (L 1)‖ + 1 + ‖D s₀‖ := by
      have hbound := norm_add_le (Complex.log (L 1)) (Complex.log (N s))
      dsimp [H]
      linarith [(hsmall s hmem).2]
theorem Submission.p09_af497904fe_ftl_frobenius_valuation_union :
    ∀ (F : ℕ → IntermediateField ℚ (AlgebraicClosure ℚ)) (hmono : Monotone F),
      (∀ x : AlgebraicClosure ℚ, ∃ i : ℕ, x ∈ F i) →
      ∀ (V : (i : ℕ) → ValuationSubring (F i)) (ℓ : ℕ),
        (∀ i : ℕ, (V i).LiesOverPrime ℓ) →
        (∀ (i j : ℕ) (hij : i ≤ j) (x : F i),
          IntermediateField.inclusion (hmono hij) x ∈ V j ↔ x ∈ V i) →
        ∀ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
          (∀ i : ℕ, ∃ g : F i ≃ₐ[ℚ] F i, (V i).IsFrobeniusAt g ℓ ∧
            ∀ x : F i,
              τ (x : AlgebraicClosure ℚ) = ((g x : F i) : AlgebraicClosure ℚ)) →
          ∃ P : ValuationSubring (AlgebraicClosure ℚ),
            P.LiesOverPrime ℓ ∧
              (∀ (i : ℕ) (x : F i), (x : AlgebraicClosure ℚ) ∈ P ↔ x ∈ V i) ∧
              P.IsFrobeniusAt τ ℓ := by
  intro F hmono hexhaust V ℓ hprime hcompat τ hfrob
  obtain ⟨P, hPprime, hrestrict⟩ :=
    Submission.p09_af497904fe_fvu_compatible_valuation_gluing
      F hmono hexhaust V ℓ hprime hcompat
  exact ⟨P, hPprime, hrestrict,
    Submission.p09_af497904fe_fvu_frobenius_from_exhaustive_restrictions
      F hexhaust V P hrestrict ℓ τ hfrob⟩
theorem Submission.p09_af497904fe_ce_compositum_pair :
    ∀ (E C : IntermediateField ℚ (AlgebraicClosure ℚ))
      [FiniteDimensional ℚ E] [IsGalois ℚ E]
      [FiniteDimensional ℚ C] [IsGalois ℚ C], E ⊓ C = ⊥ →
      ∀ (g : E ≃ₐ[ℚ] E) (a : C ≃ₐ[ℚ] C),
      ∃! h : ↥(E ⊔ C) ≃ₐ[ℚ] ↥(E ⊔ C),
        (∀ x : E, h (IntermediateField.inclusion (show E ≤ E ⊔ C from le_sup_left) x) =
          IntermediateField.inclusion (show E ≤ E ⊔ C from le_sup_left) (g x)) ∧
        (∀ y : C, h (IntermediateField.inclusion (show C ≤ E ⊔ C from le_sup_right) y) =
          IntermediateField.inclusion (show C ≤ E ⊔ C from le_sup_right) (a y)) := by
  intro E C hfinE hgalE hfinC hgalC hEC g a
  classical
  have hdegree : Module.finrank ℚ ↥(E ⊔ C) =
      Module.finrank ℚ E * Module.finrank ℚ C :=
    (@IntermediateField.LinearDisjoint.of_inf_eq_bot ℚ (AlgebraicClosure ℚ)
      _ _ _ E C hgalE hfinE hfinC hEC).finrank_sup
  let M := E ⊔ C
  let iE : E →ₐ[ℚ] M := IntermediateField.inclusion le_sup_left
  let iC : C →ₐ[ℚ] M := IntermediateField.inclusion le_sup_right
  let := iE.toAlgebra
  let := iC.toAlgebra
  have : IsScalarTower ℚ E M := IsScalarTower.of_algHom iE
  have : IsScalarTower ℚ C M := IsScalarTower.of_algHom iC
  have : IsGalois ℚ M :=
    { to_isSeparable := inferInstance
      to_normal := @IntermediateField.normal_sup ℚ (AlgebraicClosure ℚ)
        _ _ _ E C hgalE.to_normal hgalC.to_normal }
  let R : (M ≃ₐ[ℚ] M) →* (E ≃ₐ[ℚ] E) × (C ≃ₐ[ℚ] C) :=
    (AlgEquiv.restrictNormalHom E).prod (AlgEquiv.restrictNormalHom C)
  have hE (h : M ≃ₐ[ℚ] M) (x : E) :
      iE (h.restrictNormal E x) = h (iE x) := h.restrictNormal_commutes E x
  have hC (h : M ≃ₐ[ℚ] M) (y : C) :
      iC (h.restrictNormal C y) = h (iC y) := h.restrictNormal_commutes C y
  let E' : IntermediateField ℚ M := E.restrict le_sup_left
  let C' : IntermediateField ℚ M := C.restrict le_sup_right
  have hsup : E' ⊔ C' = ⊤ := by
    apply (IntermediateField.lift_inj (F := M) (E' ⊔ C') ⊤).mp
    rw [IntermediateField.lift_sup, IntermediateField.lift_top,
      IntermediateField.lift_restrict le_sup_left,
      IntermediateField.lift_restrict le_sup_right]
  -- An automorphism fixing both fields fixes their compositum.
  have hinj : Function.Injective R := by
    apply (injective_iff_map_eq_one R).2
    intro h hh
    have he : h.restrictNormal E = 1 := congrArg Prod.fst hh
    have hc : h.restrictNormal C = 1 := congrArg Prod.snd hh
    rw [← Subgroup.mem_bot, ← IntermediateField.fixingSubgroup_top,
      ← hsup, IntermediateField.fixingSubgroup_sup]
    constructor
    · intro x
      let z : E := ⟨x.1.1, (IntermediateField.mem_restrict le_sup_left x.1).1 x.2⟩
      have hz : iE z = x.1 := by
        apply Subtype.ext
        rfl
      simpa only [he, AlgEquiv.one_apply, hz, AlgEquiv.smul_def] using (hE h z).symm
    · intro y
      let z : C := ⟨y.1.1, (IntermediateField.mem_restrict le_sup_right y.1).1 y.2⟩
      have hz : iC z = y.1 := by
        apply Subtype.ext
        rfl
      simpa only [hc, AlgEquiv.one_apply, hz, AlgEquiv.smul_def] using (hC h z).symm
  -- The disjoint Galois degree formula makes paired restriction bijective.
  have hcard : Nat.card (M ≃ₐ[ℚ] M) = Nat.card ((E ≃ₐ[ℚ] E) × (C ≃ₐ[ℚ] C)) := by
    rw [Nat.card_prod, IsGalois.card_aut_eq_finrank,
      IsGalois.card_aut_eq_finrank, IsGalois.card_aut_eq_finrank]
    exact hdegree
  obtain ⟨h, hh⟩ := ((Nat.bijective_iff_injective_and_card R).2 ⟨hinj, hcard⟩).2 (g, a)
  have he : h.restrictNormal E = g := congrArg Prod.fst hh
  have hc : h.restrictNormal C = a := congrArg Prod.snd hh
  refine ⟨h, ⟨?_, ?_⟩, ?_⟩
  · intro x
    exact (hE h x).symm.trans (congrArg (fun e : E ≃ₐ[ℚ] E => iE (e x)) he)
  · intro y
    exact (hC h y).symm.trans (congrArg (fun e : C ≃ₐ[ℚ] C => iC (e y)) hc)
  · intro k hk
    apply hinj
    apply Prod.ext
    · change k.restrictNormal E = h.restrictNormal E
      rw [he]
      apply AlgEquiv.ext
      intro x
      apply iE.injective
      exact (hE k x).trans (hk.1 x)
    · change k.restrictNormal C = h.restrictNormal C
      rw [hc]
      apply AlgEquiv.ext
      intro y
      apply iC.injective
      exact (hC k y).trans (hk.2 y)
