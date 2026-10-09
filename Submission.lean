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
theorem Submission.p09_af497904fe_luf_valuation_localization :
    ∀ (E : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ E] (ℓ : ℕ),
      ℓ.Prime → ∀ (V : ValuationSubring E), V.LiesOverPrime ℓ →
      ∃ q : Ideal (NumberField.RingOfIntegers E),
        q.IsPrime ∧ q ≠ ⊥ ∧ (ℓ : NumberField.RingOfIntegers E) ∈ q ∧
        Finite (NumberField.RingOfIntegers E ⧸ q) ∧
        (∀ x : E, x ∈ V ↔ ∃ a b : NumberField.RingOfIntegers E,
          b ∉ q ∧ x = (a : E) / (b : E)) ∧
        (∀ a : NumberField.RingOfIntegers E, (a : E) ∈ V.nonunits ↔ a ∈ q) := by
  intro E _ ℓ hℓ V hV
  obtain ⟨hints, q, hq, hqne, hℓq, hfinite, hcenter⟩ :=
    Submission.p09_af497904fe_vloc_integral_center E ℓ hℓ V hV
  exact ⟨q, hq, hqne, hℓq, hfinite,
    Submission.p09_af497904fe_vloc_fraction_characterization
      E V q hq hqne hints hcenter,
    hcenter⟩


theorem Submission.p09_af497904fe_luf_valuation_extension :
    ∀ (E F : IntermediateField ℚ (AlgebraicClosure ℚ))
      [FiniteDimensional ℚ E] [FiniteDimensional ℚ F] (hEF : E ≤ F) (ℓ : ℕ),
      ℓ.Prime → ∀ (V : ValuationSubring E), V.LiesOverPrime ℓ →
      ∃ W : ValuationSubring F, W.LiesOverPrime ℓ ∧
        ∀ x : E, IntermediateField.inclusion hEF x ∈ W ↔ x ∈ V := by
  intro E F _ _ hEF ℓ hℓ V hV
  classical
  let : NumberField E := NumberField.of_module_finite ℚ E
  let : NumberField F := NumberField.of_module_finite ℚ F
  obtain ⟨q, hq, _, hℓq, _, hfrac, hnonunits⟩ :=
    Submission.p09_af497904fe_luf_valuation_localization E ℓ hℓ V hV
  let : q.IsPrime := hq
  let i := IntermediateField.inclusion hEF
  let f := NumberField.RingOfIntegers.mapRingHom i.toRingHom
  let : Algebra (NumberField.RingOfIntegers E) (NumberField.RingOfIntegers F) :=
    f.toAlgebra
  have hf : Function.Injective f := by
    intro a b hab
    apply NumberField.RingOfIntegers.ext
    exact i.injective (congrArg (fun z : NumberField.RingOfIntegers F => (z : F)) hab)
  let : Algebra.IsIntegral (NumberField.RingOfIntegers E) (NumberField.RingOfIntegers F) :=
    ⟨fun a => (NumberField.RingOfIntegers.isIntegral a).tower_top⟩
  obtain ⟨Q, hQ, hQq⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := NumberField.RingOfIntegers F)
      q (by
        intro a ha
        have ha0 : a = 0 := hf (ha.trans f.map_zero.symm)
        simpa only [ha0] using q.zero_mem)
  let : Q.IsPrime := hQ
  have hcontract (a : NumberField.RingOfIntegers E) : f a ∈ Q ↔ a ∈ q := by
    change a ∈ Q.comap f ↔ a ∈ q
    rw [show Q.comap f = q from hQq]
  have hℓQ : (ℓ : NumberField.RingOfIntegers F) ∈ Q := by
    simpa only [map_natCast] using (hcontract (ℓ : NumberField.RingOfIntegers E)).2 hℓq
  have hQzero : Q ≠ ⊥ := by
    intro h
    have hz : (ℓ : NumberField.RingOfIntegers F) = 0 := by simpa [h] using hℓQ
    exact hℓ.ne_zero (Nat.cast_eq_zero.mp hz)
  -- Realize the upper DVR localization as a subalgebra of F.
  let A := Localization.subalgebra.ofField F Q.primeCompl Q.primeCompl_le_nonZeroDivisors
  let : IsDiscreteValuationRing A :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
      (NumberField.RingOfIntegers F) hQzero A
  let v := ValuationRing.valuation A F
  have hA (x : F) : x ∈ v.valuationSubring ↔ x ∈ A := by
    change x ∈ (ValuationRing.valuation A F).integer ↔ x ∈ A
    rw [ValuationRing.range_algebraMap_eq]
    exact ⟨fun ⟨a, ha⟩ => ha ▸ a.property, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
  let W : ValuationSubring F := v.valuationSubring
  have hWfrac (x : F) : x ∈ W ↔
      ∃ a b : NumberField.RingOfIntegers F, b ∉ Q ∧ x = (a : F) / (b : F) := by
    rw [hA x]
    change (∃ (a b : NumberField.RingOfIntegers F) (_ : b ∈ Q.primeCompl),
      x = (a : F) * (b : F)⁻¹) ↔ _
    simp only [Ideal.mem_primeCompl_iff, div_eq_mul_inv, exists_prop]
  have hWnonunits (a : NumberField.RingOfIntegers F) (ha : a ∈ Q) :
      (a : F) ∈ W.nonunits := by
    apply W.mem_nonunits_iff_or.2
    by_cases ha0 : (a : F) = 0
    · exact Or.inl ha0
    · right
      intro hinv
      have hinvA : (a : F)⁻¹ ∈ A := (hA _).1 hinv
      let aA := algebraMap (NumberField.RingOfIntegers F) A a
      have hmax : aA ∈ maximalIdeal A :=
        (IsLocalization.AtPrime.to_map_mem_maximal_iff A Q a).2 ha
      have hunit : IsUnit aA := by
        apply IsUnit.of_mul_eq_one (⟨(a : F)⁻¹, hinvA⟩ : A)
        apply Subtype.ext
        exact mul_inv_cancel₀ ha0
      exact (show ¬ IsUnit aA from hmax) hunit
  have hmul {K : Type} [Field K] (U : ValuationSubring K) {a b : K}
      (ha : a ∈ U.nonunits) (hb : b ∈ U) : a * b ∈ U.nonunits := by
    rw [U.mem_nonunits_iff, map_mul]
    exact (mul_le_mul_of_nonneg_left ((U.valuation_le_one_iff b).2 hb) zero_le).trans_lt
      (by simpa only [mul_one] using (U.mem_nonunits_iff.1 ha))
  have hOE (a : NumberField.RingOfIntegers E) : (a : E) ∈ V :=
    (hfrac _).2 ⟨a, 1, hq.one_notMem, by simp⟩
  have hmaps (x : E) (hx : x ∈ V) : i x ∈ W := by
    obtain ⟨a, b, hb, rfl⟩ := (hfrac x).1 hx
    apply (hWfrac _).2
    refine ⟨f a, f b, fun h => hb ((hcontract b).1 h), ?_⟩
    exact map_div₀ i (a : E) (b : E)
  have hmaps_nonunits (x : E) (hx : x ∈ V.nonunits) : i x ∈ W.nonunits := by
    obtain ⟨a, b, hb, hxab⟩ := (hfrac x).1 (V.nonunits_subset hx)
    have hb0 : (b : E) ≠ 0 := by
      intro h
      exact hb ((NumberField.RingOfIntegers.coe_eq_zero_iff.mp h) ▸ q.zero_mem)
    have ha : a ∈ q := by
      apply (hnonunits a).1
      have h := hmul V hx (hOE b)
      rwa [hxab, div_mul_cancel₀ _ hb0] at h
    have haW : ((f a : NumberField.RingOfIntegers F) : F) ∈ W.nonunits :=
      hWnonunits (f a) ((hcontract a).2 ha)
    have hbW : (((f b : NumberField.RingOfIntegers F) : F))⁻¹ ∈ W := by
      apply (hWfrac _).2
      exact ⟨1, f b, fun h => hb ((hcontract b).1 h), by simp⟩
    rw [hxab, map_div₀, div_eq_mul_inv]
    exact hmul W haW hbW
  refine ⟨W, ?_, ?_⟩
  · exact hWnonunits (ℓ : NumberField.RingOfIntegers F) hℓQ
  · intro x
    refine ⟨fun hx => ?_, hmaps x⟩
    by_contra hxV
    have hx0 : x ≠ 0 := fun h => hxV (h ▸ V.zero_mem)
    have hinv := hmaps_nonunits x⁻¹ (V.inv_mem_nonunits_iff.2 (Or.inr hxV))
    have hn := W.mem_nonunits_iff_or.1 hinv
    rcases hn with hz | hn
    · exact (inv_ne_zero hx0) (i.injective (by simpa using hz))
    · exact hn (by simpa only [map_inv₀, inv_inv] using hx)
theorem Submission.p09_af497904fe_luf_frobenius_tower_limit :
    ∀ (F : ℕ → IntermediateField ℚ (AlgebraicClosure ℚ)) (hmono : Monotone F),
      (∀ i : ℕ, FiniteDimensional ℚ (F i)) →
      (∀ i : ℕ, IsGalois ℚ (F i)) →
      (∀ x : AlgebraicClosure ℚ, ∃ i : ℕ, x ∈ F i) →
      ∀ (V : (i : ℕ) → ValuationSubring (F i)) (ℓ : ℕ),
      (∀ i : ℕ, (V i).LiesOverPrime ℓ) →
      (∀ (i j : ℕ) (hij : i ≤ j) (x : F i),
        IntermediateField.inclusion (hmono hij) x ∈ V j ↔ x ∈ V i) →
      (∀ i : ℕ, ∃ g : F i ≃ₐ[ℚ] F i, (V i).IsFrobeniusAt g ℓ) →
      ∃ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ ∧
        (∀ (i : ℕ) (x : F i), (x : AlgebraicClosure ℚ) ∈ P ↔ x ∈ V i) ∧
        ∃ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
          P.IsFrobeniusAt τ ℓ ∧ ∀ i : ℕ, ∃ g : F i ≃ₐ[ℚ] F i,
            (V i).IsFrobeniusAt g ℓ ∧ ∀ x : F i,
              τ (x : AlgebraicClosure ℚ) = ((g x : F i) : AlgebraicClosure ℚ) := by
  intro F hmono hfin hgal hexhaust V ℓ hprime hV hnonempty
  classical
  let : ∀ i : ℕ, FiniteDimensional ℚ (F i) := hfin
  let : ∀ i : ℕ, IsGalois ℚ (F i) := hgal
  let X : ℕ → Type := fun i => {g : F i ≃ₐ[ℚ] F i // (V i).IsFrobeniusAt g ℓ}
  have : ∀ i : ℕ, Finite (X i) := fun i =>
    inferInstanceAs (Finite {g : F i ≃ₐ[ℚ] F i // (V i).IsFrobeniusAt g ℓ})
  have : ∀ i : ℕ, Nonempty (X i) := fun i => by
    obtain ⟨g, hg⟩ := hnonempty i
    exact ⟨⟨g, hg⟩⟩
  -- Normal restriction supplies transition maps on the finite Frobenius sets.
  have hrestrict (i j : ℕ) (hij : i ≤ j) (g : X j) :
      ∃ e : X i, ∀ x : F i,
        IntermediateField.inclusion (hmono hij) (e.val x) =
          g.val (IntermediateField.inclusion (hmono hij) x) := by
    obtain ⟨e, he, _⟩ := Submission.p09_af497904fe_ftl_normal_frobenius_restriction
      (F i) (F j) (hmono hij) (V i) (V j) ℓ (hV i j hij) g.val g.property
    exact ⟨⟨e, he.1⟩, he.2⟩
  let r : ∀ i j : ℕ, i ≤ j → X j → X i :=
    fun i j hij g => (hrestrict i j hij g).choose
  have hr (i j : ℕ) (hij : i ≤ j) (g : X j) (x : F i) :
      IntermediateField.inclusion (hmono hij) ((r i j hij g).val x) =
        g.val (IntermediateField.inclusion (hmono hij) x) :=
    (hrestrict i j hij g).choose_spec x
  have hself (i : ℕ) (g : X i) : r i i (Nat.le_refl i) g = g := by
    apply Subtype.ext
    apply AlgEquiv.ext
    intro x
    simpa only [IntermediateField.inclusion_self, AlgHom.id_apply] using
      hr i i (Nat.le_refl i) g x
  have hcomp (i j k : ℕ) (hij : i ≤ j) (hjk : j ≤ k) (g : X k) :
      r i k (Nat.le_trans hij hjk) g = r i j hij (r j k hjk g) := by
    apply Subtype.ext
    apply AlgEquiv.ext
    intro x
    apply IntermediateField.inclusion_injective (hmono (Nat.le_trans hij hjk))
    calc
      IntermediateField.inclusion (hmono (Nat.le_trans hij hjk))
          ((r i k (Nat.le_trans hij hjk) g).val x) =
          g.val (IntermediateField.inclusion (hmono (Nat.le_trans hij hjk)) x) :=
        hr i k (Nat.le_trans hij hjk) g x
      _ = IntermediateField.inclusion (hmono hjk)
          ((r j k hjk g).val (IntermediateField.inclusion (hmono hij) x)) :=
        (hr j k hjk g (IntermediateField.inclusion (hmono hij) x)).symm
      _ = IntermediateField.inclusion (hmono (Nat.le_trans hij hjk))
          ((r i j hij (r j k hjk g)).val x) :=
        congrArg (IntermediateField.inclusion (hmono hjk))
          (hr i j hij (r j k hjk g) x).symm
  -- Finiteness and nonemptiness suffice; the transition maps need not be surjective.
  obtain ⟨g, hg⟩ := Submission.p09_af497904fe_finite_inverse_limit X r hself hcomp
  have hcompat (i j : ℕ) (hij : i ≤ j) (x : F i) :
      IntermediateField.inclusion (hmono hij) ((g i).val x) =
        (g j).val (IntermediateField.inclusion (hmono hij) x) := by
    rw [← hg i j hij]
    exact hr i j hij (g j) x
  obtain ⟨τ, hτ⟩ := Submission.p09_af497904fe_ftl_compatible_automorphisms_glue
    F hmono hexhaust (fun i => (g i).val) hcompat
  have hstages : ∀ i : ℕ, ∃ e : F i ≃ₐ[ℚ] F i,
      (V i).IsFrobeniusAt e ℓ ∧ ∀ x : F i,
        τ (x : AlgebraicClosure ℚ) = ((e x : F i) : AlgebraicClosure ℚ) :=
    fun i => ⟨(g i).val, (g i).property, hτ i⟩
  obtain ⟨P, hPprime, hPV, hPfrob⟩ := Submission.p09_af497904fe_ftl_frobenius_valuation_union
    F hmono hexhaust V ℓ hprime hV τ hstages
  exact ⟨P, hPprime, hPV, τ, hPfrob, hstages⟩


theorem Submission.p09_af497904fe_ci_unramified_subfield :
    ∀ (E D : IntermediateField ℚ (AlgebraicClosure ℚ))
      [FiniteDimensional ℚ E] [FiniteDimensional ℚ D] (q : ℕ),
      q.Prime → D ≤ E →
      (∀ P : Ideal (NumberField.RingOfIntegers E), P.IsPrime →
        P.LiesOver (Ideal.span {(q : ℤ)}) → Ideal.ramificationIdx P ℤ = 1) →
      ∀ R : Ideal (NumberField.RingOfIntegers D), R.IsPrime →
        R.LiesOver (Ideal.span {(q : ℤ)}) → Ideal.ramificationIdx R ℤ = 1 := by
  intro E D _ _ q _ hDE hE R hR hRq
  let : NumberField E := NumberField.of_module_finite ℚ E
  let : NumberField D := NumberField.of_module_finite ℚ D
  let : Algebra D E := (IntermediateField.inclusion hDE).toRingHom.toAlgebra
  let : R.IsPrime := hR
  let : R.LiesOver (Ideal.span {(q : ℤ)}) := hRq
  obtain ⟨P, hP, hPR⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain
      (S := NumberField.RingOfIntegers E) R (by
        rw [NumberField.RingOfIntegers.ker_algebraMap_eq_bot D E]
        exact bot_le)
  let : P.IsPrime := hP
  let : P.LiesOver R := ⟨hPR.symm⟩
  have hPq : P.LiesOver (Ideal.span {(q : ℤ)}) :=
    Ideal.LiesOver.trans P R (Ideal.span {(q : ℤ)})
  have hprod : Ideal.ramificationIdx R ℤ *
      Ideal.ramificationIdx P (NumberField.RingOfIntegers D) = 1 :=
    (Ideal.ramificationIdx_tower (R := ℤ) R P).symm.trans (hE P hP hPq)
  exact (mul_eq_one.mp hprod).1


theorem Submission.p09_af497904fe_ir_inertia_cardinality :
    ∀ (E : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ E]
      [IsGalois ℚ E] (q : ℕ), q.Prime →
      ∀ P : Ideal (NumberField.RingOfIntegers E), P.IsPrime →
      P.LiesOver (Ideal.span {(q : ℤ)}) →
      Nat.card (P.inertia (E ≃ₐ[ℚ] E)) = Ideal.ramificationIdx P ℤ := by
  intro E _ _ q hq P hP hPq
  let : NumberField E := NumberField.of_module_finite ℚ E
  let : Fact q.Prime := ⟨hq⟩
  let : P.IsPrime := hP
  let : P.LiesOver (Ideal.span {(q : ℤ)}) := hPq
  let : Finite (ℤ ⧸ Ideal.span {(q : ℤ)}) :=
    Finite.of_equiv (ZMod q) (Int.quotientSpanNatEquivZMod q).symm.toEquiv
  exact (Ideal.card_inertia_eq_ramificationIdxIn (G := E ≃ₐ[ℚ] E)
    (Ideal.span {(q : ℤ)}) P).trans
    (Ideal.ramificationIdxIn_eq_ramificationIdx (Ideal.span {(q : ℤ)}) P (E ≃ₐ[ℚ] E))


theorem Submission.p09_af497904fe_cs_valuation_product_separation :
    ∀ {K : Type} [Field K] (n : ℕ) (β : Fin n → K) (D : ℤ),
      (∀ i : Fin n, IsIntegral ℤ (β i)) →
      (D : K) = (Finset.univ.filter (fun ij : Fin n × Fin n => ij.1 < ij.2)).prod
        (fun ij => (β ij.1 - β ij.2) ^ 2) →
      ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ D.natAbs →
      ∀ V : ValuationSubring K, V.LiesOverPrime ℓ →
        (∀ i : Fin n, β i ∈ V) ∧
        ∀ i j : Fin n, β i - β j ∈ V.nonunits → β i = β j := by
  classical
  intro K _ n β D hβ hprod ℓ hℓ hℓD V hV
  have hmem (i : Fin n) : β i ∈ V := by
    obtain ⟨x, hx⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral
      ((hβ i).tower_top : IsIntegral V (β i))
    exact hx ▸ x.property
  let b (i : Fin n) : V := ⟨β i, hmem i⟩
  have hℓV : (ℓ : V) ∈ maximalIdeal V :=
    ValuationSubring.coe_mem_nonunits_iff.mp (by
      simpa [ValuationSubring.LiesOverPrime] using hV)
  have hcop : IsCoprime D (ℓ : ℤ) := by
    apply Int.isCoprime_iff_gcd_eq_one.mpr
    simpa only [Int.gcd_def, Int.natAbs_natCast] using
      ((hℓ.coprime_iff_not_dvd.mpr hℓD).symm).gcd_eq_one
  obtain ⟨u, v, huv⟩ := hcop
  have hD : (D : V) ∉ maximalIdeal V := by
    intro hD
    have hcast : (u : V) * (D : V) + (v : V) * (ℓ : V) = 1 := by
      simpa using congrArg (Int.castRingHom V) huv
    have hone : (1 : V) ∈ maximalIdeal V := by
      rw [← hcast]
      exact (maximalIdeal V).add_mem
        ((maximalIdeal V).mul_mem_left _ hD) ((maximalIdeal V).mul_mem_left _ hℓV)
    exact (maximalIdeal.isMaximal V).ne_top (Ideal.eq_top_of_isUnit_mem _ hone isUnit_one)
  have hprodV : (D : V) =
      (Finset.univ.filter (fun ij : Fin n × Fin n => ij.1 < ij.2)).prod
        (fun ij => (b ij.1 - b ij.2) ^ 2) := by
    apply Subtype.ext
    change V.subtype (D : V) = V.subtype _
    simpa [b] using hprod
  have hsep (i j : Fin n) (hij : i < j) : β i - β j ∉ V.nonunits := by
    intro hdiff
    have hdiffV : b i - b j ∈ maximalIdeal V :=
      ValuationSubring.coe_mem_nonunits_iff.mp hdiff
    apply hD
    rw [hprodV]
    apply (maximalIdeal V).prod_mem (i := (i, j)) (by simp only [Finset.mem_filter,
      Finset.mem_univ, true_and, hij])
    simpa only [pow_two] using (maximalIdeal V).mul_mem_left (b i - b j) hdiffV
  refine ⟨hmem, ?_⟩
  intro i j hdiff
  rcases lt_trichotomy i j with hij | hij | hij
  · exact (hsep i j hij hdiff).elim
  · exact congrArg β hij
  · exact (hsep j i hij (by simpa only [neg_sub] using V.nonunits.neg_mem hdiff)).elim


theorem Submission.p09_af497904fe_ir_ideal_inertia_to_valuation :
    ∀ (E : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ E]
      (q : ℕ), q.Prime → ∀ P : Ideal (NumberField.RingOfIntegers E),
      P.IsPrime → P.LiesOver (Ideal.span {(q : ℤ)}) →
      ∃ V : ValuationSubring E, V.LiesOverPrime q ∧
        P.inertia (E ≃ₐ[ℚ] E) ≤ V.inertiaSubgroupIn ℚ := by
  classical
  intro E _ q hq P hP hPQ
  let : NumberField E := NumberField.of_module_finite ℚ E
  let : P.IsPrime := hP
  let : P.LiesOver (Ideal.span {(q : ℤ)}) := hPQ
  have hqP : (q : NumberField.RingOfIntegers E) ∈ P := by
    simpa only [map_natCast] using
      (Ideal.mem_of_liesOver P (Ideal.span {(q : ℤ)}) (q : ℤ)).mp
        (Ideal.subset_span (Set.mem_singleton _))
  have hP0 : P ≠ ⊥ := by
    intro h
    have : (q : NumberField.RingOfIntegers E) = 0 := by simpa [h] using hqP
    exact hq.ne_zero (Nat.cast_eq_zero.mp this)
  let v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E) :=
    ⟨P, hP, hP0⟩
  let V := v.valuationSubringAtPrime E
  let : Algebra (NumberField.RingOfIntegers E) V :=
    (Localization.subalgebra.ofField E P.primeCompl P.primeCompl_le_nonZeroDivisors).algebra'
  let : IsLocalization P.primeCompl V :=
    Localization.subalgebra.isLocalization_ofField E P.primeCompl
      P.primeCompl_le_nonZeroDivisors
  have hV (x : E) : x ∈ V ↔ ∃ a b : NumberField.RingOfIntegers E,
      b ∉ P ∧ x = (a : E) / (b : E) := by
    change (∃ a b, ∃ _ : b ∈ P.primeCompl,
      x = algebraMap (NumberField.RingOfIntegers E) E a *
        (algebraMap (NumberField.RingOfIntegers E) E b)⁻¹) ↔ _
    simp only [Ideal.mem_primeCompl_iff, exists_prop, div_eq_mul_inv]
  have hcenter (a : NumberField.RingOfIntegers E) :
      algebraMap (NumberField.RingOfIntegers E) V a ∈ maximalIdeal V ↔ a ∈ P :=
    IsLocalization.AtPrime.to_map_mem_maximal_iff V P a
  refine ⟨V, ?_, ?_⟩
  · change (q : E) ∈ V.nonunits
    have h := (hcenter q).mpr hqP
    have := V.coe_mem_nonunits_iff.mpr h
    simpa only [map_natCast, SubringClass.coe_natCast] using this
  · intro σ hσ
    have hstable (τ : E ≃ₐ[ℚ] E) (hτ : τ ∈ P.inertia (E ≃ₐ[ℚ] E))
        (x : E) (hx : x ∈ V) : τ x ∈ V := by
      obtain ⟨a, b, hb, rfl⟩ := (hV x).mp hx
      have hτb : τ • b ∉ P := by
        intro h
        apply hb
        have hd : τ • b - b ∈ P := hτ b
        simpa only [sub_sub_cancel] using P.sub_mem h hd
      apply (hV _).mpr
      refine ⟨τ • a, τ • b, hτb, ?_⟩
      exact map_div₀ τ (a : E) (b : E)
    have hσV : σ ∈ V.decompositionSubgroup ℚ := by
      let : MulAction (E ≃ₐ[ℚ] E) (ValuationSubring E) :=
        ValuationSubring.pointwiseMulAction
      apply MulAction.mem_stabilizer_iff.mpr
      apply ValuationSubring.ext
      intro x
      rw [ValuationSubring.mem_smul_pointwise_iff_exists]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hstable σ hσ y hy
      · intro hx
        refine ⟨σ⁻¹ x, hstable σ⁻¹ ((P.inertia _).inv_mem hσ) x hx, ?_⟩
        exact σ.apply_symm_apply x
    let g : V.decompositionSubgroup ℚ := ⟨σ, hσV⟩
    have hres : (residue V).comp
        (MulSemiringAction.toRingAut (V.decompositionSubgroup ℚ) V g).toRingHom =
        residue V := by
      apply IsLocalization.ringHom_ext P.primeCompl
      apply RingHom.ext
      intro a
      change residue V (g • algebraMap (NumberField.RingOfIntegers E) V a) =
        residue V (algebraMap (NumberField.RingOfIntegers E) V a)
      apply sub_eq_zero.mp
      rw [← map_sub, residue_eq_zero_iff]
      have heq : g • algebraMap (NumberField.RingOfIntegers E) V a -
          algebraMap (NumberField.RingOfIntegers E) V a =
          algebraMap (NumberField.RingOfIntegers E) V (σ • a - a) := by
        apply Subtype.ext
        rfl
      rw [heq]
      exact (hcenter _).mpr (hσ a)
    have hg : g ∈ V.inertiaSubgroup ℚ := by
      change MulSemiringAction.toRingAut (V.decompositionSubgroup ℚ)
        (ResidueField V) g = 1
      apply RingEquiv.ext
      intro x
      obtain ⟨a, rfl⟩ := residue_surjective x
      exact RingHom.congr_fun hres a
    exact ⟨g, hg, rfl⟩
theorem Submission.p09_af497904fe_luf_finite_frobenius_exists :
    ∀ (E : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ E]
      [IsGalois ℚ E] (ℓ : ℕ), ℓ.Prime → ∀ (V : ValuationSubring E),
      V.LiesOverPrime ℓ → ∃ g : E ≃ₐ[ℚ] E, V.IsFrobeniusAt g ℓ := by
  intro E _ _ ℓ hℓ V hV
  obtain ⟨q, hq, _hq_ne, hℓq, hfinite, hlocal, hnonunits⟩ :=
    Submission.p09_af497904fe_luf_valuation_localization E ℓ hℓ V hV
  obtain ⟨g, hg⟩ :=
    Submission.p09_af497904fe_ffe_prime_frobenius_congruence E ℓ hℓ q hq hℓq hfinite
  exact ⟨g, Submission.p09_af497904fe_ffe_localized_frobenius
    E ℓ hℓ V q hq hlocal hnonunits g hg⟩


theorem Submission.p09_af497904fe_cwi_infinite_diff_of_log_lower_bound :
    ∀ (ι : Type) (N : ι → ℕ) (E D : Set ι) (c K ε C : ℝ),
      (∀ i : ι, 2 ≤ N i) →
      (∀ s : ℝ, 1 < s → Summable (fun i : ι => Real.rpow (N i : ℝ) (-s))) →
      0 < c → 0 < ε → ε ≤ 1 →
      (∀ s : ℝ, 1 < s → s < 1 + ε →
        c * Real.log (1 / (s - 1)) - K ≤
          ∑' i : {i : ι // i ∈ E}, Real.rpow (N i.1 : ℝ) (-s)) →
      (∀ s : ℝ, 1 < s → s < 2 →
        (∑' i : {i : ι // i ∈ D}, Real.rpow (N i.1 : ℝ) (-s)) ≤ C) →
      Set.Infinite (E \ D) := by
  classical
  intro ι N E D c K ε C hN hsum hc hε hεone hlower hD
  by_contra hfinite
  have hA : (E \ D).Finite := Set.not_infinite.mp hfinite
  let := hA.fintype
  let r : ℝ := Fintype.card ↑(E \ D)
  have hnonneg (s : ℝ) (i : ι) : 0 ≤ Real.rpow (N i : ℝ) (-s) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hweight (s : ℝ) (hs : 1 < s) (i : ι) :
      Real.rpow (N i : ℝ) (-s) ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos
    · exact_mod_cast (le_trans (by decide : 1 ≤ 2) (hN i))
    · linarith
  have hupper (s : ℝ) (hs : 1 < s) (hsε : s < 1 + ε) :
      (∑' i : E, Real.rpow (N i.1 : ℝ) (-s)) ≤ C + r := by
    have hsplit := Summable.tsum_union_disjoint
      (f := fun i : ι => Real.rpow (N i : ℝ) (-s))
      (s := E ∩ D) (t := E \ D) Set.disjoint_sdiff_inter.symm
      ((hsum s hs).subtype _) ((hsum s hs).subtype _)
    rw [Set.inter_union_sdiff] at hsplit
    have hinter : (∑' i : ↑(E ∩ D), Real.rpow (N i.1 : ℝ) (-s)) ≤
        ∑' i : D, Real.rpow (N i.1 : ℝ) (-s) := by
      apply Summable.tsum_le_tsum_of_inj
        (fun i : ↑(E ∩ D) => (⟨i.1, i.2.2⟩ : D))
        (fun i j hij => Subtype.ext (congrArg (fun k : D => k.1) hij))
        (fun i _ => hnonneg s i.1) (fun _ => le_rfl)
        ((hsum s hs).subtype _) ((hsum s hs).subtype _)
    have hdiff : (∑' i : ↑(E \ D), Real.rpow (N i.1 : ℝ) (-s)) ≤ r := by
      rw [tsum_fintype]
      calc
        (∑ i : ↑(E \ D), Real.rpow (N i.1 : ℝ) (-s)) ≤
            ∑ _i : ↑(E \ D), (1 : ℝ) := Finset.sum_le_sum fun i _ => hweight s hs i.1
        _ = r := by simp [r]
    rw [hsplit]
    exact add_le_add (hinter.trans (hD s hs (by linarith))) hdiff
  let u : ℝ := max ((C + r + K) / c) (-Real.log ε) + 1
  have hu₁ : (C + r + K) / c < u :=
    lt_of_le_of_lt (le_max_left _ _) (lt_add_one _)
  have hu₂ : -Real.log ε < u :=
    lt_of_le_of_lt (le_max_right _ _) (lt_add_one _)
  let s : ℝ := 1 + Real.exp (-u)
  have hs : 1 < s := by dsimp [s]; linarith [Real.exp_pos (-u)]
  have hsε : s < 1 + ε := by
    have hexp : Real.exp (-u) < ε := by
      calc
        Real.exp (-u) < Real.exp (Real.log ε) := Real.exp_lt_exp.mpr (by linarith)
        _ = ε := Real.exp_log hε
    dsimp [s]
    linarith
  have hlog : Real.log (1 / (s - 1)) = u := by
    dsimp [s]
    rw [add_sub_cancel_left, one_div, Real.log_inv, Real.log_exp, neg_neg]
  have hl := hlower s hs hsε
  rw [hlog] at hl
  have hu : C + r + K < u * c := (div_lt_iff₀ hc).mp hu₁
  have hb := hupper s hs hsε
  nlinarith


theorem Submission.p09_af497904fe_ce_inertia_ramification :
    ∀ (E : IntermediateField ℚ (AlgebraicClosure ℚ))
      [FiniteDimensional ℚ E] [IsGalois ℚ E] (q : ℕ),
      q.Prime →
      (∀ V : ValuationSubring E, V.LiesOverPrime q →
        ∀ τ : E ≃ₐ[ℚ] E, τ ∈ V.inertiaSubgroupIn ℚ → τ = 1) →
      ∀ P : Ideal (NumberField.RingOfIntegers E), P.IsPrime →
        P.LiesOver (Ideal.span {(q : ℤ)}) → Ideal.ramificationIdx P ℤ = 1 := by
  intro E _ _ q hq hI P hP hPq
  obtain ⟨V, hV, hPV⟩ :=
    Submission.p09_af497904fe_ir_ideal_inertia_to_valuation E q hq P hP hPq
  have htrivial : P.inertia (E ≃ₐ[ℚ] E) = ⊥ := by
    apply (Subgroup.eq_bot_iff_forall _).mpr
    intro τ hτ
    exact hI V hV τ (hPV hτ)
  rw [← Submission.p09_af497904fe_ir_inertia_cardinality E q hq P hP hPq,
    htrivial]
  exact Subgroup.card_bot

theorem Submission.p09_af497904fe_irp_squared_vandermonde_symmetric :
    ∀ n : ℕ, MvPolynomial.IsSymmetric
      ((Finset.univ.filter (fun ij : Fin n × Fin n => ij.1 < ij.2)).prod
        (fun ij => ((MvPolynomial.X ij.1 : MvPolynomial (Fin n) ℤ) -
          MvPolynomial.X ij.2) ^ 2)) := by
  classical
  intro n π
  let T := Finset.univ.filter (fun ij : Fin n × Fin n => ij.1 < ij.2)
  let B (e : Equiv.Perm (Fin n)) (ij : Fin n × Fin n) :=
    if e ij.1 < e ij.2 then (e ij.1, e ij.2) else (e ij.2, e ij.1)
  have hmem (e : Equiv.Perm (Fin n)) (ij : Fin n × Fin n) (hij : ij ∈ T) :
      B e ij ∈ T := by
    have hlt : ij.1 < ij.2 := (Finset.mem_filter.mp hij).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    by_cases h : e ij.1 < e ij.2
    · simpa only [B, if_pos h] using h
    · have hne : e ij.2 ≠ e ij.1 := fun heq =>
        (ne_of_lt hlt) (e.injective heq.symm)
      simpa only [B, if_neg h] using lt_of_le_of_ne (le_of_not_gt h) hne
  have hinv (e : Equiv.Perm (Fin n)) (ij : Fin n × Fin n) (hij : ij ∈ T) :
      B e.symm (B e ij) = ij := by
    have hlt : ij.1 < ij.2 := (Finset.mem_filter.mp hij).2
    by_cases h : e ij.1 < e ij.2
    · simp [B, h, hlt]
    · simp [B, h, not_lt_of_gt hlt]
  simp only [map_prod, map_pow, map_sub, MvPolynomial.rename_X]
  refine Finset.prod_nbij' (B π) (B π.symm) (hmem π) (hmem π.symm)
    (hinv π) ?_ ?_
  · intro ij hij
    simpa only [Equiv.symm_symm] using hinv π.symm ij hij
  · intro ij _
    by_cases h : π ij.1 < π ij.2
    · simp only [B, if_pos h]
    · simp only [B, if_neg h]
      ring

theorem Submission.p09_af497904fe_csr_prime_residue_descent :
    ∀ (C D : IntermediateField ℚ (AlgebraicClosure ℚ))
      [FiniteDimensional ℚ C] [FiniteDimensional ℚ D] (q : ℕ)
      (A : Ideal (NumberField.RingOfIntegers C)),
      q.Prime → D ≤ C → A.IsPrime → A.LiesOver (Ideal.span {(q : ℤ)}) →
      Nat.card (NumberField.RingOfIntegers C ⧸ A) = q →
      (∀ B : Ideal (NumberField.RingOfIntegers C), B.IsPrime →
        B.LiesOver (Ideal.span {(q : ℤ)}) → B = A) →
      ∃ R : Ideal (NumberField.RingOfIntegers D), R.IsPrime ∧
        R.LiesOver (Ideal.span {(q : ℤ)}) ∧
        Ideal.ramificationIdx R ℤ = Module.finrank ℚ D := by
  intro C D _ _ q A hq hDC hA hAover hcard huniq
  classical
  let : NumberField C := ⟨⟩
  let : NumberField D := ⟨⟩
  let : Algebra D C := (IntermediateField.inclusion hDC).toRingHom.toAlgebra
  let : Fact q.Prime := ⟨hq⟩
  let p : Ideal ℤ := Ideal.span {(q : ℤ)}
  let R := A.under (NumberField.RingOfIntegers D)
  have : A.IsPrime := hA
  have : A.LiesOver p := hAover
  have : A.LiesOver R := Ideal.over_under _
  have : R.IsPrime := inferInstance
  have : R.LiesOver p := Ideal.LiesOver.tower_bot A R p
  have hRuniq (Q : Ideal (NumberField.RingOfIntegers D))
      (hQ : Q.IsPrime) (hQover : Q.LiesOver p) : Q = R := by
    have := hQ
    have := hQover
    obtain ⟨B, hB, hBQ⟩ := Q.exists_ideal_over_prime_of_isIntegral_of_isDomain
      (S := NumberField.RingOfIntegers C) (by
        rw [NumberField.RingOfIntegers.ker_algebraMap_eq_bot]
        exact bot_le)
    have := hB
    have : B.LiesOver Q := ⟨hBQ.symm⟩
    have : B.LiesOver p := Ideal.LiesOver.trans B Q p
    have hBA := huniq B hB inferInstance
    exact hBQ.symm.trans (congrArg (fun I => I.under (NumberField.RingOfIntegers D)) hBA)
  have hAdeg : A.inertiaDeg ℤ = 1 := by
    apply Nat.pow_right_injective hq.two_le
    simpa only [pow_one, Ideal.absNorm_apply, Submodule.cardQuot_apply, hcard] using
      (Ideal.pow_inertiaDeg q A)
  have hRdeg : R.inertiaDeg ℤ = 1 := by
    apply Nat.dvd_one.mp
    rw [← hAdeg]
    exact Ideal.inertiaDeg_below_dvd (R := ℤ) R A
  let r : p.primesOver (NumberField.RingOfIntegers D) := Ideal.primesOver.mk p R
  let : Unique (p.primesOver (NumberField.RingOfIntegers D)) :=
    { default := r
      uniq := fun Q => Subtype.ext (hRuniq Q.1 Q.2.1 Q.2.2) }
  let := Fintype.ofFinite (p.primesOver (NumberField.RingOfIntegers D))
  refine ⟨R, inferInstance, inferInstance, ?_⟩
  have hsum := Ideal.sum_ramification_inertia_eq_finrank p (NumberField.RingOfIntegers D)
  rw [Finset.univ_unique, Finset.sum_singleton] at hsum
  change R.ramificationIdx ℤ * R.inertiaDeg ℤ =
    Module.finrank ℤ (NumberField.RingOfIntegers D) at hsum
  simpa only [hRdeg, mul_one, NumberField.RingOfIntegers.rank] using hsum

theorem Submission.p09_af497904fe_irp_minpoly_roots :
    ∀ (E : IntermediateField ℚ (AlgebraicClosure ℚ))
      [FiniteDimensional ℚ E] [IsGalois ℚ E] (α : E),
      IsIntegral ℤ α → ∃ (n : ℕ) (β : Fin n → E),
        Function.Injective β ∧ (∀ i : Fin n, IsIntegral ℤ (β i)) ∧
        (∀ σ : E ≃ₐ[ℚ] E, ∃ i : Fin n, β i = σ α) ∧
        (minpoly ℤ α).map (Int.castRingHom E) =
          Finset.univ.prod (fun i : Fin n => Polynomial.X - Polynomial.C (β i)) := by
  intro E _ _ α hα
  classical
  have hαQ : IsIntegral ℚ α := Algebra.IsIntegral.isIntegral α
  have hmap : (minpoly ℤ α).map (Int.castRingHom E) =
      (minpoly ℚ α).map (algebraMap ℚ E) := by
    calc
      _ = ((minpoly ℤ α).map (algebraMap ℤ ℚ)).map (algebraMap ℚ E) := by
        rw [Polynomial.map_map]
        exact congrArg (fun f : ℤ →+* E => (minpoly ℤ α).map f)
          (Subsingleton.elim _ _)
      _ = _ := congrArg (Polynomial.map (algebraMap ℚ E))
        (minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hα).symm
  obtain ⟨s, hs⟩ := Polynomial.exists_finset_of_splits (algebraMap ℚ E)
    (Algebra.IsSeparable.isSeparable ℚ α)
    (Normal.splits (inferInstance : Normal ℚ E) α)
  have hprod : (minpoly ℤ α).map (Int.castRingHom E) =
      s.prod (fun b => Polynomial.X - Polynomial.C b) := by
    rw [hmap, hs, (minpoly.monic hαQ).leadingCoeff, map_one, Polynomial.C_1, one_mul]
  let n := Fintype.card s
  let e : Fin n ≃ s := (Fintype.equivFin s).symm
  let β : Fin n → E := fun i => (e i).val
  have hfac : (minpoly ℤ α).map (Int.castRingHom E) =
      Finset.univ.prod (fun i : Fin n => Polynomial.X - Polynomial.C (β i)) := by
    calc
      _ = s.prod (fun b => Polynomial.X - Polynomial.C b) := hprod
      _ = ∏ b : s, (Polynomial.X - Polynomial.C (b : E)) :=
        (Finset.prod_coe_sort s (fun b => Polynomial.X - Polynomial.C b)).symm
      _ = _ := (e.prod_comp (fun b : s => Polynomial.X - Polynomial.C (b : E))).symm
  refine ⟨n, β, Subtype.val_injective.comp e.injective, ?_, ?_, hfac⟩
  · intro i
    refine ⟨minpoly ℤ α, minpoly.monic hα, ?_⟩
    change Polynomial.eval₂ (Int.castRingHom E) (β i) (minpoly ℤ α) = 0
    rw [Polynomial.eval₂_eq_eval_map, hfac, Polynomial.eval_prod]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp
  · intro σ
    have hzero : ((minpoly ℤ α).map (Int.castRingHom E)).eval (σ α) = 0 := by
      rw [hmap, Polynomial.eval_map_algebraMap, Polynomial.aeval_algHom_apply,
        minpoly.aeval, map_zero]
    rw [hfac, Polynomial.eval_prod] at hzero
    obtain ⟨i, _, hi⟩ := Finset.prod_eq_zero_iff.mp hzero
    exact ⟨i, (sub_eq_zero.mp (by simpa using hi)).symm⟩

theorem Submission.p09_af497904fe_irp_integer_discriminant :
    ∀ (K : Type) [Field K] (f : Polynomial ℤ) (n : ℕ) (β : Fin n → K),
      f.Monic → Function.Injective β →
      f.map (Int.castRingHom K) = Finset.univ.prod
        (fun i : Fin n => Polynomial.X - Polynomial.C (β i)) →
      ∃ D : ℤ, D ≠ 0 ∧ (D : K) =
        (Finset.univ.filter (fun ij : Fin n × Fin n => ij.1 < ij.2)).prod
          (fun ij => (β ij.1 - β ij.2) ^ 2) := by
  classical
  intro K _ f n β _hf hβ hfac
  let P : MvPolynomial (Fin n) ℤ :=
    (Finset.univ.filter (fun ij : Fin n × Fin n => ij.1 < ij.2)).prod
      (fun ij => (MvPolynomial.X ij.1 - MvPolynomial.X ij.2) ^ 2)
  have hP : MvPolynomial.IsSymmetric P :=
    Submission.p09_af497904fe_irp_squared_vandermonde_symmetric n
  obtain ⟨Q, hQ⟩ := MvPolynomial.esymmAlgHom_surjective ℤ
    (σ := Fin n) (n := n) (by simp) ⟨P, hP⟩
  have hQval : MvPolynomial.aeval
      (fun i : Fin n => MvPolynomial.esymm (Fin n) ℤ (i.val + 1)) Q = P := by
    simpa only [MvPolynomial.esymmAlgHom_apply] using congrArg Subtype.val hQ
  -- Vieta identifies the elementary symmetric values with signed integer coefficients.
  let c : Fin n → ℤ := fun i => (-1) ^ (i.val + 1) * f.coeff (n - (i.val + 1))
  let s : Multiset K := Finset.univ.val.map β
  have hcard : s.card = n := by simp [s]
  have hprod : (s.map (fun b => Polynomial.X - Polynomial.C b)).prod =
      Finset.univ.prod (fun i : Fin n => Polynomial.X - Polynomial.C (β i)) := by
    simp [s, Finset.prod_eq_multiset_prod, Function.comp_def]
  have hc (i : Fin n) : (c i : K) =
      MvPolynomial.aeval β (MvPolynomial.esymm (Fin n) ℤ (i.val + 1)) := by
    have hi : i.val + 1 ≤ n := i.isLt
    have hv := Multiset.prod_X_sub_C_coeff s
      (k := n - (i.val + 1)) (by rw [hcard]; exact Nat.sub_le _ _)
    rw [hcard, Nat.sub_sub_self hi, hprod, ← hfac, Polynomial.coeff_map] at hv
    change (f.coeff (n - (i.val + 1)) : K) = _ at hv
    rw [MvPolynomial.aeval_esymm_eq_multiset_esymm]
    change (((-1 : ℤ) ^ (i.val + 1) * f.coeff (n - (i.val + 1)) : ℤ) : K) =
      s.esymm (i.val + 1)
    push_cast
    rw [hv, ← mul_assoc, ← mul_pow]
    simp
  let D : ℤ := MvPolynomial.aeval c Q
  have hD : (D : K) =
      (Finset.univ.filter (fun ij : Fin n × Fin n => ij.1 < ij.2)).prod
        (fun ij => (β ij.1 - β ij.2) ^ 2) := by
    calc
      (D : K) = MvPolynomial.aeval (fun i => (c i : K)) Q := by
        exact MvPolynomial.comp_aeval_apply c (Algebra.ofId ℤ K) Q
      _ = MvPolynomial.aeval
          (fun i : Fin n => MvPolynomial.aeval β
            (MvPolynomial.esymm (Fin n) ℤ (i.val + 1))) Q := by
        simp_rw [hc]
      _ = MvPolynomial.aeval β P := by
        rw [← MvPolynomial.comp_aeval_apply, hQval]
      _ = _ := by simp [P]
  refine ⟨D, ?_, hD⟩
  have hnonzero :
      (Finset.univ.filter (fun ij : Fin n × Fin n => ij.1 < ij.2)).prod
        (fun ij => (β ij.1 - β ij.2) ^ 2) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro ij hij
    exact pow_ne_zero _ (sub_ne_zero.mpr (hβ.ne (ne_of_lt (Finset.mem_filter.mp hij).2)))
  intro hzero
  apply hnonzero
  rw [← hD, hzero, Int.cast_zero]
theorem Submission.p09_af497904fe_csr_cyclotomic_prime_residue :
    ∀ (q : ℕ) (ζ : AlgebraicClosure ℚ), q.Prime → IsPrimitiveRoot ζ q →
      let C := IntermediateField.adjoin ℚ ({ζ} : Set (AlgebraicClosure ℚ))
      FiniteDimensional ℚ C ∧ ∃ A : Ideal (NumberField.RingOfIntegers C),
        A.IsPrime ∧ A.LiesOver (Ideal.span {(q : ℤ)}) ∧
        Nat.card (NumberField.RingOfIntegers C ⧸ A) = q ∧
        ∀ B : Ideal (NumberField.RingOfIntegers C), B.IsPrime →
          B.LiesOver (Ideal.span {(q : ℤ)}) → B = A := by
  intro q ζ hq hζ
  let C := IntermediateField.adjoin ℚ ({ζ} : Set (AlgebraicClosure ℚ))
  let : Fact q.Prime := ⟨hq⟩
  let : NeZero q := ⟨hq.ne_zero⟩
  let : Algebra.IsIntegral ℚ (AlgebraicClosure ℚ) :=
    Algebra.isAlgebraic_iff_isIntegral.mp (AlgebraicClosure.isAlgebraic ℚ)
  let : IsCyclotomicExtension {q} ℚ C :=
    hζ.intermediateField_adjoin_isCyclotomicExtension ℚ
  let : NumberField C := IsCyclotomicExtension.numberField {q} ℚ C
  let : IsCyclotomicExtension {q ^ (0 + 1)} ℚ C := by
  letI : Fact q.Prime := ⟨hq⟩
  letI : NeZero q := ⟨hq.ne_zero⟩
  letI : IsCyclotomicExtension {q} ℚ C :=
    Algebra.isAlgebraic_iff_isIntegral.mp inferInstance
  let : IsCyclotomicExtension {q} ℚ C :=
    hζ.intermediateField_adjoin_isCyclotomicExtension ℚ
  let : NumberField C := IsCyclotomicExtension.numberField {q} ℚ C
  let : IsCyclotomicExtension {q ^ (0 + 1)} ℚ C := by
    simpa only [zero_add, pow_one] using
      (inferInstance : IsCyclotomicExtension {q} ℚ C)
  have hξ := IsCyclotomicExtension.zeta_spec (q ^ (0 + 1)) ℚ C
  refine ⟨inferInstance, Ideal.span {hξ.toInteger - 1},
    IsCyclotomicExtension.Rat.isPrime_span_zeta_sub_one q 0 hξ,
    IsCyclotomicExtension.Rat.liesOver_span_zeta_sub_one q 0 hξ, ?_, ?_⟩
  · change Ideal.absNorm (Ideal.span {hξ.toInteger - 1}) = q
    exact IsCyclotomicExtension.Rat.absNorm_span_zeta_sub_one q 0 hξ
  · intro B hB hBq
    let : B.IsPrime := hB
    let : B.LiesOver (Ideal.span {(q : ℤ)}) := hBq
    exact IsCyclotomicExtension.Rat.eq_span_zeta_sub_one_of_liesOver q 0 C hξ B
theorem Submission.p09_af497904fe_cs_integer_root_product :
    ∀ (E : IntermediateField ℚ (AlgebraicClosure ℚ))
      [FiniteDimensional ℚ E] [IsGalois ℚ E] (α : E),
      IsIntegral ℤ α → ∃ (n : ℕ) (β : Fin n → E) (D : ℤ),
        Function.Injective β ∧
        (∀ i : Fin n, IsIntegral ℤ (β i)) ∧
        (∀ σ : E ≃ₐ[ℚ] E, ∃ i : Fin n, β i = σ α) ∧
        D ≠ 0 ∧
        (D : E) = (Finset.univ.filter (fun ij : Fin n × Fin n => ij.1 < ij.2)).prod
          (fun ij => (β ij.1 - β ij.2) ^ 2) := by
  intro E _ _ α hα
  obtain ⟨n, β, hβinj, hβint, hβconj, hfactor⟩ :=
    Submission.p09_af497904fe_irp_minpoly_roots E α hα
  obtain ⟨D, hDne, hDprod⟩ :=
    Submission.p09_af497904fe_irp_integer_discriminant E (minpoly ℤ α) n β
      (minpoly.monic hα) hβinj hfactor
  exact ⟨n, β, D, hβinj, hβint, hβconj, hDne, hDprod⟩
/-- Lift the uniquely specified finite Frobenius through a countable Galois tower. -/
theorem Submission.p09_af497904fe_fa_lift_unique_frobenius :
    ∀ (E : IntermediateField ℚ (AlgebraicClosure ℚ))
      [FiniteDimensional ℚ E] [IsGalois ℚ E] (ℓ : ℕ), ℓ.Prime →
      ∀ (V : ValuationSubring E), V.LiesOverPrime ℓ →
      ∀ (g : E ≃ₐ[ℚ] E), V.IsFrobeniusAt g ℓ →
      (∀ g' : E ≃ₐ[ℚ] E, V.IsFrobeniusAt g' ℓ → g' = g) →
      ∃ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ ∧
        (∀ x : E, (x : AlgebraicClosure ℚ) ∈ P ↔ x ∈ V) ∧
        ∃ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
          P.IsFrobeniusAt τ ℓ ∧
          ∀ x : E, τ (x : AlgebraicClosure ℚ) = ((g x : E) : AlgebraicClosure ℚ) := by
  classical
  intro E hfd hgal ℓ hℓ V hV g _hg huniq
  -- Close each successive enumerated element under its rational conjugates.
  have : IsAlgClosure ℚ (AlgebraicClosure ℚ) :=
    { isAlgClosed := AlgebraicClosure.isAlgClosed ℚ
      isAlgebraic := AlgebraicClosure.isAlgebraic ℚ }
  have : Countable (AlgebraicClosure ℚ) := Set.countable_univ_iff.mp
    ((Algebraic.countable ℚ (AlgebraicClosure ℚ)).mono
      (fun x _ => Algebra.IsAlgebraic.isAlgebraic x))
  have : IsGalois ℚ (AlgebraicClosure ℚ) :=
    { to_isSeparable := inferInstance, to_normal := IsAlgClosure.normal ℚ (AlgebraicClosure ℚ) }
  obtain ⟨a, ha⟩ := exists_surjective_nat (AlgebraicClosure ℚ)
  let T : ℕ → FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ) :=
    Nat.rec { toIntermediateField := E, finiteDimensional := hfd, isGalois := hgal }
      (fun i K => K ⊔ FiniteGaloisIntermediateField.adjoin ℚ {a i})
  let F : ℕ → IntermediateField ℚ (AlgebraicClosure ℚ) :=
    fun i => (T i).toIntermediateField
  have hmono : Monotone F := monotone_nat_of_le_succ fun i =>
    (show T i ≤ T (i + 1) from le_sup_left)
  have hcover : ∀ x : AlgebraicClosure ℚ, ∃ i : ℕ, x ∈ F i := by
    intro x
    obtain ⟨i, rfl⟩ := ha x
    refine ⟨i + 1, ?_⟩
    exact (show (FiniteGaloisIntermediateField.adjoin ℚ {a i}).toIntermediateField ≤
      F (i + 1) from le_sup_right)
      (FiniteGaloisIntermediateField.subset_adjoin ℚ {a i} (Set.mem_singleton _))
  -- Choose extensions recursively, retaining the nonunit condition at every stage.
  let extend (i : ℕ) (W : {W : ValuationSubring (F i) // W.LiesOverPrime ℓ}) :
      {W : ValuationSubring (F (i + 1)) // W.LiesOverPrime ℓ} :=
    ⟨(@Submission.p09_af497904fe_luf_valuation_extension (F i) (F (i + 1))
        (T i).finiteDimensional (T (i + 1)).finiteDimensional
        (hmono (Nat.le_succ i)) ℓ hℓ W.1 W.2).choose,
      (@Submission.p09_af497904fe_luf_valuation_extension (F i) (F (i + 1))
        (T i).finiteDimensional (T (i + 1)).finiteDimensional
        (hmono (Nat.le_succ i)) ℓ hℓ W.1 W.2).choose_spec.1⟩
  let W : (i : ℕ) → {W : ValuationSubring (F i) // W.LiesOverPrime ℓ} :=
    Nat.rec ⟨V, hV⟩ extend
  have hstep (i : ℕ) (x : F i) :
      IntermediateField.inclusion (hmono (Nat.le_succ i)) x ∈ (W (i + 1)).1 ↔
        x ∈ (W i).1 :=
    (@Submission.p09_af497904fe_luf_valuation_extension (F i) (F (i + 1))
        (T i).finiteDimensional (T (i + 1)).finiteDimensional
      (hmono (Nat.le_succ i)) ℓ hℓ (W i).1 (W i).2).choose_spec.2 x
  have hrestrict (i j : ℕ) (hij : i ≤ j) (x : F i) :
      IntermediateField.inclusion (hmono hij) x ∈ (W j).1 ↔ x ∈ (W i).1 := by
    induction j, hij using Nat.le_induction with
    | base => rfl
    | succ j hij ih =>
      exact (hstep j (IntermediateField.inclusion (hmono hij) x)).trans ih
  -- The tower lemma supplies a global Frobenius with finite Frobenius restrictions.
  obtain ⟨P, hP, hPW, τ, hτ, hτW⟩ :=
    Submission.p09_af497904fe_luf_frobenius_tower_limit F hmono
      (fun i => (T i).finiteDimensional) (fun i => (T i).isGalois) hcover
      (fun i => (W i).1) ℓ (fun i => (W i).2) hrestrict
      (fun i => @Submission.p09_af497904fe_luf_finite_frobenius_exists
        (F i) (T i).finiteDimensional (T i).isGalois ℓ hℓ (W i).1 (W i).2)
  obtain ⟨g₀, hg₀, hτ₀⟩ := hτW 0
  have hg₀_eq : g₀ = g := huniq g₀ hg₀
  refine ⟨P, hP, hPW 0, τ, hτ, ?_⟩
  intro x
  simpa only [hg₀_eq] using hτ₀ x


theorem Submission.p09_af497904fe_ci_cyclotomic_subfield_ramification :
    ∀ (q : ℕ) (ζ : AlgebraicClosure ℚ), q.Prime → IsPrimitiveRoot ζ q →
      ∀ (D : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ D],
        D ≤ IntermediateField.adjoin ℚ ({ζ} : Set (AlgebraicClosure ℚ)) →
          ∃ R : Ideal (NumberField.RingOfIntegers D),
            R.IsPrime ∧ R.LiesOver (Ideal.span {(q : ℤ)}) ∧
              Ideal.ramificationIdx R ℤ = Module.finrank ℚ D := by
  intro q ζ hq hζ D _ hDC
  let C := IntermediateField.adjoin ℚ ({ζ} : Set (AlgebraicClosure ℚ))
  obtain ⟨hC, A, hA, hAq, hcard, huniq⟩ :=
    Submission.p09_af497904fe_csr_cyclotomic_prime_residue q ζ hq hζ
  let : FiniteDimensional ℚ C := hC
  exact Submission.p09_af497904fe_csr_prime_residue_descent
    C D q A hq hDC hA hAq hcard huniq


theorem Submission.p09_af497904fe_cwi_character_orthogonality :
    ∀ (m : ℕ) (ω : ℂ), 0 < m → IsPrimitiveRoot ω m → ∀ a b : ZMod m,
      (∑ k : Fin m, star (ω ^ (k.val * a.val)) * ω ^ (k.val * b.val)) =
        (if b = a then (m : ℂ) else 0) := by
  intro m ω hm hω a b
  have : NeZero m := ⟨Nat.ne_of_gt hm⟩
  have hω0 : ω ≠ 0 := hω.ne_zero (Nat.ne_of_gt hm)
  have hstar : (starRingEnd ℂ) ω = ω⁻¹ :=
    (Complex.inv_eq_conj (hω.norm'_eq_one (Nat.ne_of_gt hm))).symm
  let u : ℂ := ω ^ b.val / ω ^ a.val
  have hu : u ^ m = 1 := by
    dsimp [u]
    rw [div_pow, pow_right_comm ω b.val m, pow_right_comm ω a.val m,
      hω.pow_eq_one, one_pow, one_pow, div_self one_ne_zero]
  have hterm (k : ℕ) :
      star (ω ^ (k * a.val)) * ω ^ (k * b.val) = u ^ k := by
    dsimp [u]
    rw [Nat.mul_comm k a.val, Nat.mul_comm k b.val, pow_mul, pow_mul,
      map_pow, map_pow, hstar, inv_pow, div_pow, div_eq_mul_inv, inv_pow]
    exact mul_comm _ _
  simp_rw [hterm]
  by_cases hba : b = a
  · have hu1 : u = 1 := by
      dsimp [u]
      rw [hba, div_self (pow_ne_zero _ hω0)]
    simp [hba, hu1]
  · have hu1 : u ≠ 1 := by
      intro h
      apply hba
      apply ZMod.val_injective
      apply hω.pow_inj (ZMod.val_lt _) (ZMod.val_lt _)
      exact (div_eq_one_iff_eq (pow_ne_zero _ hω0)).mp h
    rw [if_neg hba, Fin.sum_univ_eq_sum_range]
    exact (mul_eq_zero.mp ((geom_sum_mul u m).trans (by rw [hu, sub_self]))).resolve_right
      (sub_ne_zero.mpr hu1)


theorem Submission.p09_af497904fe_cwi_fiber_log_estimate :
    ∀ (ι : Type) (m : ℕ) (ω : ℂ) (N : ι → ℕ) (g : ι → ZMod m),
      0 < m → IsPrimitiveRoot ω m → (∀ i : ι, 2 ≤ N i) →
      (∀ s : ℝ, 1 < s → Summable (fun i : ι => Real.rpow (N i : ℝ) (-s))) →
      (∀ k : Fin m, ∃ C : ℝ, 0 ≤ C ∧ ∃ ε : ℝ, 0 < ε ∧
        ∀ s : ℝ, 1 < s → s < 1 + ε →
          ‖(∑' i : ι, ω ^ (k.val * (g i).val) *
              Complex.ofReal (Real.rpow (N i : ℝ) (-s))) -
            (if k.val = 0 then (Real.log (1 / (s - 1)) : ℂ) else 0)‖ ≤ C) →
      ∃ K : ℝ, 0 ≤ K ∧ ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧
        ∀ (a : ZMod m) (s : ℝ), 1 < s → s < 1 + ε →
          |(∑' i : {i : ι // g i = a}, Real.rpow (N i.1 : ℝ) (-s)) -
            Real.log (1 / (s - 1)) / (m : ℝ)| ≤ K := by
  classical
  intro ι m ω N g hm hω _hN hsum hbound
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hnorm : ‖ω‖ = 1 := hω.norm'_eq_one (Nat.ne_of_gt hm)
  have hchar (k : Fin m) (b : ZMod m) : ‖ω ^ (k.val * b.val)‖ = 1 := by
    rw [norm_pow, hnorm, one_pow]
  choose C hC εk hεk hestimate using hbound
  -- A common positive interval works for the finitely many characters.
  have hinterval (t : Finset (Fin m)) :
      ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∀ k ∈ t, ε ≤ εk k := by
    induction t using Finset.induction_on with
    | empty => exact ⟨1, zero_lt_one, le_rfl, by simp⟩
    | @insert k t _ ih =>
        obtain ⟨ε, hε, hεone, hεle⟩ := ih
        refine ⟨min ε (εk k), lt_min hε (hεk k),
          (min_le_left _ _).trans hεone, ?_⟩
        intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact min_le_right _ _
        · exact (min_le_left _ _).trans (hεle j hj)
  obtain ⟨ε, hε, hεone, hεle⟩ := hinterval Finset.univ
  refine ⟨(∑ k : Fin m, C k) / (m : ℝ),
    div_nonneg (Finset.sum_nonneg fun k _ => hC k) hmR.le,
    ε, hε, hεone, ?_⟩
  intro a s hs hsε
  let w : ι → ℝ := fun i => Real.rpow (N i : ℝ) (-s)
  let L : ℝ := Real.log (1 / (s - 1))
  let P : ℝ := ∑' i : {i : ι // g i = a}, w i.val
  let F : Fin m → ℂ := fun k =>
    ∑' i : ι, ω ^ (k.val * (g i).val) * (w i : ℂ)
  let v : Fin m → ℂ := fun k => star (ω ^ (k.val * a.val))
  have hw (i : ι) : 0 ≤ w i := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hseries (k : Fin m) :
      Summable (fun i : ι => ω ^ (k.val * (g i).val) * (w i : ℂ)) := by
    apply (hsum s hs).of_norm_bounded
    intro i
    simpa only [norm_mul, hchar, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hw i), one_mul] using (le_rfl : w i ≤ w i)
  -- Finite Fourier inversion, with all infinite series justified by summability.
  have hfourier : (∑ k : Fin m, v k * F k) = (m : ℂ) * (P : ℂ) := by
    calc
      (∑ k : Fin m, v k * F k) =
          ∑ k : Fin m, ∑' i : ι,
            v k * (ω ^ (k.val * (g i).val) * (w i : ℂ)) := by
        apply Finset.sum_congr rfl
        intro k _
        exact (tsum_mul_left (a := v k)).symm
      _ = ∑' i : ι, ∑ k : Fin m,
            v k * (ω ^ (k.val * (g i).val) * (w i : ℂ)) :=
        (Summable.tsum_finsetSum (fun k _ => (hseries k).mul_left (v k))).symm
      _ = ∑' i : ι, (if g i = a then (m : ℂ) else 0) * (w i : ℂ) := by
        apply tsum_congr
        intro i
        rw [← Submission.p09_af497904fe_cwi_character_orthogonality m ω hm hω a (g i),
          Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro k _
        exact (mul_assoc _ _ _).symm
      _ = (m : ℂ) * (P : ℂ) := by
        have hfiber : (P : ℂ) =
            ∑' i : ι, ({i : ι | g i = a} : Set ι).indicator (fun i => (w i : ℂ)) i :=
          (Complex.ofReal_tsum (fun i : {i : ι // g i = a} => w i.val)).trans
            (tsum_subtype {i : ι | g i = a} (fun i => (w i : ℂ)))
        rw [hfiber, ← tsum_mul_left]
        apply tsum_congr
        intro i
        by_cases hi : g i = a <;> simp [Set.indicator, hi]
  have hmain : (∑ k : Fin m, v k *
      (if k.val = 0 then (L : ℂ) else 0)) = (L : ℂ) := by
    rw [Finset.sum_eq_single (⟨0, hm⟩ : Fin m)]
    · simp [v]
    · intro k _ hk
      have hk0 : k.val ≠ 0 := fun h => hk (Fin.ext h)
      simp [hk0]
    · simp
  have herror : (m : ℂ) * (P : ℂ) - (L : ℂ) =
      ∑ k : Fin m, v k * (F k - (if k.val = 0 then (L : ℂ) else 0)) := by
    simp only [mul_sub, Finset.sum_sub_distrib, hfourier, hmain]
  have hnormerror : ‖(m : ℂ) * (P : ℂ) - (L : ℂ)‖ ≤ ∑ k : Fin m, C k := by
    rw [herror]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro k _
    have hv : ‖v k‖ = 1 := by simpa [v] using hchar k a
    rw [norm_mul, hv, one_mul]
    exact hestimate k s hs (by linarith [hεle k (Finset.mem_univ k)])
  have hreal : |(m : ℝ) * P - L| ≤ ∑ k : Fin m, C k := by
    simpa only [← Complex.ofReal_natCast, ← Complex.ofReal_mul, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs] using hnormerror
  change |P - L / (m : ℝ)| ≤ (∑ k : Fin m, C k) / (m : ℝ)
  apply (le_div_iff₀ hmR).mpr
  have hid : (P - L / (m : ℝ)) * (m : ℝ) = (m : ℝ) * P - L := by
    rw [sub_mul, div_mul_cancel₀ _ (ne_of_gt hmR), mul_comm P (m : ℝ)]
  calc
    |P - L / (m : ℝ)| * (m : ℝ) = |(P - L / (m : ℝ)) * (m : ℝ)| := by
      rw [abs_mul, abs_of_pos hmR]
    _ = |(m : ℝ) * P - L| := congrArg abs hid
    _ ≤ ∑ k : Fin m, C k := hreal


theorem Submission.p09_af497904fe_fie_conjugate_separation :
    ∀ (E : IntermediateField ℚ (AlgebraicClosure ℚ))
      [FiniteDimensional ℚ E] [IsGalois ℚ E] (α : E),
      IsIntegral ℤ α → ∃ D : ℤ, D ≠ 0 ∧
        ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ D.natAbs →
          ∀ V : ValuationSubring E, V.LiesOverPrime ℓ →
            (∀ σ : E ≃ₐ[ℚ] E, σ α ∈ V) ∧
              ∀ σ τ : E ≃ₐ[ℚ] E,
                σ α - τ α ∈ V.nonunits → σ α = τ α := by
  intro E _ _ α hα
  obtain ⟨n, β, D, _, hβIntegral, hβConjugates, hD, hProduct⟩ :=
    Submission.p09_af497904fe_cs_integer_root_product E α hα
  refine ⟨D, hD, ?_⟩
  intro ℓ hℓ hℓD V hV
  obtain ⟨hβMem, hβSep⟩ :=
    Submission.p09_af497904fe_cs_valuation_product_separation
      n β D hβIntegral hProduct ℓ hℓ hℓD V hV
  constructor
  · intro σ
    obtain ⟨i, hi⟩ := hβConjugates σ
    rw [← hi]
    exact hβMem i
  · intro σ τ hστ
    obtain ⟨i, hi⟩ := hβConjugates σ
    obtain ⟨j, hj⟩ := hβConjugates τ
    rw [← hi, ← hj] at hστ ⊢
    exact hβSep i j hστ
    letI : B.IsPrime := hB
    letI : B.LiesOver (Ideal.span {(q : ℤ)}) := hBq
    exact IsCyclotomicExtension.Rat.eq_span_zeta_sub_one_of_liesOver q 0 C hξ B

theorem Submission.p09_af497904fe_csr_prime_residue_descent :
    ∀ (C D : IntermediateField ℚ (AlgebraicClosure ℚ))
      [FiniteDimensional ℚ C] [FiniteDimensional ℚ D] (q : ℕ)
      (A : Ideal (NumberField.RingOfIntegers C)),
      q.Prime → D ≤ C → A.IsPrime → A.LiesOver (Ideal.span {(q : ℤ)}) →
      Nat.card (NumberField.RingOfIntegers C ⧸ A) = q →
      (∀ B : Ideal (NumberField.RingOfIntegers C), B.IsPrime →
        B.LiesOver (Ideal.span {(q : ℤ)}) → B = A) →
      ∃ R : Ideal (NumberField.RingOfIntegers D), R.IsPrime ∧
        R.LiesOver (Ideal.span {(q : ℤ)}) ∧
        Ideal.ramificationIdx R ℤ = Module.finrank ℚ D := by
  intro C D _ _ q A hq hDC hA hAover hcard huniq
  classical
  let : NumberField C := ⟨⟩
  let : NumberField D := ⟨⟩
  let : Algebra D C := (IntermediateField.inclusion hDC).toRingHom.toAlgebra
  let : Fact q.Prime := ⟨hq⟩
  let p : Ideal ℤ := Ideal.span {(q : ℤ)}
  let R := A.under (NumberField.RingOfIntegers D)
  have : A.IsPrime := hA
  have : A.LiesOver p := hAover
  have : A.LiesOver R := Ideal.over_under _
  have : R.IsPrime := inferInstance
  have : R.LiesOver p := Ideal.LiesOver.tower_bot A R p
  have hRuniq (Q : Ideal (NumberField.RingOfIntegers D))
      (hQ : Q.IsPrime) (hQover : Q.LiesOver p) : Q = R := by
    have := hQ
    have := hQover
    obtain ⟨B, hB, hBQ⟩ := Q.exists_ideal_over_prime_of_isIntegral_of_isDomain
      (S := NumberField.RingOfIntegers C) (by
        rw [NumberField.RingOfIntegers.ker_algebraMap_eq_bot]
        exact bot_le)
    have := hB
    have : B.LiesOver Q := ⟨hBQ.symm⟩
    have : B.LiesOver p := Ideal.LiesOver.trans B Q p
    have hBA := huniq B hB inferInstance
    exact hBQ.symm.trans (congrArg (fun I => I.under (NumberField.RingOfIntegers D)) hBA)
  have hAdeg : A.inertiaDeg ℤ = 1 := by
    apply Nat.pow_right_injective hq.two_le
    simpa only [pow_one, Ideal.absNorm_apply, Submodule.cardQuot_apply, hcard] using
      (Ideal.pow_inertiaDeg q A)
  have hRdeg : R.inertiaDeg ℤ = 1 := by
    apply Nat.dvd_one.mp
    rw [← hAdeg]
    exact Ideal.inertiaDeg_below_dvd (R := ℤ) R A
  let r : p.primesOver (NumberField.RingOfIntegers D) := Ideal.primesOver.mk p R
  let : Unique (p.primesOver (NumberField.RingOfIntegers D)) :=
    { default := r
      uniq := fun Q => Subtype.ext (hRuniq Q.1 Q.2.1 Q.2.2) }
  let := Fintype.ofFinite (p.primesOver (NumberField.RingOfIntegers D))
  refine ⟨R, inferInstance, inferInstance, ?_⟩
  have hsum := Ideal.sum_ramification_inertia_eq_finrank p (NumberField.RingOfIntegers D)
  rw [Finset.univ_unique, Finset.sum_singleton] at hsum
  change R.ramificationIdx ℤ * R.inertiaDeg ℤ =
    Module.finrank ℤ (NumberField.RingOfIntegers D) at hsum
  simpa only [hRdeg, mul_one, NumberField.RingOfIntegers.rank] using hsum


theorem Submission.p09_af497904fe_ci_cyclotomic_subfield_ramification :
    ∀ (q : ℕ) (ζ : AlgebraicClosure ℚ), q.Prime → IsPrimitiveRoot ζ q →
      ∀ (D : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ D],
        D ≤ IntermediateField.adjoin ℚ ({ζ} : Set (AlgebraicClosure ℚ)) →
          ∃ R : Ideal (NumberField.RingOfIntegers D),
            R.IsPrime ∧ R.LiesOver (Ideal.span {(q : ℤ)}) ∧
              Ideal.ramificationIdx R ℤ = Module.finrank ℚ D := by
  intro q ζ hq hζ D _ hDC
  let C := IntermediateField.adjoin ℚ ({ζ} : Set (AlgebraicClosure ℚ))
  obtain ⟨hC, A, hA, hAq, hcard, huniq⟩ :=
    Submission.p09_af497904fe_csr_cyclotomic_prime_residue q ζ hq hζ
  let : FiniteDimensional ℚ C := hC
  exact Submission.p09_af497904fe_csr_prime_residue_descent
    C D q A hq hDC hA hAq hcard huniq


theorem Submission.p09_af497904fe_ci_unramified_subfield :
    ∀ (E D : IntermediateField ℚ (AlgebraicClosure ℚ))
      [FiniteDimensional ℚ E] [FiniteDimensional ℚ D] (q : ℕ),
      q.Prime → D ≤ E →
      (∀ P : Ideal (NumberField.RingOfIntegers E), P.IsPrime →
        P.LiesOver (Ideal.span {(q : ℤ)}) → Ideal.ramificationIdx P ℤ = 1) →
      ∀ R : Ideal (NumberField.RingOfIntegers D), R.IsPrime →
        R.LiesOver (Ideal.span {(q : ℤ)}) → Ideal.ramificationIdx R ℤ = 1 := by
  intro E D _ _ q _ hDE hE R hR hRq
  let : NumberField E := NumberField.of_module_finite ℚ E
  let : NumberField D := NumberField.of_module_finite ℚ D
  let : Algebra D E := (IntermediateField.inclusion hDE).toRingHom.toAlgebra
  let : R.IsPrime := hR
  let : R.LiesOver (Ideal.span {(q : ℤ)}) := hRq
  obtain ⟨P, hP, hPR⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain
      (S := NumberField.RingOfIntegers E) R (by
        rw [NumberField.RingOfIntegers.ker_algebraMap_eq_bot D E]
        exact bot_le)
  let : P.IsPrime := hP
  let : P.LiesOver R := ⟨hPR.symm⟩
  have hPq : P.LiesOver (Ideal.span {(q : ℤ)}) :=
    Ideal.LiesOver.trans P R (Ideal.span {(q : ℤ)})
  have hprod : Ideal.ramificationIdx R ℤ *
      Ideal.ramificationIdx P (NumberField.RingOfIntegers D) = 1 :=
    (Ideal.ramificationIdx_tower (R := ℤ) R P).symm.trans (hE P hP hPq)
  exact (mul_eq_one.mp hprod).1
