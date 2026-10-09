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

theorem Submission.p09_af497904fe_ce_cyclotomic_intersection :
    ∀ (E : IntermediateField ℚ (AlgebraicClosure ℚ))
      [FiniteDimensional ℚ E] [IsGalois ℚ E] (q : ℕ) (ζ : AlgebraicClosure ℚ),
      q.Prime → IsPrimitiveRoot ζ q →
      (∀ V : ValuationSubring E, V.LiesOverPrime q →
        ∀ τ : E ≃ₐ[ℚ] E, τ ∈ V.inertiaSubgroupIn ℚ → τ = 1) →
      E ⊓ IntermediateField.adjoin ℚ ({ζ} : Set (AlgebraicClosure ℚ)) = ⊥ := by
  intro E _ _ q ζ hq hζ hinertia
  let D := E ⊓ IntermediateField.adjoin ℚ ({ζ} : Set (AlgebraicClosure ℚ))
  have hDE : D ≤ E := inf_le_left
  have : FiniteDimensional ℚ D :=
    FiniteDimensional.of_injective (IntermediateField.inclusion hDE).toLinearMap
      (IntermediateField.inclusion_injective hDE)
  have hE := Submission.p09_af497904fe_ce_inertia_ramification E q hq hinertia
  obtain ⟨R, hRprime, hRover, hRdegree⟩ :=
    Submission.p09_af497904fe_ci_cyclotomic_subfield_ramification q ζ hq hζ D inf_le_right
  have hRone := Submission.p09_af497904fe_ci_unramified_subfield
    E D q hq hDE hE R hRprime hRover
  exact IntermediateField.finrank_eq_one_iff.mp (hRdegree.symm.trans hRone)
theorem Submission.p09_af497904fe_cfs_cyclic_weighted_infinitude :
    ∀ (ι : Type) (m : ℕ) (ω : ℂ) (N : ι → ℕ) (g : ι → ZMod m) (D : Set ι),
      0 < m → IsPrimitiveRoot ω m → (∀ i : ι, 2 ≤ N i) →
      (∀ s : ℝ, 1 < s → Summable (fun i : ι => Real.rpow (N i : ℝ) (-s))) →
      (∀ k : Fin m, ∃ C : ℝ, 0 ≤ C ∧ ∃ ε : ℝ, 0 < ε ∧
        ∀ s : ℝ, 1 < s → s < 1 + ε →
          ‖(∑' i : ι, ω ^ (k.val * (g i).val) *
              Complex.ofReal (Real.rpow (N i : ℝ) (-s))) -
            (if k.val = 0 then (Real.log (1 / (s - 1)) : ℂ) else 0)‖ ≤ C) →
      (∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, 1 < s → s < 2 →
        (∑' i : {i : ι // i ∈ D}, Real.rpow (N i.1 : ℝ) (-s)) ≤ C) →
      ∀ a : ZMod m, Set.Infinite {i : ι | i ∉ D ∧ g i = a} := by
  intro ι m ω N g D hm hω hN hsum hF hD a
  obtain ⟨K, _, ε, hε, hεone, hestimate⟩ :=
    Submission.p09_af497904fe_cwi_fiber_log_estimate ι m ω N g hm hω hN hsum hF
  obtain ⟨C, _, hD⟩ := hD
  have hmR : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
  have hlower (s : ℝ) (hs : 1 < s) (hsε : s < 1 + ε) :
      (1 / (m : ℝ)) * Real.log (1 / (s - 1)) - K ≤
        ∑' i : {i : ι // g i = a}, Real.rpow (N i.1 : ℝ) (-s) := by
    have h := (abs_le.mp (hestimate a s hs hsε)).1
    rw [one_div, mul_comm, ← div_eq_mul_inv]
    linarith only [h]
  have hinfinite := Submission.p09_af497904fe_cwi_infinite_diff_of_log_lower_bound
    ι N {i : ι | g i = a} D (1 / (m : ℝ)) K ε C hN hsum
    (one_div_pos.mpr hmR) hε hεone hlower hD
  change Set.Infinite {i : ι | g i = a ∧ i ∉ D} at hinfinite
  simpa only [and_comm] using hinfinite


theorem Submission.p09_af497904fe_ff_finite_inertia_exclusion :
    ∀ (E : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ E]
      [IsGalois ℚ E], ∃ S : Finset ℕ, ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S →
      ∀ V : ValuationSubring E, V.LiesOverPrime ℓ → ∀ τ : E ≃ₐ[ℚ] E,
        τ ∈ V.inertiaSubgroupIn ℚ → τ = 1 := by
  classical
  intro E _ _
  obtain ⟨α, hαint, hαgen⟩ := Submission.p09_af497904fe_fie_integral_primitive E
  obtain ⟨D, hD, hsep⟩ := Submission.p09_af497904fe_fie_conjugate_separation E α hαint
  refine ⟨D.natAbs.primeFactors, ?_⟩
  intro ℓ hℓ hℓS V hV τ hτ
  have hℓD : ¬ ℓ ∣ D.natAbs := by
    intro hdvd
    exact hℓS (hℓ.mem_primeFactors hdvd (Int.natAbs_ne_zero.mpr hD))
  obtain ⟨hmem, hseparate⟩ := hsep ℓ hℓ hℓD V hV
  -- Lift inertia membership to the kernel of the residue-field action.
  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hτ
  have hgtriv : MulSemiringAction.toRingAut (V.decompositionSubgroup ℚ)
      (IsLocalRing.ResidueField V) g = 1 := hg
  let a : V := ⟨α, by simpa using hmem 1⟩
  have hresidue : IsLocalRing.residue V (g • a) = IsLocalRing.residue V a := by
    change (MulSemiringAction.toRingAut (V.decompositionSubgroup ℚ)
      (IsLocalRing.ResidueField V) g) (IsLocalRing.residue V a) = _
    rw [hgtriv]
    rfl
  have hdiff : (g : E ≃ₐ[ℚ] E) α - α ∈ V.nonunits := by
    change ((g • a - a : V) : E) ∈ V.nonunits
    apply ValuationSubring.coe_mem_nonunits_iff.mpr
    apply (IsLocalRing.residue_eq_zero_iff _).mp
    rw [map_sub, hresidue, sub_self]
  have hfix : (g : E ≃ₐ[ℚ] E) α = α := by
    simpa using hseparate (g : E ≃ₐ[ℚ] E) 1 hdiff
  -- Agreement on the primitive element determines the rational automorphism.
  apply AlgEquiv.coe_toAlgHom_injective
  apply AlgHom.ext_of_adjoin_eq_top (IntermediateField.adjoin_eq_top_iff.mp hαgen)
  intro x hx
  obtain rfl := Set.mem_singleton_iff.mp hx
  exact hfix

theorem Submission.p09_af497904fe_rhc_20261009_adic_cyclotomic_character :
    ∀ {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
      [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] [CharZero 𝒪]
      (p : ℕ) [Fact p.Prime], (p : 𝒪) ∈ IsLocalRing.maximalIdeal 𝒪 →
      ∀ {R : Type} [CommRing R] [IsLocalRing R] [Algebra 𝒪 R],
      IsLocalHom (algebraMap 𝒪 R) →
      ∃ c : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Rˣ,
        (∀ n : ℕ, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ),
          FiniteDimensional ℚ F ∧
          ∀ σ τ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
            (∀ x ∈ F, σ x = τ x) →
            ((c σ : Rˣ) : R) - ((c τ : Rˣ) : R) ∈ IsLocalRing.maximalIdeal R ^ n) ∧
        (∀ (ℓ : ℕ), ℓ.Prime → ℓ ≠ p →
          ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
          ∀ σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
            P.IsFrobeniusAt σ ℓ → ((c σ : Rˣ) : R) = (ℓ : R)) := by
  classical
  intro 𝒪 _ _ _ _ _ p _ hp𝒪 R _ _ _ hl
  have hp : p.Prime := Fact.out
  have : NeZero p := ⟨hp.ne_zero⟩
  choose χ F hF hagree haction hfrob using
    fun n : ℕ => Submission.p09_af497904fe_finite_cyclotomic_character (p ^ n)
  let A (n : ℕ) (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) : ℕ :=
    (χ n g : ZMod (p ^ n)).val
  let a (n : ℕ) (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) : 𝒪 := A n g
  have hdivmem (n : ℕ) (z : ℤ) (hz : (z : ZMod (p ^ n)) = 0) :
      (z : 𝒪) ∈ maximalIdeal 𝒪 ^ n := by
    obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd z (p ^ n)).mp hz
    rw [hk, Int.cast_mul, Int.cast_natCast, Nat.cast_pow]
    exact (maximalIdeal 𝒪 ^ n).mul_mem_right _ (Ideal.pow_mem_pow hp𝒪 n)
  have hcong (n i j : ℕ) (hij : (i : ZMod (p ^ n)) = (j : ZMod (p ^ n))) :
      (i : 𝒪) - (j : 𝒪) ∈ maximalIdeal 𝒪 ^ n := by
    simpa only [Int.cast_sub, Int.cast_natCast] using
      hdivmem n ((i : ℤ) - (j : ℤ)) (by
        simpa only [Int.cast_sub, Int.cast_natCast, sub_eq_zero] using hij)
  have hcompat (n m : ℕ) (hnm : n ≤ m)
      (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
      a m g - a n g ∈ maximalIdeal 𝒪 ^ n := by
    apply hcong n (A m g) (A n g)
    obtain ⟨ζ, hζ⟩ :=
      HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) (p ^ n)
    have hζm : ζ ^ (p ^ m) = 1 :=
      (hζ.pow_eq_one_iff_dvd _).mpr (pow_dvd_pow p hnm)
    have he : ζ ^ A m g = ζ ^ A n g :=
      (haction m g ζ hζm).symm.trans (haction n g ζ hζ.pow_eq_one)
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mpr
    rw [hζ.eq_orderOf]
    exact (hζ.isOfFinOrder (NeZero.ne (p ^ n))).pow_eq_pow_iff_modEq.mp he
  have hone (n : ℕ) : a n 1 - 1 ∈ maximalIdeal 𝒪 ^ n := by
    simpa only [a, Nat.cast_one] using hcong n (A n 1) 1 (by
      simp [A])
  have hmul (n : ℕ) (g h : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
      a n (g * h) - a n g * a n h ∈ maximalIdeal 𝒪 ^ n := by
    simpa only [a, Nat.cast_mul] using hcong n (A n (g * h)) (A n g * A n h) (by
      simp [A])
  obtain ⟨b, hb, _⟩ :=
    Submission.p09_af497904fe_adic_character_lift (maximalIdeal 𝒪) a hcompat hone hmul
  let c := (Units.map (algebraMap 𝒪 R).toMonoidHom).comp b
  have hmap (n : ℕ) :
      (maximalIdeal 𝒪 ^ n).map (algebraMap 𝒪 R) ≤ maximalIdeal R ^ n := by
    rw [Ideal.map_pow]
    exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.mpr fun x hx =>
      Ideal.mem_comap.mpr (haveI := hl; map_nonunit (algebraMap 𝒪 R) x hx)) n
  refine ⟨c, ?_, ?_⟩
  · intro n
    refine ⟨F n, hF n, ?_⟩
    intro σ τ hστ
    have ha : a n σ = a n τ := by
      simp only [a, A, hagree n σ τ hστ]
    have hd : (b σ : 𝒪) - (b τ : 𝒪) ∈ maximalIdeal 𝒪 ^ n := by
      convert (maximalIdeal 𝒪 ^ n).sub_mem (hb n σ) (hb n τ) using 1
      rw [ha]
      ring
    change algebraMap 𝒪 R (b σ : 𝒪) - algebraMap 𝒪 R (b τ : 𝒪) ∈ maximalIdeal R ^ n
    rw [← map_sub]
    exact hmap n (Ideal.mem_map_of_mem (algebraMap 𝒪 R) hd)
  · intro ℓ hℓ hℓp P hP σ hσ
    have he : (b σ : 𝒪) = (ℓ : 𝒪) := by
      apply (IsHausdorff.eq_iff_smodEq (I := maximalIdeal 𝒪)).mpr
      intro n
      rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top]
      have hℓn : ¬ ℓ ∣ p ^ n := fun h =>
        hℓp (Nat.prime_eq_prime_of_dvd_pow hℓ hp h)
      have hf : a n σ - (ℓ : 𝒪) ∈ maximalIdeal 𝒪 ^ n := by
        apply hcong n (A n σ) ℓ
        simp only [A, ZMod.natCast_zmod_val, hfrob n ℓ hℓ hℓn P hP σ hσ,
          ZMod.coe_unitOfCoprime]
      convert (maximalIdeal 𝒪 ^ n).add_mem (hb n σ) hf using 1
      ring
    change algebraMap 𝒪 R (b σ : 𝒪) = (ℓ : R)
    rw [he, map_natCast]
/-- A finite rational Galois automorphism is the restriction of an automorphism
of a prime cyclotomic extension of a suitable fixed field. -/
theorem Submission.p09_af497904fe_ff_cyclotomic_envelope :
    ∀ (E : IntermediateField ℚ (AlgebraicClosure ℚ))
      [FiniteDimensional ℚ E] [IsGalois ℚ E] (g : E ≃ₐ[ℚ] E),
      ∃ M : IntermediateField ℚ (AlgebraicClosure ℚ),
        FiniteDimensional ℚ M ∧ IsGalois ℚ M ∧
        ∃ (ι : E →ₐ[ℚ] M) (F : IntermediateField ℚ M) (q : ℕ) (ζ : M)
          (h : M ≃ₐ[F] M), q.Prime ∧ IsPrimitiveRoot ζ q ∧
          IntermediateField.adjoin F ({ζ} : Set M) = ⊤ ∧
          ∀ x : E, h (ι x) = ι (g x) := by
  classical
  intro E _ _ g
  -- Choose an unramified prime whose cyclotomic group contains an element
  -- of the same order as g.
  obtain ⟨S, hS⟩ := Submission.p09_af497904fe_ff_finite_inertia_exclusion E
  obtain ⟨q, hq, hqS, hqm⟩ :=
    Nat.exists_prime_gt_modEq_one (S.sup id + 2) (orderOf_pos g).ne'
  have hqnot : q ∉ S := by
    intro h
    have hle : q ≤ S.sup id := Finset.le_sup (f := id) h
    omega
  have hmdvd : orderOf g ∣ q - 1 :=
    (Nat.modEq_iff_dvd' hq.pos).mp hqm.symm
  let : Fact q.Prime := ⟨hq⟩
  let : NeZero q := ⟨hq.ne_zero⟩
  obtain ⟨ζ₀, hζ₀⟩ :=
    HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) q
  let : Algebra.IsIntegral ℚ (AlgebraicClosure ℚ) :=
    Algebra.isAlgebraic_iff_isIntegral.mp (AlgebraicClosure.isAlgebraic ℚ)
  let C := IntermediateField.adjoin ℚ ({ζ₀} : Set (AlgebraicClosure ℚ))
  let : IsCyclotomicExtension {q} ℚ C :=
    hζ₀.intermediateField_adjoin_isCyclotomicExtension ℚ
  let : FiniteDimensional ℚ C := IsCyclotomicExtension.finiteDimensional {q} ℚ C
  let : IsGalois ℚ C := IsCyclotomicExtension.isGalois {q} ℚ C
  have hEC : E ⊓ C = ⊥ :=
    Submission.p09_af497904fe_ce_cyclotomic_intersection E q ζ₀ hq hζ₀
      (hS q hq hqnot)
  let ζC : C := ⟨ζ₀, IntermediateField.mem_adjoin_simple_self ℚ ζ₀⟩
  have hζC : IsPrimitiveRoot ζC q :=
    (IsPrimitiveRoot.coe_submonoidClass_iff).mp hζ₀
  let e : (C ≃ₐ[ℚ] C) ≃* (ZMod q)ˣ :=
    IsCyclotomicExtension.autEquivPow C (Polynomial.cyclotomic.irreducible_rat hq.pos)
  obtain ⟨b, hb⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod q)ˣ)
  have hbq : orderOf b = q - 1 := by
    simpa only [Nat.card_eq_fintype_card, ZMod.card_units] using hb
  let a : C ≃ₐ[ℚ] C := e.symm (b ^ (orderOf b / orderOf g))
  have ha : orderOf a = orderOf g := by
    rw [show orderOf a = orderOf (b ^ (orderOf b / orderOf g)) from
      e.symm.orderOf_eq _]
    exact orderOf_pow_orderOf_div (orderOf_pos b).ne' (by simpa only [hbq] using hmdvd)
  -- The disjoint compositum permits the prescribed pair of restrictions.
  let M := E ⊔ C
  let : IsGalois ℚ M := by
    have hnE : Normal ℚ E := IsGalois.to_normal
    have hnC : Normal ℚ C := IsGalois.to_normal
    exact { to_normal :=
      @IntermediateField.normal_sup ℚ (AlgebraicClosure ℚ) _ _ _ E C hnE hnC }
  let ι : E →ₐ[ℚ] M := IntermediateField.inclusion le_sup_left
  let j : C →ₐ[ℚ] M := IntermediateField.inclusion le_sup_right
  obtain ⟨u, hu, _⟩ := Submission.p09_af497904fe_ce_compositum_pair E C hEC g a
  have huE (x : E) : u (ι x) = ι (g x) := hu.1 x
  have huC (x : C) : u (j x) = j (a x) := hu.2 x
  have hpowE (n : ℕ) (x : E) : (u ^ n) (ι x) = ι ((g ^ n) x) := by
    induction n generalizing x with
    | zero => rfl
    | succ n ih =>
        rw [pow_succ', AlgEquiv.mul_apply, ih, huE, pow_succ', AlgEquiv.mul_apply]
  have hpowC (n : ℕ) (x : C) : (u ^ n) (j x) = j ((a ^ n) x) := by
    induction n generalizing x with
    | zero => rfl
    | succ n ih =>
        rw [pow_succ', AlgEquiv.mul_apply, ih, huC, pow_succ', AlgEquiv.mul_apply]
  let ζ : M := j ζC
  have hζ : IsPrimitiveRoot ζ q := hζC.map_of_injective j.injective
  -- Fixing ζ forces the cyclotomic restriction, then the E restriction,
  -- and finally the entire compositum automorphism to be trivial.
  have hfaithful (n : ℕ) (hn : (u ^ n) ζ = ζ) : u ^ n = 1 := by
    have hanζ : (a ^ n) ζC = ζC := by
      apply j.injective
      exact (hpowC n ζC).symm.trans hn
    have han : a ^ n = 1 := by
      apply AlgEquiv.coe_toAlgHom_injective
      apply IntermediateField.adjoin_algHom_ext ℚ
      intro x hx
      obtain rfl : x = ζ₀ := Set.mem_singleton_iff.mp hx
      exact hanζ
    have hgn : g ^ n = 1 := by
      apply orderOf_dvd_iff_pow_eq_one.mp
      rw [← ha]
      exact orderOf_dvd_of_pow_eq_one han
    obtain ⟨v, _, hv⟩ :=
      Submission.p09_af497904fe_ce_compositum_pair E C hEC 1 1
    have hun : u ^ n = v := by
      apply hv
      constructor
      · intro x
        simpa only [hgn, AlgEquiv.one_apply, ι] using! hpowE n x
      · intro x
        simpa only [han, AlgEquiv.one_apply, j] using! hpowC n x
    have hvone : (1 : M ≃ₐ[ℚ] M) = v := hv 1 ⟨fun _ => rfl, fun _ => rfl⟩
    exact hun.trans hvone.symm
  obtain ⟨F, h, hgen, hh⟩ :=
    Submission.p09_af497904fe_ce_fixed_field_generator M u ζ hfaithful
  exact ⟨M, inferInstance, inferInstance, ι, F, q, ζ, h, hq, hζ, hgen,
    fun x => (hh (ι x)).trans (huE x)⟩
theorem Submission.p09_af497904fe_cmc_40fde013_floor_remainder :
    ∀ (a : ℕ → ℝ) (κ α C : ℝ), 0 ≤ α → 0 ≤ C →
      (∀ n : ℕ, 1 ≤ n →
        |(∑ k ∈ Finset.Icc 1 n, a k) - κ * (n : ℝ)| ≤ C * (n : ℝ) ^ α) →
      Measurable (fun t : ℝ => (∑ k ∈ Finset.Icc 1 (Nat.floor t), a k) - κ * t) ∧
        ∀ t : ℝ, 1 ≤ t →
          |(∑ k ∈ Finset.Icc 1 (Nat.floor t), a k) - κ * t| ≤ (C + |κ|) * t ^ α := by
  intro a κ α C hα hC hcount
  constructor
  · exact ((measurable_of_countable (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, a k)).comp
      Nat.measurable_floor).sub (measurable_const.mul measurable_id)
  · intro t ht
    have ht0 : 0 ≤ t := le_trans zero_le_one ht
    have hn : 1 ≤ Nat.floor t := Nat.le_floor (by simpa using ht)
    have hfloor : (Nat.floor t : ℝ) ≤ t := Nat.floor_le ht0
    have hpow : (Nat.floor t : ℝ) ^ α ≤ t ^ α :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) hfloor hα
    have hone : 1 ≤ t ^ α := Real.one_le_rpow ht hα
    have herror : |κ * ((Nat.floor t : ℝ) - t)| ≤ |κ| := by
      rw [abs_mul]
      calc
        |κ| * |(Nat.floor t : ℝ) - t| ≤ |κ| * 1 :=
          mul_le_mul_of_nonneg_left (Nat.abs_floor_sub_le ht0) (abs_nonneg κ)
        _ = |κ| := mul_one _
    calc
      |(∑ k ∈ Finset.Icc 1 (Nat.floor t), a k) - κ * t| =
          |((∑ k ∈ Finset.Icc 1 (Nat.floor t), a k) - κ * (Nat.floor t : ℝ)) +
            κ * ((Nat.floor t : ℝ) - t)| := by congr 1; ring
      _ ≤ |(∑ k ∈ Finset.Icc 1 (Nat.floor t), a k) - κ * (Nat.floor t : ℝ)| +
          |κ * ((Nat.floor t : ℝ) - t)| := abs_add_le _ _
      _ ≤ C * (Nat.floor t : ℝ) ^ α + |κ| := add_le_add (hcount _ hn) herror
      _ ≤ C * t ^ α + |κ| * t ^ α := by
        exact add_le_add (mul_le_mul_of_nonneg_left hpow hC)
          (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hone (abs_nonneg κ))
      _ = (C + |κ|) * t ^ α := (add_mul _ _ _).symm
theorem Submission.p09_af497904fe_cmc_40fde013_mellin_tail_holomorphic :
    ∀ (R : ℝ → ℝ) (α M : ℝ), Measurable R → 0 ≤ M →
      (∀ t : ℝ, 1 ≤ t → |R t| ≤ M * t ^ α) →
      (∀ s : ℂ, α < s.re → MeasureTheory.IntegrableOn
        (fun t : ℝ => (R t : ℂ) * (t : ℂ) ^ (-(s + 1))) (Set.Ioi (1 : ℝ))) ∧
      DifferentiableOn ℂ (fun s : ℂ => MeasureTheory.integral
        (μ := MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ)))
        (fun t : ℝ => (R t : ℂ) * (t : ℂ) ^ (-(s + 1)))) {s : ℂ | α < s.re} := by
  intro R α M hR hM hbound
  let μ := MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ))
  let F : ℂ → ℝ → ℂ := fun s t => (R t : ℂ) * (t : ℂ) ^ (-(s + 1))
  have hmeas (s : ℂ) : MeasureTheory.AEStronglyMeasurable (F s) μ := by
    refine (Complex.continuous_ofReal.measurable.comp hR).aestronglyMeasurable.mul ?_
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    intro t ht
    exact (Complex.continuousAt_ofReal_cpow_const t (-(s + 1))
      (Or.inr (ne_of_gt (lt_trans zero_lt_one ht)))).continuousWithinAt
  have hnorm (s : ℂ) (t : ℝ) (ht : 1 < t) :
      ‖F s t‖ ≤ M * t ^ (α - s.re - 1) := by
    have ht0 : 0 < t := lt_trans zero_lt_one ht
    dsimp [F]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_cpow_eq_rpow_re_of_pos ht0]
    calc
      |R t| * t ^ (-(s + 1)).re ≤ (M * t ^ α) * t ^ (-(s + 1)).re :=
        mul_le_mul_of_nonneg_right (hbound t ht.le) (Real.rpow_nonneg ht0.le _)
      _ = M * t ^ (α - s.re - 1) := by
        rw [mul_assoc, ← Real.rpow_add ht0]
        congr 2
        simp only [Complex.neg_re, Complex.add_re, Complex.one_re]
        ring
  have hint (s : ℂ) (hs : α < s.re) : MeasureTheory.Integrable (F s) μ := by
    refine ((integrableOn_Ioi_rpow_of_lt (by linarith : α - s.re - 1 < -1)
      zero_lt_one).const_mul M).mono' (hmeas s) ?_
    exact (MeasureTheory.ae_restrict_mem measurableSet_Ioi).mono fun t ht => hnorm s t ht
  refine ⟨hint, ?_⟩
  intro s hs
  have hs' : α < s.re := hs
  let ε : ℝ := (s.re - α) / 4
  have hε : 0 < ε := by dsimp [ε]; linarith
  let F' : ℂ → ℝ → ℂ := fun z t => -((Real.log t : ℂ) * F z t)
  let bound : ℝ → ℝ := fun t => (M / ε) * t ^ (α - s.re + 2 * ε - 1)
  have hmeas' : MeasureTheory.AEStronglyMeasurable (F' s) μ := by
    exact ((Complex.continuous_ofReal.measurable.comp Real.measurable_log).aestronglyMeasurable.mul (hmeas s)).neg
  have hbound' : ∀ᵐ t : ℝ ∂μ, ∀ z ∈ Metric.ball s ε, ‖F' z t‖ ≤ bound t := by
    refine (MeasureTheory.ae_restrict_mem measurableSet_Ioi).mono fun t ht z hz => ?_
    have ht0 : 0 < t := lt_trans zero_lt_one ht
    have hzre : s.re - ε ≤ z.re := by
      have hzn := Complex.re_le_norm (s - z)
      rw [Complex.sub_re] at hzn
      rw [Metric.mem_ball, dist_comm, dist_eq_norm] at hz
      linarith
    have hp : ‖F z t‖ ≤ M * t ^ (α - s.re + ε - 1) :=
      (hnorm z t ht).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le ht.le (by linarith)) hM)
    dsimp [F', bound]
    rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.log_nonneg ht.le)]
    calc
      Real.log t * ‖F z t‖ ≤ (t ^ ε / ε) * (M * t ^ (α - s.re + ε - 1)) :=
        mul_le_mul (Real.log_le_rpow_div ht0.le hε) hp (norm_nonneg _)
          (by positivity)
      _ = (M / ε) * t ^ (α - s.re + 2 * ε - 1) := by
        calc
          _ = (M / ε) * (t ^ ε * t ^ (α - s.re + ε - 1)) := by ring
          _ = _ := by rw [← Real.rpow_add ht0]; congr 2; ring
  have hbound_int : MeasureTheory.Integrable bound μ := by
    exact (integrableOn_Ioi_rpow_of_lt
      (by dsimp [ε]; linarith : α - s.re + 2 * ε - 1 < -1)
      zero_lt_one).const_mul (M / ε)
  have hderiv : ∀ᵐ t : ℝ ∂μ, ∀ z ∈ Metric.ball s ε,
      HasDerivAt (fun w => F w t) (F' z t) z := by
    refine (MeasureTheory.ae_restrict_mem measurableSet_Ioi).mono fun t ht z _ => ?_
    have ht0 : 0 < t := lt_trans zero_lt_one ht
    have hd := (((hasDerivAt_id z).add_const 1).neg.const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr ht0.ne'))).const_mul (R t : ℂ)
    convert! hd using 1
    dsimp [F', F]
    rw [← Complex.ofReal_log ht0.le]
    ring
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds s hε) (Filter.Eventually.of_forall hmeas)
    (hint s hs') hmeas' hbound' hbound_int hderiv).2.differentiableAt.differentiableWithinAt
open Filter Asymptotics MeasureTheory in
theorem Submission.p09_af497904fe_cfs_counting_mellin_continuation :
    ∀ (a : ℕ → ℝ) (κ α : ℝ), (∀ n : ℕ, 0 ≤ a n) → 0 ≤ α → α < 1 →
      (∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 1 ≤ n →
        |(∑ k ∈ Finset.Icc 1 n, a k) - κ * (n : ℝ)| ≤ C * (n : ℝ) ^ α) →
      ∃ H : ℂ → ℂ, DifferentiableOn ℂ H {s : ℂ | α < s.re} ∧
        ∀ s : ℂ, 1 < s.re → LSeries (fun n : ℕ => (a n : ℂ)) s =
          (κ : ℂ) / (s - 1) + H s := by
  intro a κ α ha hα hα1 ⟨C, hC, hcount⟩
  -- The counting estimate and positivity give the linear bound used in Abel summation.
  have hO : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, a k) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ (1 : ℝ)) := by
    refine isBigO_iff.mpr ⟨C + |κ|, ?_⟩
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hsum : 0 ≤ ∑ k ∈ Finset.Icc 1 n, a k :=
      Finset.sum_nonneg fun k _ => ha k
    have hpow : (n : ℝ) ^ α ≤ n := by
      simpa using Real.rpow_le_rpow_of_exponent_le hn' hα1.le
    have hupper := (le_abs_self _).trans (hcount n hn)
    have hκ := mul_le_mul_of_nonneg_right (le_abs_self κ) (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    simp only [Real.norm_eq_abs, Real.rpow_one, abs_of_nonneg hsum,
      abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    nlinarith [mul_le_mul_of_nonneg_left hpow hC]
  let R : ℝ → ℝ := fun t => (∑ k ∈ Finset.Icc 1 (Nat.floor t), a k) - κ * t
  obtain ⟨hRm, hRb⟩ :=
    Submission.p09_af497904fe_cmc_40fde013_floor_remainder a κ α C hα hC hcount
  obtain ⟨hIint, hIdiff⟩ :=
    Submission.p09_af497904fe_cmc_40fde013_mellin_tail_holomorphic R α (C + |κ|)
      hRm (add_nonneg hC (abs_nonneg κ)) hRb
  let I : ℂ → ℂ := fun s => ∫ t in Set.Ioi (1 : ℝ),
    (R t : ℂ) * (t : ℂ) ^ (-(s + 1))
  -- The total integral defines a function everywhere; only the stated half-plane is used.
  refine ⟨fun s => (κ : ℂ) + s * I s,
    (differentiableOn_const (κ : ℂ)).add (differentiableOn_id.mul hIdiff), ?_⟩
  intro s hs
  have hsα : α < s.re := hα1.trans hs
  have hsneg : (-s).re < -1 := by simpa using neg_lt_neg hs
  have hs1 : s - 1 ≠ 0 := by
    apply sub_ne_zero.mpr
    intro h
    have := congrArg Complex.re h
    simp only [Complex.one_re] at this
    linarith
  have hpint : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-s)) (Set.Ioi 1) :=
    integrableOn_Ioi_cpow_of_lt hsneg zero_lt_one
  have hpole : (∫ t : ℝ in Set.Ioi 1, (t : ℂ) ^ (-s)) = 1 / (s - 1) := by
    rw [integral_Ioi_cpow_of_lt hsneg zero_lt_one, Complex.ofReal_one,
      Complex.one_cpow, show -s + 1 = -(s - 1) by ring, neg_div_neg_eq]
  have hsplit :
      (∫ t in Set.Ioi (1 : ℝ),
        (∑ k ∈ Finset.Icc 1 (Nat.floor t), (a k : ℂ)) * (t : ℂ) ^ (-(s + 1))) =
      (κ : ℂ) / (s - 1) + I s := by
    calc
      _ = ∫ t in Set.Ioi (1 : ℝ),
          ((κ : ℂ) * (t : ℂ) ^ (-s) + (R t : ℂ) * (t : ℂ) ^ (-(s + 1))) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        have ht0 : (t : ℂ) ≠ 0 :=
          Complex.ofReal_ne_zero.mpr (ne_of_gt (lt_trans zero_lt_one ht))
        have hpower : (t : ℂ) * (t : ℂ) ^ (-(s + 1)) = (t : ℂ) ^ (-s) := by
          rw [show -(s + 1) = -s - 1 by ring, Complex.cpow_sub _ _ ht0,
            Complex.cpow_one, mul_div_cancel₀ _ ht0]
        simp only [R, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_sum]
        rw [sub_mul, mul_assoc (κ : ℂ), hpower]
        ring
      _ = (κ : ℂ) / (s - 1) + I s := by
        rw [integral_add (hpint.const_mul (κ : ℂ)) (hIint s hsα),
          integral_const_mul, hpole]
        simp only [I, mul_one_div]
  rw [LSeries_eq_mul_integral_of_nonneg a zero_le_one hs hO ha, hsplit]
  dsimp only
  field_simp [hs1]
  ring


namespace Submission

theorem p09_af497904fe_adic_cyclotomic_character
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [CharZero 𝒪]
    (p : ℕ) [Fact p.Prime] (hp𝒪 : (p : 𝒪) ∈ maximalIdeal 𝒪)
    {R : Type} [CommRing R] [IsLocalRing R] [Algebra 𝒪 R]
    (hl : IsLocalHom (algebraMap 𝒪 R)) :
    ∃ c : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Rˣ,
      (∀ n : ℕ, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ),
        FiniteDimensional ℚ F ∧
        ∀ σ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
          (∀ x ∈ F, σ x = τ x) →
          ((c σ : Rˣ) : R) - ((c τ : Rˣ) : R) ∈ maximalIdeal R ^ n) ∧
      (∀ (ℓ : ℕ), ℓ.Prime → ℓ ≠ p →
        ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
          P.IsFrobeniusAt σ ℓ → ((c σ : Rˣ) : R) = (ℓ : R)) := by
  classical
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  choose χ F hF hcontrol haction hfrob using
    fun n : ℕ => p09_af497904fe_finite_cyclotomic_character (p ^ n)
  let A (n : ℕ) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) : ℕ :=
    (χ n σ : ZMod (p ^ n)).val
  let a (n : ℕ) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) : 𝒪 := A n σ

  -- Divisibility by p^n becomes membership in the n-th maximal-ideal power.
  have hcast (n : ℕ) (z : ℤ) (hz : (z : ZMod (p ^ n)) = 0) :
      (z : 𝒪) ∈ maximalIdeal 𝒪 ^ n := by
    obtain ⟨t, ht⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd z (p ^ n)).mp hz
    rw [ht, Int.cast_mul, Int.cast_natCast, Nat.cast_pow]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hp𝒪 n)

  -- A primitive root at the lower level is also a root at the higher level.
  have hcompatible (n m : ℕ) (hnm : n ≤ m)
      (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
      a m σ - a n σ ∈ maximalIdeal 𝒪 ^ n := by
    obtain ⟨ζ, hζ⟩ :=
      HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) (p ^ n)
    have hζm : ζ ^ (p ^ m) = 1 :=
      (hζ.pow_eq_one_iff_dvd _).mpr (pow_dvd_pow p hnm)
    have he : ζ ^ A m σ = ζ ^ A n σ :=
      (haction m σ ζ hζm).symm.trans (haction n σ ζ hζ.pow_eq_one)
    have hm : A m σ ≡ A n σ [MOD p ^ n] := by
      rw [hζ.eq_orderOf]
      exact (hζ.isOfFinOrder (NeZero.ne _)).pow_eq_pow_iff_modEq.mp he
    have hz : (((A m σ : ℤ) - A n σ : ℤ) : ZMod (p ^ n)) = 0 := by
      rw [Int.cast_sub, Int.cast_natCast, Int.cast_natCast, sub_eq_zero]
      exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr hm
    simpa only [Int.cast_sub, Int.cast_natCast] using hcast n _ hz
  have hone (n : ℕ) : a n 1 - 1 ∈ maximalIdeal 𝒪 ^ n := by
    have hz : (((A n 1 : ℤ) - 1 : ℤ) : ZMod (p ^ n)) = 0 := by
      simp [A]
    simpa only [Int.cast_sub, Int.cast_natCast, Int.cast_one] using hcast n _ hz
  have hmul (n : ℕ) (σ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
      a n (σ * τ) - a n σ * a n τ ∈ maximalIdeal 𝒪 ^ n := by
    have hz : (((A n (σ * τ) : ℤ) - (A n σ : ℤ) * A n τ : ℤ) :
        ZMod (p ^ n)) = 0 := by
      simp [A]
    simpa only [Int.cast_sub, Int.cast_mul, Int.cast_natCast] using hcast n _ hz
  obtain ⟨b, hb, _⟩ := p09_af497904fe_adic_character_lift
    (maximalIdeal 𝒪) a hcompatible hone hmul

  let c : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Rˣ :=
    (Units.map (algebraMap 𝒪 R).toMonoidHom).comp b
  have hmap (n : ℕ) : (maximalIdeal 𝒪 ^ n).map (algebraMap 𝒪 R) ≤
      maximalIdeal R ^ n := by
    rw [Ideal.map_pow]
    apply Ideal.pow_right_mono _ n
    apply Ideal.map_le_iff_le_comap.mpr
    intro x hx
    have := hl
    exact map_nonunit (algebraMap 𝒪 R) x hx
  refine ⟨c, ?_, ?_⟩
  · intro n
    refine ⟨F n, hF n, ?_⟩
    intro σ τ hστ
    have ha : a n σ = a n τ := by
      simp only [a, A, hcontrol n σ τ hστ]
    have hsub : (b σ : 𝒪) - (b τ : 𝒪) ∈ maximalIdeal 𝒪 ^ n := by
      have h := (maximalIdeal 𝒪 ^ n).sub_mem (hb n σ) (hb n τ)
      simpa only [ha, sub_sub_sub_cancel_right] using h
    change algebraMap 𝒪 R (b σ : 𝒪) - algebraMap 𝒪 R (b τ : 𝒪) ∈ maximalIdeal R ^ n
    rw [← map_sub]
    exact hmap n (Ideal.mem_map_of_mem (algebraMap 𝒪 R) hsub)
  · intro ℓ hℓ hℓp P hP σ hσ
    have hvalue : (b σ : 𝒪) = (ℓ : 𝒪) := by
      apply (IsHausdorff.eq_iff_smodEq (I := maximalIdeal 𝒪)).mpr
      intro n
      have hℓn : ¬ ℓ ∣ p ^ n := by
        intro h
        exact hℓp ((Nat.prime_dvd_prime_iff_eq hℓ (Fact.out : p.Prime)).mp
          (hℓ.dvd_of_dvd_pow h))
      have hz : (((A n σ : ℤ) - ℓ : ℤ) : ZMod (p ^ n)) = 0 := by
        simp only [Int.cast_sub, Int.cast_natCast, A, ZMod.natCast_zmod_val,
          hfrob n ℓ hℓ hℓn P hP σ hσ, ZMod.coe_unitOfCoprime, sub_self]
      have ha : a n σ - (ℓ : 𝒪) ∈ maximalIdeal 𝒪 ^ n := by
        simpa only [Int.cast_sub, Int.cast_natCast] using hcast n _ hz
      rw [SModEq.sub_mem, smul_eq_mul, ← Ideal.one_eq_top, mul_one]
      simpa only [sub_add_sub_cancel] using (maximalIdeal 𝒪 ^ n).add_mem (hb n σ) ha
    change algebraMap 𝒪 R (b σ : 𝒪) = (ℓ : R)
    rw [hvalue, map_natCast]

end Submission
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
theorem Submission.p09_af497904fe_cfs_cyclic_weighted_infinitude :
    ∀ (ι : Type) (m : ℕ) (ω : ℂ) (N : ι → ℕ) (g : ι → ZMod m) (D : Set ι),
      0 < m → IsPrimitiveRoot ω m → (∀ i : ι, 2 ≤ N i) →
      (∀ s : ℝ, 1 < s → Summable (fun i : ι => Real.rpow (N i : ℝ) (-s))) →
      (∀ k : Fin m, ∃ C : ℝ, 0 ≤ C ∧ ∃ ε : ℝ, 0 < ε ∧
        ∀ s : ℝ, 1 < s → s < 1 + ε →
          ‖(∑' i : ι, ω ^ (k.val * (g i).val) *
              Complex.ofReal (Real.rpow (N i : ℝ) (-s))) -
            (if k.val = 0 then (Real.log (1 / (s - 1)) : ℂ) else 0)‖ ≤ C) →
      (∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, 1 < s → s < 2 →
        (∑' i : {i : ι // i ∈ D}, Real.rpow (N i.1 : ℝ) (-s)) ≤ C) →
      ∀ a : ZMod m, Set.Infinite {i : ι | i ∉ D ∧ g i = a} := by
  intro ι m ω N g D hm hω hN hsum hF hD a
  obtain ⟨K, _, ε, hε, hεone, hestimate⟩ :=
    Submission.p09_af497904fe_cwi_fiber_log_estimate ι m ω N g hm hω hN hsum hF
  obtain ⟨C, _, hD⟩ := hD
  have hmR : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
  have hlower (s : ℝ) (hs : 1 < s) (hsε : s < 1 + ε) :
      (1 / (m : ℝ)) * Real.log (1 / (s - 1)) - K ≤
        ∑' i : {i : ι // g i = a}, Real.rpow (N i.1 : ℝ) (-s) := by
    have h := (abs_le.mp (hestimate a s hs hsε)).1
    rw [one_div, mul_comm, ← div_eq_mul_inv]
    linarith only [h]
  have hinfinite := Submission.p09_af497904fe_cwi_infinite_diff_of_log_lower_bound
    ι N {i : ι | g i = a} D (1 / (m : ℝ)) K ε C hN hsum
    (one_div_pos.mpr hmR) hε hεone hlower hD
  change Set.Infinite {i : ι | g i = a ∧ i ∉ D} at hinfinite
  simpa only [and_comm] using hinfinite
open scoped nonZeroDivisors in
open Filter Topology Ideal Asymptotics UniqueFactorizationMonoid in
/-- Speculative parent draft. The arithmetic input obligation at the end is still open. -/
theorem Submission.p09_af497904fe_ff_cyclotomic_supply :
    ∀ (M : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ M]
      (F : IntermediateField ℚ M) (q : ℕ) (ζ : M), q.Prime →
      IsPrimitiveRoot ζ q → IntermediateField.adjoin F ({ζ} : Set M) = ⊤ →
      ∀ (h : M ≃ₐ[F] M) (B : Finset ℕ),
        ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ∉ B ∧ ∃ W : ValuationSubring M,
          W.LiesOverPrime ℓ ∧ W.IsFrobeniusAt h ℓ := by
  classical
  intro M _ F q ζ hq hζ hadjoin h B
  -- Steps 1, 2, and 21: the cyclotomic group and its actual residue action.
  let : Fact q.Prime := ⟨hq⟩
  let : NeZero q := ⟨hq.ne_zero⟩
  let : NumberField M := ⟨⟩
  let : NumberField F := inferInstance
  let : IsCyclotomicExtension {q} F (⊤ : IntermediateField F M) :=
    hadjoin ▸ hζ.intermediateField_adjoin_isCyclotomicExtension F
  let : IsCyclotomicExtension {q} F M :=
    IsCyclotomicExtension.equiv {q} F (⊤ : IntermediateField F M)
      IntermediateField.topEquiv
  let : IsGalois F M := IsCyclotomicExtension.isGalois {q} F M
  let J := M ≃ₐ[F] M
  have hexponent : Function.Injective (hζ.autToPow F) := hζ.autToPow_injective F
  let : IsCyclic J := isCyclic_of_injective (hζ.autToPow F) hexponent
  let m := Nat.card J
  have hm : 0 < m := Nat.card_pos
  let e : Multiplicative (ZMod m) ≃* J := zmodCyclicMulEquiv (inferInstance : IsCyclic J)
  let code : J → ZMod m := fun σ => Multiplicative.toAdd (e.symm σ)
  have hcode : Function.Injective code := by
    intro σ τ heq
    apply e.symm.injective
    exact heq
  let ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / m)
  have hω : IsPrimitiveRoot ω m := Complex.isPrimitiveRoot_exp m hm.ne'
  have hrootmem (W : ValuationSubring M) (x : M) (hx : x ^ q = 1) :
      x ∈ W ∧ x⁻¹ ∈ W := by
    have hi : x ^ (q - 1) = x⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      rw [pow_sub_one_mul hq.ne_zero, hx]
    have hback : (x⁻¹) ^ (q - 1) = x := by rw [inv_pow, hi, inv_inv]
    have hmem : x ∈ W := by
      rcases W.mem_or_inv_mem x with h | h
      · exact h
      · rw [← hback]
        exact pow_mem h (q - 1)
    exact ⟨hmem, hi ▸ pow_mem hmem (q - 1)⟩
  have hrootinj (W : ValuationSubring M) (ℓ : ℕ)
      (hW : W.LiesOverPrime ℓ) (hℓq : ℓ.Coprime q) (x y : W)
      (hx : x ^ q = 1) (hy : y ^ q = 1)
      (hxy : residue W x = residue W y) : x = y := by
    have hℓW : (ℓ : W) ∈ maximalIdeal W :=
      ValuationSubring.coe_mem_nonunits_iff.mp (by
        simpa [ValuationSubring.LiesOverPrime] using hW)
    have hℓk : (ℓ : ResidueField W) = 0 := by
      rw [← map_natCast (residue W) ℓ]
      exact (residue_eq_zero_iff _).mpr hℓW
    have hqk : (q : ResidueField W) ≠ 0 := by
      intro hq0
      obtain ⟨a, b, hab⟩ := hℓq.cast (R := ResidueField W)
      simp only [hℓk, hq0, mul_zero, zero_add, zero_ne_one] at hab
    have hone (t : W) (ht : t ^ q = 1) (hred : residue W t = 1) : t = 1 := by
      by_contra h
      have hs : (∑ i ∈ Finset.range q, t ^ i) = 0 :=
        (mul_eq_zero.mp ((geom_sum_mul t q).trans (by rw [ht, sub_self]))).resolve_right
          (sub_ne_zero.mpr h)
      have hr := congrArg (residue W) hs
      apply hqk
      simpa [map_sum, map_pow, hred] using hr
    let v : W := y ^ (q - 1)
    have hyv : y * v = 1 := by
      dsimp [v]
      rw [← pow_succ', Nat.sub_add_cancel hq.one_le, hy]
    have hvy : v * y = 1 := by rw [mul_comm, hyv]
    have hv : v ^ q = 1 := by
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
  have hrootext (σ τ : J) (heq : σ ζ = τ ζ) : σ = τ := by
    apply AlgEquiv.coe_toAlgHom_injective
    apply (hζ.powerBasis F).algHom_ext
    simpa only [IsPrimitiveRoot.powerBasis_gen, AlgEquiv.coe_toAlgHom] using heq
  have hfrobroot (W : ValuationSubring M) (ℓ : ℕ)
      (hW : W.LiesOverPrime ℓ) (hℓq : ℓ.Coprime q) (σ : J)
      (hσ : W.IsFrobeniusAt σ ℓ) : σ ζ = ζ ^ ℓ := by
    let z : W := ⟨ζ, (hrootmem W ζ hζ.pow_eq_one).1⟩
    let d : W.decompositionSubgroup F := ⟨σ, hσ.mem_decompositionSubgroup⟩
    have hz : z ^ q = 1 := Subtype.ext hζ.pow_eq_one
    have heq : d • z = z ^ ℓ := by
      apply hrootinj W ℓ hW hℓq
      · rw [← smul_pow', hz, smul_one]
      · rw [← pow_mul, Nat.mul_comm, pow_mul, hz, one_pow]
      · rw [IsLocalRing.ResidueField.residue_smul, map_pow]
        exact hσ.smul_residue_eq (residue W z)
    exact congrArg Subtype.val heq
  have hinertia (W : ValuationSubring M) (ℓ : ℕ) (hℓ : ℓ.Prime)
      (hW : W.LiesOverPrime ℓ) (hℓq : ¬ ℓ ∣ q) :
      W.inertiaSubgroupIn F = ⊥ := by
    apply le_antisymm _ bot_le
    rintro σ ⟨d, hd, rfl⟩
    have hred : ∀ x : ResidueField W, d • x = x := by
      have hd' : MulSemiringAction.toRingAut (W.decompositionSubgroup F)
          (ResidueField W) d = 1 := hd
      intro x
      exact congrArg (fun f : RingAut (ResidueField W) => f x) hd'
    apply Subgroup.mem_bot.mpr
    apply hrootext
    let z : W := ⟨ζ, (hrootmem W ζ hζ.pow_eq_one).1⟩
    have hz : z ^ q = 1 := Subtype.ext hζ.pow_eq_one
    have heq : d • z = z := by
      refine hrootinj W ℓ hW (hℓ.coprime_iff_not_dvd.mpr hℓq) _ _ ?_ hz ?_
      · rw [← smul_pow', hz, smul_one]
      · rw [IsLocalRing.ResidueField.residue_smul, hred]
    exact congrArg Subtype.val heq
  -- Steps 20 and 24: cancellation of the common ray-class pole.
  have hrayContinuation (C : Type) [Fintype C] (a : C → ℕ → ℝ)
      (κ α : ℝ) (ha : ∀ c n, 0 ≤ a c n) (hα₀ : 0 ≤ α) (hα₁ : α < 1)
      (hcount : ∀ c, ∃ R : ℝ, 0 ≤ R ∧ ∀ n : ℕ, 1 ≤ n →
        |(∑ k ∈ Finset.Icc 1 n, a c k) - κ * (n : ℝ)| ≤ R * (n : ℝ) ^ α)
      (θ : C → ℂ) (hθ : ∑ c, θ c = 0) :
      ∃ H : ℂ → ℂ, DifferentiableOn ℂ H {s : ℂ | α < s.re} ∧
        ∀ s : ℂ, 1 < s.re →
          (∑ c, θ c * LSeries (fun n : ℕ => (a c n : ℂ)) s) = H s := by
    choose H hH hseries using fun c =>
      Submission.p09_af497904fe_cfs_counting_mellin_continuation
        (a c) κ α (ha c) hα₀ hα₁ (hcount c)
    refine ⟨fun s => ∑ c, θ c * H c s, ?_, ?_⟩
    · exact DifferentiableOn.fun_sum fun c _ => (hH c).const_mul (θ c)
    · intro s hs
      simp_rw [hseries _ s hs, mul_add, Finset.sum_add_distrib]
      rw [← Finset.sum_mul, hθ, zero_mul, zero_add]
  have hprimeBound (E L P : ℝ → ℂ)
      (hE : ContinuousOn E (Set.Ioo 1 2))
      (hL : ContinuousWithinAt L (Set.Ici 1) 1) (hL₁ : L 1 ≠ 0)
      (hexp : ∀ s, s ∈ Set.Ioo 1 2 → Complex.exp (E s) = L s)
      (R : ℝ) (hR : 0 ≤ R)
      (htail : ∀ s : ℝ, 1 < s → s < 2 → ‖P s - E s‖ ≤ R) :
      ∃ C : ℝ, 0 ≤ C ∧ ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧
        ∀ s : ℝ, 1 < s → s < 1 + ε → ‖P s‖ ≤ C := by
    obtain ⟨ε, hε, hε₁, C, hC, hbound⟩ :=
      Submission.p09_af497904fe_cfs_bounded_euler_logarithm E L hE hL hL₁ hexp
    refine ⟨R + C, add_nonneg hR hC, ε, hε, hε₁, ?_⟩
    intro s hs hsε
    calc
      ‖P s‖ = ‖(P s - E s) + E s‖ := by rw [sub_add_cancel]
      _ ≤ ‖P s - E s‖ + ‖E s‖ := norm_add_le _ _
      _ ≤ R + C := add_le_add (htail s hs (by linarith)) (hbound s hs hsε)
  -- Steps 27 and 28: weighted infinitude supplies the requested prime and valuation.
  let ι := IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)
  let N : ι → ℕ := fun v => Ideal.absNorm v.asIdeal
  let D : Set ι := {v | ¬ (N v).Prime ∨ N v ∈ insert q B}
  have hN (v : ι) : 2 ≤ N v := NumberField.HeightOneSpectrum.one_lt_absNorm v
  -- Steps 11 and 20: ideal Euler products and the ordinary Dedekind-zeta series.
  have hIdealSieve (R : Type) [CommRing R] [IsDedekindDomain R]
      (f : Ideal R →*₀ ℂ) (hf : Summable (fun I => ‖f I‖))
      (S : Finset (IsDedekindDomain.HeightOneSpectrum R)) :
      (∏ v ∈ S, (1 - f v.asIdeal)) * (∑' I : Ideal R, f I) =
        ∑' I : Ideal R, if ∀ v ∈ S, ¬ v.asIdeal ∣ I then f I else 0 := by
    classical
    let a : Finset (IsDedekindDomain.HeightOneSpectrum R) → Ideal R → ℂ := fun S I =>
      if ∀ v ∈ S, ¬ v.asIdeal ∣ I then f I else 0
    have ha (S : Finset (IsDedekindDomain.HeightOneSpectrum R)) : Summable (a S) := by
      apply hf.of_norm_bounded
      intro I
      dsimp [a]
      split_ifs <;> simp
    have haway (p v : IsDedekindDomain.HeightOneSpectrum R) (hvp : v ≠ p) (I : Ideal R) :
        v.asIdeal ∣ p.asIdeal * I ↔ v.asIdeal ∣ I := by
      rw [v.prime.dvd_mul]
      apply or_iff_right
      intro h
      apply hvp
      apply IsDedekindDomain.HeightOneSpectrum.asIdeal_injective
      exact (p.isMaximal.eq_of_le v.isPrime.ne_top (Ideal.dvd_iff_le.mp h)).symm
    have hsieve (S : Finset (IsDedekindDomain.HeightOneSpectrum R)) :
        (∏ v ∈ S, (1 - f v.asIdeal)) * (∑' I, f I) = ∑' I, a S I := by
      induction S using Finset.induction_on with
      | empty => simp [a]
      | @insert p S hp ih =>
        have hmul (I : Ideal R) : a S (p.asIdeal * I) = f p.asIdeal * a S I := by
          have hiff : (∀ v ∈ S, ¬ v.asIdeal ∣ p.asIdeal * I) ↔
              (∀ v ∈ S, ¬ v.asIdeal ∣ I) := by
            apply forall_congr'
            intro v
            apply forall_congr'
            intro hv
            rw [haway p v (fun h => hp (h ▸ hv))]
          simp only [a, hiff, map_mul]
          split_ifs <;> simp
        let e : Ideal R ≃ {I : Ideal R // p.asIdeal ∣ I} :=
          Equiv.ofBijective (fun I => ⟨p.asIdeal * I, dvd_mul_right _ _⟩)
            ⟨fun I J h => mul_left_cancel₀ p.ne_bot (congrArg Subtype.val h), by
              rintro ⟨I, J, hJ⟩
              exact ⟨J, Subtype.ext hJ.symm⟩⟩
        have hdiv : (∑' I : {I : Ideal R // p.asIdeal ∣ I}, a S I.1) =
            f p.asIdeal * ∑' I, a S I := by
          rw [← e.tsum_eq]
          change (∑' I, a S (p.asIdeal * I)) = _
          simp_rw [hmul]
          exact tsum_mul_left
        have hrest : (∑' I : {I : Ideal R // ¬ p.asIdeal ∣ I}, a S I.1) =
            ∑' I, a (insert p S) I := by
          have hsub := tsum_subtype {I : Ideal R | ¬ p.asIdeal ∣ I} (a S)
          simp only [Set.coe_eq_subtype, Set.mem_ofPred_eq] at hsub
          rw [hsub]
          apply tsum_congr
          intro I
          by_cases hpI : p.asIdeal ∣ I <;> simp [Set.indicator, a, hpI]
        have hsplit := (ha S).tsum_subtype_add_tsum_subtype_compl
          {I : Ideal R | p.asIdeal ∣ I}
        change (∑' I : {I : Ideal R // p.asIdeal ∣ I}, a S I.1) +
          (∑' I : {I : Ideal R // ¬ p.asIdeal ∣ I}, a S I.1) = _ at hsplit
        rw [hdiv, hrest] at hsplit
        rw [Finset.prod_insert hp, mul_assoc, ih]
        linear_combination - hsplit
    exact hsieve S
  have hEulerIdeal (R : Type) [CommRing R] [IsDedekindDomain R]
      (f : Ideal R →*₀ ℂ) (hf : Summable (fun I => ‖f I‖))
      (hsmall : ∀ v : IsDedekindDomain.HeightOneSpectrum R, 1 - f v.asIdeal ≠ 0) :
      Complex.exp (∑' v : IsDedekindDomain.HeightOneSpectrum R, -Complex.log (1 - f v.asIdeal)) =
        ∑' I : Ideal R, f I := by
    classical
    let a : Finset (IsDedekindDomain.HeightOneSpectrum R) → Ideal R → ℂ := fun S I =>
      if ∀ v ∈ S, ¬ v.asIdeal ∣ I then f I else 0
    have ha (S : Finset (IsDedekindDomain.HeightOneSpectrum R)) : Summable (a S) := by
      apply hf.of_norm_bounded
      intro I
      dsimp [a]
      split_ifs <;> simp
    have hsieve (S : Finset (IsDedekindDomain.HeightOneSpectrum R)) :
        (∏ v ∈ S, (1 - f v.asIdeal)) * (∑' I, f I) = ∑' I, a S I :=
      hIdealSieve R f hf S
    have hpoint (I : Ideal R) :
        Tendsto (fun S : Finset (IsDedekindDomain.HeightOneSpectrum R) => a S I) atTop
          (𝓝 (if I = 1 then (1 : ℂ) else 0)) := by
      by_cases hIone : I = 1
      · subst I
        have hno (v : IsDedekindDomain.HeightOneSpectrum R) : ¬ v.asIdeal ∣ (1 : Ideal R) :=
          fun h => v.irreducible.not_isUnit (isUnit_of_dvd_one h)
        simpa only [a, hno, not_false_eq_true, implies_true, if_true, map_one] using
          (tendsto_const_nhds : Tendsto (fun _ : Finset (IsDedekindDomain.HeightOneSpectrum R) => (1 : ℂ))
            atTop (𝓝 1))
      by_cases hIzero : I = 0
      · simp only [hIone, if_false]
        simpa only [a, hIzero, map_zero, ite_self] using
          (tendsto_const_nhds : Tendsto (fun _ : Finset (IsDedekindDomain.HeightOneSpectrum R) => (0 : ℂ))
            atTop (𝓝 0))
      obtain ⟨P, hP, hPI⟩ := WfDvdMonoid.exists_irreducible_factor
        (fun h => hIone (by simpa only [Ideal.one_eq_top] using Ideal.isUnit_iff.mp h)) hIzero
      let v : IsDedekindDomain.HeightOneSpectrum R := IsDedekindDomain.HeightOneSpectrum.ofPrime hP.prime
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop ({v} : Finset (IsDedekindDomain.HeightOneSpectrum R))] with S hS
      have hv : v ∈ S := hS (Finset.mem_singleton_self v)
      have hnot : ¬ (∀ w ∈ S, ¬ w.asIdeal ∣ I) := fun h => h v hv hPI
      simp only [a, if_neg hnot, if_neg hIone]
    have hlimit : Tendsto (fun S : Finset (IsDedekindDomain.HeightOneSpectrum R) => ∑' I, a S I)
        atTop (𝓝 (1 : ℂ)) := by
      convert tendsto_tsum_of_dominated_convergence hf hpoint
        (Filter.Eventually.of_forall (fun S I => ?_)) using 1
      · simp
      · dsimp [a]
        split_ifs <;> simp
    have hlogs : Summable (fun v : IsDedekindDomain.HeightOneSpectrum R => Complex.log (1 - f v.asIdeal)) :=
      (hf.of_norm.comp_injective IsDedekindDomain.HeightOneSpectrum.asIdeal_injective).clog_one_sub
    have hprod : HasProd (fun v : IsDedekindDomain.HeightOneSpectrum R => 1 - f v.asIdeal)
        (Complex.exp (∑' v : IsDedekindDomain.HeightOneSpectrum R, Complex.log (1 - f v.asIdeal))) := by
      simpa only [Function.comp_def, Complex.exp_log (hsmall _)] using hlogs.hasSum.cexp
    have hid : Complex.exp (∑' v : IsDedekindDomain.HeightOneSpectrum R, Complex.log (1 - f v.asIdeal)) *
        (∑' I, f I) = 1 := by
      apply tendsto_nhds_unique (hprod.mul_const (∑' I, f I))
      exact hlimit.congr (fun S => (hsieve S).symm)
    rw [tsum_neg, Complex.exp_neg]
    exact inv_eq_of_mul_eq_one_right hid
  have hIdealSeries (s : ℝ) (hs : 1 < s) :
      Summable (fun I : Ideal (NumberField.RingOfIntegers F) =>
        Real.rpow (absNorm I : ℝ) (-s)) ∧
      NumberField.dedekindZeta F (s : ℂ) = ∑' I : Ideal (NumberField.RingOfIntegers F),
        (Real.rpow (absNorm I : ℝ) (-s) : ℂ) := by
    classical
    let a : ℕ → ℝ := fun n => Nat.card {I : Ideal (NumberField.RingOfIntegers F) // absNorm I = n}
    have hlim : Tendsto (fun n : ℕ => (∑ k ∈ Finset.Icc 1 n, a k) / (n : ℝ))
        atTop (𝓝 (NumberField.dedekindZeta_residue F)) := by
      refine ((NumberField.Ideal.tendsto_norm_le_div_atTop₀ F).comp
        tendsto_natCast_atTop_atTop).congr fun n => ?_
      dsimp [a]
      simp only [Nat.cast_le, ← Nat.cast_sum]
      congr
      rw [← add_left_inj 1, ← card_norm_le_eq_card_norm_le_add_one,
        show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
        show 1 = Nat.card {I : Ideal (NumberField.RingOfIntegers F) // absNorm I = 0} by
          simp [Ideal.absNorm_eq_zero_iff],
        Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),
        ← Finset.card_preimage_eq_sum_card_image_eq (fun k _ => finite_setOfPred_absNorm_eq k)]
      simp [Set.coe_eq_subtype]
    have hls : LSeriesSummable (fun n => (a n : ℂ)) (s : ℂ) := by
      apply LSeriesSummable_of_sum_norm_bigO_and_nonneg
        (r := 1) _ (fun n => Nat.cast_nonneg _) zero_le_one hs
      exact isBigO_atTop_natCast_rpow_of_tendsto_div_rpow (by simpa using hlim)
    have hnorm : Summable (fun n : ℕ => a n * Real.rpow (n : ℝ) (-s)) := by
      refine hls.norm.congr fun n => ?_
      rw [LSeries.norm_term_eq]
      by_cases hn : n = 0
      · subst n
        simp [ne_of_lt (neg_lt_zero.mpr (lt_trans zero_lt_one hs))]
      · simp [hn, Complex.norm_real, abs_of_nonneg (show 0 ≤ a n from Nat.cast_nonneg _),
          Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]
    have hideals : Summable (fun I : Ideal (NumberField.RingOfIntegers F) =>
        Real.rpow (absNorm I : ℝ) (-s)) := by
      refine (summable_partition (fun I => Real.rpow_nonneg (Nat.cast_nonneg _) _)
        (s := fun n => {I : Ideal (NumberField.RingOfIntegers F) | absNorm I = n})
        (fun I => ⟨absNorm I, rfl, fun n hn => hn.symm⟩)).mpr ⟨?_, ?_⟩
      · intro n
        change Summable (fun I : {I : Ideal (NumberField.RingOfIntegers F) // absNorm I = n} =>
          Real.rpow (absNorm I.1 : ℝ) (-s))
        let : Fintype {I : Ideal (NumberField.RingOfIntegers F) // absNorm I = n} :=
          (finite_setOfPred_absNorm_eq n).fintype
        exact Summable.of_finite
      · apply hnorm.congr
        intro n
        change a n * Real.rpow (n : ℝ) (-s) =
          ∑' I : {I : Ideal (NumberField.RingOfIntegers F) // absNorm I = n},
            Real.rpow (absNorm I.1 : ℝ) (-s)
        let : Fintype {I : Ideal (NumberField.RingOfIntegers F) // absNorm I = n} :=
          (finite_setOfPred_absNorm_eq n).fintype
        have heq : (fun I : {I : Ideal (NumberField.RingOfIntegers F) // absNorm I = n} =>
            Real.rpow (absNorm I.1 : ℝ) (-s)) = fun _ => Real.rpow (n : ℝ) (-s) :=
          funext fun I => by rw [I.property]
        rw [heq, tsum_fintype]
        simp [a, Nat.card_eq_fintype_card]
    refine ⟨hideals, ?_⟩
    have hgroup : (∑' n : ℕ, a n * Real.rpow (n : ℝ) (-s)) =
        ∑' I : Ideal (NumberField.RingOfIntegers F), Real.rpow (absNorm I : ℝ) (-s) := by
      have h := (hideals.hasSum.tsum_fiberwise
        (fun I : Ideal (NumberField.RingOfIntegers F) => absNorm I)).tsum_eq
      rw [← h]
      apply tsum_congr
      intro n
      change a n * Real.rpow (n : ℝ) (-s) =
        ∑' I : {I : Ideal (NumberField.RingOfIntegers F) // absNorm I = n},
          Real.rpow (absNorm I.1 : ℝ) (-s)
      let : Fintype {I : Ideal (NumberField.RingOfIntegers F) // absNorm I = n} :=
        (finite_setOfPred_absNorm_eq n).fintype
      have heq : (fun I : {I : Ideal (NumberField.RingOfIntegers F) // absNorm I = n} =>
          Real.rpow (absNorm I.1 : ℝ) (-s)) = fun _ => Real.rpow (n : ℝ) (-s) :=
        funext fun I => by rw [I.property]
      rw [heq, tsum_fintype]
      simp [a, Nat.card_eq_fintype_card]
    change (∑' n, LSeries.term (fun n => (a n : ℂ)) (s : ℂ) n) = _
    rw [← Complex.ofReal_tsum, ← hgroup, Complex.ofReal_tsum]
    apply tsum_congr
    intro n
    rw [LSeries.term_of_ne_zero' (Complex.ofReal_ne_zero.mpr (by linarith))]
    rw [Complex.ofReal_mul, Real.rpow_eq_pow, Complex.ofReal_cpow (Nat.cast_nonneg n),
      Complex.ofReal_neg, Complex.ofReal_natCast, Complex.cpow_neg, div_eq_mul_inv]
    norm_cast
  have hsum : ∀ s : ℝ, 1 < s →
      Summable (fun v : ι => Real.rpow (N v : ℝ) (-s)) := by
    intro s hs
    exact (hIdealSeries s hs).1.comp_injective
      IsDedekindDomain.HeightOneSpectrum.asIdeal_injective
  -- Step 26: uniformly control the Euler logarithm beyond its linear terms.
  have hEulerTail (χ : ι → ℂ) (hχ : ∀ v, ‖χ v‖ = 1) :
      ∃ R : ℝ, 0 ≤ R ∧ ∀ s : ℝ, 1 < s →
        ‖(∑' v, χ v * Complex.ofReal (Real.rpow (N v : ℝ) (-s))) -
          (∑' v, -Complex.log (1 - χ v *
            Complex.ofReal (Real.rpow (N v : ℝ) (-s))))‖ ≤ R := by
    let R := ∑' v, Real.rpow (N v : ℝ) (-2)
    refine ⟨R, tsum_nonneg (fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _), ?_⟩
    intro s hs
    let a : ι → ℝ := fun v => Real.rpow (N v : ℝ) (-s)
    let u : ι → ℂ := fun v => χ v * Complex.ofReal (a v)
    have ha0 (v : ι) : 0 ≤ a v := Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hnorm (v : ι) : ‖u v‖ = a v := by
      simp only [u, norm_mul, hχ, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (ha0 v), one_mul]
    have hN1 (v : ι) : 1 ≤ (N v : ℝ) := by exact_mod_cast (hN v).trans' (by omega)
    have ha (v : ι) : a v ≤ 1 / 2 := by
      calc
        a v ≤ Real.rpow (N v : ℝ) (-1) :=
          Real.rpow_le_rpow_of_exponent_le (hN1 v) (by linarith)
        _ = (N v : ℝ)⁻¹ := Real.rpow_neg_one _
        _ ≤ 1 / 2 := by
          rw [one_div]
          exact inv_anti₀ (by norm_num) (by exact_mod_cast hN v)
    have hu : Summable u := by
      apply Summable.of_norm
      simpa only [hnorm] using hsum s hs
    have hlog : Summable (fun v => -Complex.log (1 - u v)) := hu.clog_one_sub.neg
    have htail (v : ι) : ‖u v - -Complex.log (1 - u v)‖ ≤
        Real.rpow (N v : ℝ) (-2) := by
      have hhalf := ha v
      have hsmall : ‖-u v‖ < 1 := by rw [norm_neg, hnorm]; linarith
      have hb := Complex.norm_log_one_add_sub_self_le hsmall
      have hden : (1 - a v)⁻¹ ≤ 2 := by
        have : (1 / 2 : ℝ) ≤ 1 - a v := by linarith
        have hh := inv_anti₀ (by norm_num : (0 : ℝ) < 1 / 2) this
        norm_num at hh
        exact hh
      calc
        ‖u v - -Complex.log (1 - u v)‖ = ‖Complex.log (1 + -u v) - -u v‖ := by
          simp only [sub_eq_add_neg, neg_neg, add_comm]
        _ ≤ ‖-u v‖ ^ 2 * (1 - ‖-u v‖)⁻¹ / 2 := hb
        _ ≤ a v ^ 2 := by
          rw [norm_neg, hnorm]
          nlinarith [mul_le_mul_of_nonneg_left hden (sq_nonneg (a v))]
        _ = Real.rpow (N v : ℝ) (-s * 2) := by
          simp only [a, Real.rpow_eq_pow]
          rw [Real.rpow_mul (Nat.cast_nonneg _), Real.rpow_two]
        _ ≤ Real.rpow (N v : ℝ) (-2) :=
          Real.rpow_le_rpow_of_exponent_le (hN1 v) (by linarith)
    change ‖(∑' v, u v) - ∑' v, -Complex.log (1 - u v)‖ ≤ R
    rw [← hu.tsum_sub hlog]
    exact (norm_tsum_le_tsum_norm (hu.sub hlog).norm).trans
      ((hu.sub hlog).norm.tsum_le_tsum htail (hsum 2 (by norm_num)))
  have hEulerContinuous (χ : ι → ℂ) (hχ : ∀ v, ‖χ v‖ = 1) :
      ContinuousOn (fun s : ℝ => ∑' v,
        -Complex.log (1 - χ v * Complex.ofReal (Real.rpow (N v : ℝ) (-s))))
          (Set.Ioi 1) := by
    let a : ι → ℝ → ℝ := fun v s => Real.rpow (N v : ℝ) (-s)
    let u : ι → ℝ → ℂ := fun v s => χ v * Complex.ofReal (a v s)
    have ha0 (v : ι) (s : ℝ) : 0 ≤ a v s := Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hnorm (v : ι) (s : ℝ) : ‖u v s‖ = a v s := by
      simp only [u, norm_mul, hχ, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (ha0 v s), one_mul]
    have hN1 (v : ι) : 1 ≤ (N v : ℝ) := by
      exact_mod_cast (hN v).trans' (show 1 ≤ 2 by omega)
    have ha (v : ι) (s : ℝ) (hs : 1 < s) : a v s ≤ 1 / 2 := by
      calc
        a v s ≤ Real.rpow (N v : ℝ) (-1) :=
          Real.rpow_le_rpow_of_exponent_le (hN1 v) (by linarith)
        _ = (N v : ℝ)⁻¹ := Real.rpow_neg_one _
        _ ≤ 1 / 2 := by
          rw [one_div]
          exact inv_anti₀ (by norm_num) (by exact_mod_cast hN v)
    have hu (v : ι) : Continuous (u v) := by
      have hn0 : (N v : ℝ) ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (hN1 v))
      exact continuous_const.mul
        (Complex.continuous_ofReal.comp ((Real.continuous_const_rpow hn0).comp continuous_neg))
    have hlog (v : ι) : ContinuousOn (fun s => -Complex.log (1 - u v s)) (Set.Ioi 1) := by
      apply ContinuousOn.neg
      apply (continuous_const.sub (hu v)).continuousOn.clog
      intro s hs
      apply Complex.mem_slitPlane_iff.mpr
      left
      have hre := Complex.re_le_norm (u v s)
      rw [hnorm] at hre
      have hhalf := ha v s hs
      change 0 < 1 - (u v s).re
      linarith
    have hcont (b : ℝ) (hb : 1 < b) :
        ContinuousOn (fun s => ∑' v, -Complex.log (1 - u v s)) (Set.Ioi b) := by
      apply continuousOn_tsum (fun v => (hlog v).mono (Set.Ioi_subset_Ioi hb.le))
        ((hsum b hb).mul_left (3 / 2))
      intro v s hs
      have hbs : b < s := hs
      rw [norm_neg]
      have hhalf : ‖-u v s‖ ≤ 1 / 2 := by
        rw [norm_neg, hnorm]
        exact ha v s (lt_trans hb hs)
      calc
        ‖Complex.log (1 - u v s)‖ = ‖Complex.log (1 + -u v s)‖ := by rw [sub_eq_add_neg]
        _ ≤ (3 / 2) * ‖-u v s‖ := Complex.norm_log_one_add_half_le_self hhalf
        _ = (3 / 2) * a v s := by rw [norm_neg, hnorm]
        _ ≤ (3 / 2) * a v b := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact Real.rpow_le_rpow_of_exponent_le (hN1 v) (by linarith)
    intro s hs
    change 1 < s at hs
    have hb : 1 < (s + 1) / 2 := by linarith [hs]
    have hbs : (s + 1) / 2 < s := by linarith [hs]
    exact ((hcont _ hb).continuousAt (isOpen_Ioi.mem_nhds hbs)).continuousWithinAt
  -- Step 27: higher rational residue degrees have a summable p⁻² majorant.
  have hhigher : ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, 1 < s → s < 2 →
      (∑' v : {v : ι // ¬ (N v).Prime}, Real.rpow (N v.1 : ℝ) (-s)) ≤ C := by
    classical
    let O := NumberField.RingOfIntegers F
    let ι := IsDedekindDomain.HeightOneSpectrum O
    let d := Module.finrank ℤ O
    have hcard (p : ℕ) (hp : p.Prime) :
        Nat.card ((Ideal.span {(p : ℤ)}).primesOver O) ≤ d := by
      let : Fact p.Prime := ⟨hp⟩
      let P : Ideal ℤ := Ideal.span {(p : ℤ)}
      have : P.IsMaximal := Int.ideal_span_isMaximal_of_prime p
      let : Fintype (P.primesOver O) := inferInstance
      change Nat.card (P.primesOver O) ≤ d
      rw [Nat.card_eq_fintype_card]
      calc
        Fintype.card (P.primesOver O) = ∑ _ : P.primesOver O, 1 := by simp
        _ ≤ ∑ Q : P.primesOver O, Q.1.ramificationIdx ℤ * Q.1.inertiaDeg ℤ := by
          apply Finset.sum_le_sum
          intro Q _
          exact Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt
            (Nat.mul_pos (Q.1.ramificationIdx_pos ℤ) (Q.1.inertiaDeg_pos ℤ)))
        _ = d := Ideal.sum_ramification_inertia_eq_finrank P O
    have hdata (v : ι) : ∃ p : ℕ, p.Prime ∧
        v.asIdeal ∈ (Ideal.span {(p : ℤ)}).primesOver O ∧
        (¬ (Ideal.absNorm v.asIdeal).Prime → p ^ 2 ≤ Ideal.absNorm v.asIdeal) := by
      obtain ⟨p, n, hn, hpv, hp, hnorm⟩ := Ideal.exists_prime_and_absNorm_eq_pow v.asIdeal
      let : Fact p.Prime := ⟨hp⟩
      let P : Ideal ℤ := Ideal.span {(p : ℤ)}
      have hP : P.IsMaximal := Int.ideal_span_isMaximal_of_prime p
      have hle : P ≤ v.asIdeal.under ℤ := by
        rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_under]
        simpa using hpv
      have hPv : P = v.asIdeal.under ℤ := hP.eq_of_le Ideal.IsPrime.ne_top' hle
      refine ⟨p, hp, ⟨v.isPrime, ⟨hPv⟩⟩, ?_⟩
      intro hnp
      have hn1 : n ≠ 1 := by
        intro h
        apply hnp
        simpa [hnorm, h] using hp
      rw [hnorm]
      exact Nat.pow_le_pow_right hp.pos (by omega)
    let A := {v : ι // ¬ (Ideal.absNorm v.asIdeal).Prime}
    choose p hp hov hsize using hdata
    let κ := Σ r : Nat.Primes, (Ideal.span {((r : ℕ) : ℤ)}).primesOver O
    let f : A → κ := fun v => ⟨⟨p v.1, hp v.1⟩, ⟨v.1.asIdeal, hov v.1⟩⟩
    have hf : Function.Injective f := by
      intro v w heq
      apply Subtype.ext
      apply IsDedekindDomain.HeightOneSpectrum.asIdeal_injective
      exact congrArg (fun z : κ => z.2.1) heq
    let w : κ → ℝ := fun z => Real.rpow ((z.1 : ℕ) : ℝ) (-2)
    have hmajor : Summable w := by
      refine (summable_sigma_of_nonneg (fun z : κ =>
        Real.rpow_nonneg (Nat.cast_nonneg _) _)).mpr ⟨?_, ?_⟩
      · intro r
        let : Fact (r : ℕ).Prime := ⟨r.property⟩
        have : (Ideal.span {((r : ℕ) : ℤ)}).IsMaximal :=
          Int.ideal_span_isMaximal_of_prime (r : ℕ)
        exact Summable.of_finite
      · have hpseries : Summable (fun r : Nat.Primes => Real.rpow ((r : ℕ) : ℝ) (-2)) :=
          (Real.summable_nat_rpow.mpr (by norm_num : (-2 : ℝ) < -1)).subtype _
        refine Summable.of_nonneg_of_le
          (fun r => tsum_nonneg (fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _))
          (fun r => ?_) (hpseries.mul_left (d : ℝ))
        let : Fact (r : ℕ).Prime := ⟨r.property⟩
        have : (Ideal.span {((r : ℕ) : ℤ)}).IsMaximal :=
          Int.ideal_span_isMaximal_of_prime (r : ℕ)
        let : Fintype ((Ideal.span {((r : ℕ) : ℤ)}).primesOver O) := inferInstance
        change (∑' _ : (Ideal.span {((r : ℕ) : ℤ)}).primesOver O,
          Real.rpow ((r : ℕ) : ℝ) (-2)) ≤ (d : ℝ) * Real.rpow ((r : ℕ) : ℝ) (-2)
        rw [tsum_fintype]
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        exact_mod_cast (show Fintype.card ((Ideal.span {((r : ℕ) : ℤ)}).primesOver O) ≤ d by
          simpa only [Nat.card_eq_fintype_card] using hcard (r : ℕ) r.property)
    have hweight (s : ℝ) (hs : 1 < s) (v : A) :
        Real.rpow (Ideal.absNorm v.1.asIdeal : ℝ) (-s) ≤ w (f v) := by
      have hnorm := hsize v.1 v.2
      have hnorm₁ : 1 ≤ (Ideal.absNorm v.1.asIdeal : ℝ) := by
        exact_mod_cast (Nat.one_le_of_lt ((pow_pos (hp v.1).pos 2).trans_le hnorm))
      change Real.rpow (Ideal.absNorm v.1.asIdeal : ℝ) (-s) ≤
        Real.rpow (p v.1 : ℝ) (-2)
      calc
        Real.rpow (Ideal.absNorm v.1.asIdeal : ℝ) (-s) ≤
            Real.rpow (Ideal.absNorm v.1.asIdeal : ℝ) (-1) :=
          Real.rpow_le_rpow_of_exponent_le hnorm₁ (by linarith)
        _ ≤ Real.rpow ((p v.1 : ℝ) ^ 2) (-1) := by
          apply Real.rpow_le_rpow_of_nonpos
          · exact pow_pos (Nat.cast_pos.mpr (hp v.1).pos) _
          · exact_mod_cast hnorm
          · norm_num
        _ = Real.rpow (p v.1 : ℝ) (-2) := by
          simp only [Real.rpow_eq_pow]
          rw [Real.rpow_neg_one, Real.rpow_neg (Nat.cast_nonneg _), Real.rpow_two]
    have hcomp : Summable (fun v : A => w (f v)) := hmajor.comp_injective hf
    refine ⟨∑' v : A, w (f v), tsum_nonneg (fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _), ?_⟩
    intro s hs _
    exact (Summable.of_nonneg_of_le
      (fun v : A => Real.rpow_nonneg (Nat.cast_nonneg _) _) (hweight s hs) hcomp).tsum_le_tsum
        (hweight s hs) hcomp
  have hfiniteNorm (n : ℕ) : {v : ι | N v = n}.Finite :=
    Set.Finite.preimage IsDedekindDomain.HeightOneSpectrum.asIdeal_injective.injOn
      (Ideal.finite_setOfPred_absNorm_eq n)
  have hfiniteExcluded : {v : ι | N v ∈ insert q B}.Finite := by
    have hfinite := (insert q B).finite_toSet.biUnion (fun n _ => hfiniteNorm n)
    apply hfinite.subset
    intro v hv
    exact Set.mem_iUnion.mpr ⟨N v, Set.mem_iUnion.mpr ⟨hv, rfl⟩⟩
  have hexcludedBound : ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, 1 < s → s < 2 →
      (∑' v : {v : ι // N v ∈ insert q B}, Real.rpow (N v.1 : ℝ) (-s)) ≤ C := by
    let : Fintype {v : ι // N v ∈ insert q B} := hfiniteExcluded.fintype
    refine ⟨Fintype.card {v : ι // N v ∈ insert q B}, Nat.cast_nonneg _, ?_⟩
    intro s hs _
    rw [tsum_fintype]
    calc
      (∑ v : {v : ι // N v ∈ insert q B}, Real.rpow (N v.1 : ℝ) (-s)) ≤
          ∑ _ : {v : ι // N v ∈ insert q B}, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro v _
        apply Real.rpow_le_one_of_one_le_of_nonpos
        · exact_mod_cast (le_trans (by norm_num : 1 ≤ 2) (hN v.1))
        · linarith
      _ = _ := by simp
  have hbadFromHigher
      (hsum : ∀ s : ℝ, 1 < s → Summable (fun v : ι => Real.rpow (N v : ℝ) (-s)))
      (hhigher : ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, 1 < s → s < 2 →
        (∑' v : {v : ι // ¬ (N v).Prime}, Real.rpow (N v.1 : ℝ) (-s)) ≤ C) :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, 1 < s → s < 2 →
        (∑' v : {v : ι // v ∈ D}, Real.rpow (N v.1 : ℝ) (-s)) ≤ C := by
    obtain ⟨C₁, hC₁, hbound₁⟩ := hhigher
    obtain ⟨C₂, hC₂, hbound₂⟩ := hexcludedBound
    refine ⟨C₁ + C₂, add_nonneg hC₁ hC₂, ?_⟩
    intro s hs hs₂
    let f : ι → ℝ := fun v => Real.rpow (N v : ℝ) (-s)
    let U : Set ι := {v | ¬ (N v).Prime}
    let V : Set ι := {v | N v ∈ insert q B}
    have hf : Summable f := hsum s hs
    have hle : D.indicator f ≤ U.indicator f + V.indicator f := by
      intro v
      have hfv : 0 ≤ f v := Real.rpow_nonneg (Nat.cast_nonneg _) _
      by_cases hU : v ∈ U <;> by_cases hV : v ∈ V <;>
        simp_all [Set.indicator, D, U, V]
    calc
      (∑' v : {v : ι // v ∈ D}, f v.1) = ∑' v, D.indicator f v := tsum_subtype D f
      _ ≤ ∑' v, (U.indicator f + V.indicator f) v :=
        (hf.indicator D).tsum_le_tsum hle ((hf.indicator U).add (hf.indicator V))
      _ = (∑' v : U, f v.1) + ∑' v : V, f v.1 := by
        simp only [Pi.add_apply]
        rw [Summable.tsum_add (hf.indicator U) (hf.indicator V),
          ← tsum_subtype U f, ← tsum_subtype V f]
      _ ≤ C₁ + C₂ := add_le_add (hbound₁ s hs hs₂) (hbound₂ s hs hs₂)
  -- Steps 9 and 28: lift arithmetic Frobenius and extend its residue action to fractions.
  have hprimeRealize (v : ι) : ∃ g : J, ∃ W : ValuationSubring M,
      W.LiesOverPrime (N v) ∧ W.IsFrobeniusAt g (N v) := by
    let O := NumberField.RingOfIntegers M
    let R := NumberField.RingOfIntegers F
    let Qp : v.asIdeal.primesOver O := Classical.choice inferInstance
    let Q : Ideal O := Qp.1
    have hQ : Q.IsPrime := Qp.2.1
    have hQv : Q.LiesOver v.asIdeal := Qp.2.2
    have hQ0 : Q ≠ ⊥ := Ideal.ne_bot_of_mem_primesOver v.ne_bot Qp.2
    let : Finite (O ⧸ Q) := Q.finiteQuotientOfFreeOfNeBot hQ0
    obtain ⟨g, hg⟩ := IsArithFrobAt.exists_of_isInvariant R J Q
    let n := Ideal.absNorm v.asIdeal
    have hn : 0 < n := lt_trans Nat.zero_lt_one
      (NumberField.HeightOneSpectrum.one_lt_absNorm v)
    have hnorm : Nat.card (R ⧸ Q.under R) = n := by
      rw [← Ideal.over_def Q v.asIdeal]
      rfl
    let γ := NumberField.RingOfIntegers.mapRingEquiv g.toRingEquiv
    have hcong (a : O) : γ a - a ^ n ∈ Q := by
      have ha := hg a
      change g • a - a ^ Nat.card (R ⧸ Q.under R) ∈ Q at ha
      have haction : γ a = g • a := by
        apply NumberField.RingOfIntegers.ext
        rfl
      simpa only [hnorm, ← haction] using ha
    have hnQ : (n : O) ∈ Q := by
      have hnR : (n : R) ∈ v.asIdeal := v.asIdeal.absNorm_mem
      simpa only [map_natCast] using
        (Ideal.mem_of_liesOver Q v.asIdeal (n : R)).mp hnR
    let w : IsDedekindDomain.HeightOneSpectrum O := ⟨Q, hQ, hQ0⟩
    let W := w.valuationSubringAtPrime M
    let : Algebra O W :=
      (Localization.subalgebra.ofField M Q.primeCompl Q.primeCompl_le_nonZeroDivisors).algebra'
    let : IsLocalization Q.primeCompl W :=
      Localization.subalgebra.isLocalization_ofField M Q.primeCompl
        Q.primeCompl_le_nonZeroDivisors
    have hloc (x : M) : x ∈ W ↔ ∃ a b : O, b ∉ Q ∧ x = (a : M) / (b : M) := by
      change (∃ a b, ∃ _ : b ∈ Q.primeCompl,
        x = algebraMap O M a * (algebraMap O M b)⁻¹) ↔ _
      simp only [Ideal.mem_primeCompl_iff, exists_prop, div_eq_mul_inv]
      rfl
    have hcenter (a : O) : algebraMap O W a ∈ maximalIdeal W ↔ a ∈ Q :=
      IsLocalization.AtPrime.to_map_mem_maximal_iff W Q a
    have hW : W.LiesOverPrime n := by
      change (n : M) ∈ W.nonunits
      have h := (hcenter n).mpr hnQ
      have h' := W.coe_mem_nonunits_iff.mpr h
      change algebraMap O M (n : O) ∈ W.nonunits at h'
      exact (map_natCast (algebraMap O M) n) ▸ h'
    have hγ (a : O) : γ a ∈ Q ↔ a ∈ Q := by
      constructor
      · intro ha
        apply hQ.mem_of_pow_mem n
        simpa only [sub_sub_cancel] using Q.sub_mem ha (hcong a)
      · intro ha
        simpa only [sub_add_cancel] using Q.add_mem (hcong a) (Q.pow_mem_of_mem ha n hn)
    have hγinv (a : O) : γ.symm a ∈ Q ↔ a ∈ Q := by
      simpa only [RingEquiv.apply_symm_apply] using (hγ (γ.symm a)).symm
    have hforward (x : M) (hx : x ∈ W) : g x ∈ W := by
      obtain ⟨a, b, hb, rfl⟩ := (hloc x).mp hx
      apply (hloc _).mpr
      refine ⟨γ a, γ b, fun h => hb ((hγ b).mp h), ?_⟩
      exact map_div₀ g _ _
    have hbackward (x : M) (hx : x ∈ W) : g.symm x ∈ W := by
      obtain ⟨a, b, hb, rfl⟩ := (hloc x).mp hx
      apply (hloc _).mpr
      refine ⟨γ.symm a, γ.symm b, fun h => hb ((hγinv b).mp h), ?_⟩
      exact map_div₀ g.symm _ _
    have hgW : g ∈ W.decompositionSubgroup F := by
      let := ValuationSubring.pointwiseMulAction (G := J) (K := M)
      rw [MulAction.mem_stabilizer_iff]
      ext x
      rw [ValuationSubring.mem_smul_pointwise_iff_exists]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hforward y hy
      · intro hx
        exact ⟨g.symm x, hbackward x hx, g.apply_symm_apply x⟩
    let i : O →+* W := algebraMap O W
    let κ : O →+* ResidueField W := (residue W).comp i
    have hker (a : O) : κ a = 0 ↔ a ∈ Q := by
      change residue W (i a) = 0 ↔ a ∈ Q
      rw [residue_eq_zero_iff]
      exact hcenter a
    have hκ (a : O) : κ (γ a) = κ a ^ n := by
      have h := (hker (γ a - a ^ n)).mpr (hcong a)
      rw [map_sub, map_pow, sub_eq_zero] at h
      exact h
    have hfrac (z : W) (a b : O) (hb : b ∉ Q)
        (hz : (z : M) = (a : M) / (b : M)) : residue W z = κ a / κ b := by
      have hbM : (b : M) ≠ 0 := by
        intro hb0
        apply hb
        have : b = 0 := NumberField.RingOfIntegers.ext hb0
        simpa only [this] using Q.zero_mem
      have hmul : z * i b = i a := by
        apply Subtype.ext
        change (z : M) * (b : M) = (a : M)
        exact (eq_div_iff hbM).mp hz
      apply (eq_div_iff (fun h => hb ((hker b).mp h))).mpr
      exact (map_mul (residue W) z (i b)).symm.trans (congrArg (residue W) hmul)
    refine ⟨g, W, hW, hgW, ?_⟩
    intro z
    obtain ⟨x, rfl⟩ := residue_surjective (R := W) z
    obtain ⟨a, b, hb, hx⟩ := (hloc (x : M)).mp x.property
    rw [← IsLocalRing.ResidueField.residue_smul]
    have hgx : (((⟨g, hgW⟩ : W.decompositionSubgroup F) • x : W) : M) =
        (γ a : M) / (γ b : M) := by
      change g (x : M) = g (a : M) / g (b : M)
      rw [hx, map_div₀]
    rw [hfrac _ (γ a) (γ b) (fun h => hb ((hγ b).mp h)) hgx,
      hfrac x a b hb hx, hκ a, hκ b, div_pow]
  have hfinish
      (frob : ι → J)
      (hsum : ∀ s : ℝ, 1 < s → Summable (fun v : ι => Real.rpow (N v : ℝ) (-s)))
      (hcharacters : ∀ k : Fin m, ∃ C : ℝ, 0 ≤ C ∧ ∃ ε : ℝ, 0 < ε ∧
        ∀ s : ℝ, 1 < s → s < 1 + ε →
          ‖(∑' v : ι, ω ^ (k.val * (code (frob v)).val) *
            Complex.ofReal (Real.rpow (N v : ℝ) (-s))) -
              (if k.val = 0 then (Real.log (1 / (s - 1)) : ℂ) else 0)‖ ≤ C)
      (hbad : ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, 1 < s → s < 2 →
        (∑' v : {v : ι // v ∈ D}, Real.rpow (N v.1 : ℝ) (-s)) ≤ C)
      (hrealize : ∀ v : ι, v ∉ D → ∃ W : ValuationSubring M,
        W.LiesOverPrime (N v) ∧ W.IsFrobeniusAt (frob v) (N v)) :
      ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ∉ B ∧ ∃ W : ValuationSubring M,
        W.LiesOverPrime ℓ ∧ W.IsFrobeniusAt h ℓ := by
    obtain ⟨v, hv⟩ := (Submission.p09_af497904fe_cfs_cyclic_weighted_infinitude
      ι m ω N (fun v => code (frob v)) D hm hω hN hsum hcharacters hbad (code h)).nonempty
    have hvD : ¬ (¬ (N v).Prime ∨ N v ∈ insert q B) := hv.1
    have hvprime : (N v).Prime := not_not.mp (not_or.mp hvD).1
    have hvB : N v ∉ B := fun hvB => (not_or.mp hvD).2 (Finset.mem_insert_of_mem hvB)
    obtain ⟨W, hW, hFrob⟩ := hrealize v hv.1
    have hvh : frob v = h := hcode hv.2
    exact ⟨N v, hvprime, hvB, W, hW, hvh ▸ hFrob⟩
  choose frob val hval hfrob using hprimeRealize
  have hnormAction (v : ι) (hv : (N v).Coprime q) : frob v ζ = ζ ^ N v :=
    hfrobroot (val v) (N v) (hval v) hv (frob v) (hfrob v)
  -- Step 22: extend the actual prime Frobenius assignment multiplicatively.
  let O := NumberField.RingOfIntegers F
  let : CommGroup J := IsCyclic.commGroup
  let primeAction : Ideal O → J := fun P =>
    if hp : P.IsPrime ∧ P ≠ ⊥ then frob ⟨P, hp.1, hp.2⟩ else 1
  let A : (Ideal O)⁰ →* J :=
    { toFun := fun I => ((normalizedFactors (I : Ideal O)).map primeAction).prod
      map_one' := by
        change ((normalizedFactors (1 : Ideal O)).map primeAction).prod = 1
        rw [normalizedFactors_one, Multiset.map_zero, Multiset.prod_zero]
      map_mul' := fun I K => by
        change ((normalizedFactors ((I : Ideal O) * (K : Ideal O))).map primeAction).prod = _
        rw [normalizedFactors_mul (nonZeroDivisors.coe_ne_zero I)
          (nonZeroDivisors.coe_ne_zero K), Multiset.map_add, Multiset.prod_add] }
  have hprimeAction (v : ι) : primeAction v.asIdeal = frob v := by
    dsimp [primeAction]
    rw [dif_pos ⟨v.isPrime, v.ne_bot⟩]
  have hAprime (v : ι) :
      A ⟨v.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr v.ne_bot⟩ = frob v := by
    change ((normalizedFactors v.asIdeal).map primeAction).prod = frob v
    rw [normalizedFactors_irreducible v.irreducible, normalize_eq,
      Multiset.map_singleton, Multiset.prod_singleton, hprimeAction]
  have hAnorm (I : (Ideal O)⁰) (hI : (absNorm (I : Ideal O)).Coprime q) :
      A I ζ = ζ ^ absNorm (I : Ideal O) := by
    have hfactor (P : Ideal O) (hP : P ∈ normalizedFactors (I : Ideal O)) :
        primeAction P ζ = ζ ^ absNorm P := by
      have hp := prime_of_normalized_factor P hP
      let v : ι := ⟨P, Ideal.isPrime_of_prime hp, hp.ne_zero⟩
      change primeAction v.asIdeal ζ = ζ ^ absNorm v.asIdeal
      rw [hprimeAction]
      exact hnormAction v (hI.of_dvd_left (absNorm.map_dvd (dvd_of_mem_normalizedFactors hP)))
    have hprod (s : Multiset (Ideal O))
        (hs : ∀ P ∈ s, primeAction P ζ = ζ ^ absNorm P) :
        (s.map primeAction).prod ζ = ζ ^ (s.map absNorm).prod := by
      induction s using Multiset.induction_on with
      | empty =>
        change (1 : M ≃ₐ[F] M) ζ = ζ ^ 1
        exact (AlgEquiv.one_apply ζ).trans (pow_one ζ).symm
      | cons P s ih =>
        have hPs := hs P (Multiset.mem_cons_self P s)
        have hss : ∀ K ∈ s, primeAction K ζ = ζ ^ absNorm K :=
          fun K hK => hs K (Multiset.mem_cons_of_mem hK)
        simp only [Multiset.map_cons, Multiset.prod_cons]
        change primeAction P (((s.map primeAction).prod) ζ) =
          ζ ^ (absNorm P * (s.map absNorm).prod)
        rw [ih hss, map_pow, hPs, pow_mul]
    change ((normalizedFactors (I : Ideal O)).map primeAction).prod ζ = _
    rw [hprod _ hfactor, ← map_multiset_prod,
      prod_normalizedFactors_eq (nonZeroDivisors.coe_ne_zero I), normalize_eq]
  -- Step 22: determinant reduction gives the ray-principal norm congruence.
  have hnormCongruence (a b c : O) (hac : a = b + (q : O) * c) :
      (Algebra.norm ℤ a : ZMod q) = (Algebra.norm ℤ b : ZMod q) := by
    let basis := Module.Free.chooseBasis ℤ O
    let red := (Int.castRingHom (ZMod q)).mapMatrix.comp
      (Algebra.leftMulMatrix basis).toRingHom
    have hr : red a = red b := by
      rw [hac, map_add, map_mul, map_natCast]
      have hz : (q : Matrix (Module.Free.ChooseBasisIndex ℤ O)
          (Module.Free.ChooseBasisIndex ℤ O) (ZMod q)) = 0 := by
        ext i j
        simp [Matrix.natCast_apply]
      rw [hz, zero_mul, add_zero]
    rw [Algebra.norm_eq_matrix_det basis, Algebra.norm_eq_matrix_det basis]
    calc
      _ = Matrix.det (red a) := (Int.castRingHom (ZMod q)).map_det _
      _ = Matrix.det (red b) := congrArg Matrix.det hr
      _ = _ := ((Int.castRingHom (ZMod q)).map_det _).symm
  have hAmod (I K : (Ideal O)⁰)
      (hK : (absNorm (K : Ideal O)).Coprime q)
      (hIK : (absNorm (I : Ideal O) : ZMod q) = (absNorm (K : Ideal O) : ZMod q)) :
      A I = A K := by
    have hI : (absNorm (I : Ideal O)).Coprime q := by
      rw [← ZMod.isUnit_iff_coprime, hIK]
      exact (ZMod.isUnit_iff_coprime _ _).mpr hK
    apply hrootext
    rw [hAnorm I hI, hAnorm K hK]
    exact pow_eq_pow_of_modEq ((ZMod.natCast_eq_natCast_iff ..).mp hIK) hζ.pow_eq_one
  have hnormSign (a : O) (ha : ∀ φ : F →+* ℝ, 0 ≤ φ (a : F)) :
      0 ≤ Algebra.norm ℤ a := by
    have hn := Algebra.norm_eq_prod_embeddings ℚ ℂ (a : F)
    change ((Algebra.norm ℚ (a : F) : ℚ) : ℂ) = _ at hn
    rw [← Algebra.coe_norm_int] at hn
    simp only [Rat.cast_intCast] at hn
    rw [← Fintype.prod_equiv (RingHom.equivRatAlgHom F ℂ)
      (fun φ => φ (a : F)) (fun φ => φ (a : F))
      (fun _ => by simp [RingHom.equivRatAlgHom_apply])] at hn
    have hfac (w : NumberField.InfinitePlace F) : ∃ r : ℝ, 0 ≤ r ∧
        (∏ φ ∈ Finset.univ.filter (fun φ : F →+* ℂ => NumberField.InfinitePlace.mk φ = w), φ (a : F)) = (r : ℂ) := by
      have hfilter : (Finset.univ.filter (fun φ : F →+* ℂ => NumberField.InfinitePlace.mk φ = w)) =
          {NumberField.InfinitePlace.embedding w, NumberField.ComplexEmbedding.conjugate (NumberField.InfinitePlace.embedding w)} := by
        ext φ
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_insert, Finset.mem_singleton]
        conv_lhs => rw [← NumberField.InfinitePlace.mk_embedding w, NumberField.InfinitePlace.mk_eq_iff, NumberField.ComplexEmbedding.conjugate, star_involutive.eq_iff]
      rw [hfilter]
      by_cases hw : NumberField.InfinitePlace.IsReal w
      · refine ⟨NumberField.InfinitePlace.embedding_of_isReal hw a, ha (NumberField.InfinitePlace.embedding_of_isReal hw), ?_⟩
        rw [NumberField.InfinitePlace.conjugate_embedding_eq_of_isReal hw, Finset.pair_eq_singleton,
          Finset.prod_singleton, NumberField.InfinitePlace.embedding_of_isReal_apply hw]
      · refine ⟨Complex.normSq (NumberField.InfinitePlace.embedding w (a : F)), Complex.normSq_nonneg _, ?_⟩
        have hne : NumberField.InfinitePlace.embedding w ≠ NumberField.ComplexEmbedding.conjugate (NumberField.InfinitePlace.embedding w) := by
          intro heq
          apply hw
          exact NumberField.InfinitePlace.isReal_iff.mpr (NumberField.ComplexEmbedding.isReal_iff.mpr heq.symm)
        rw [Finset.prod_pair hne]
        exact Complex.mul_conj _
    choose r hr heq using hfac
    have hnorm : (Algebra.norm ℤ a : ℂ) = (∏ w, r w : ℝ) := by
      rw [hn, ← Finset.prod_fiberwise Finset.univ NumberField.InfinitePlace.mk]
      simp_rw [heq]
      simp only [Complex.ofReal_prod]
    have hnormReal : (Algebra.norm ℤ a : ℝ) = ∏ w, r w := by
      exact_mod_cast hnorm
    have hnonneg : (0 : ℝ) ≤ ∏ w, r w := Finset.prod_nonneg (fun w _ => hr w)
    rw [← hnormReal] at hnonneg
    exact_mod_cast hnonneg
  have hAprincipal (a c : O) (b : ℕ)
      (ha : a ≠ 0) (hb0 : b ≠ 0) (hb : b.Coprime q)
      (haNorm : 0 ≤ Algebra.norm ℤ a) (hab : a = (b : O) + q * c) :
      A ⟨span {a}, mem_nonZeroDivisors_iff_ne_zero.mpr
        (span_singleton_eq_bot.not.mpr ha)⟩ =
      A ⟨span {(b : O)}, mem_nonZeroDivisors_iff_ne_zero.mpr
        (span_singleton_eq_bot.not.mpr (Nat.cast_ne_zero.mpr hb0))⟩ := by
    apply hAmod
    · rw [absNorm_span_natCast]
      exact hb.pow_left _
    · have hapos : ((Algebra.norm ℤ a).natAbs : ℤ) = Algebra.norm ℤ a := by
        rw [Int.natCast_natAbs, abs_of_nonneg haNorm]
      have hbpos : 0 ≤ Algebra.norm ℤ (b : O) := by
        rw [Algebra.norm_natCast]
        positivity
      have hbabs : ((Algebra.norm ℤ (b : O)).natAbs : ℤ) = Algebra.norm ℤ (b : O) := by
        rw [Int.natCast_natAbs, abs_of_nonneg hbpos]
      rw [absNorm_span_singleton, absNorm_span_singleton,
        ← Int.cast_natCast, hapos, ← Int.cast_natCast, hbabs]
      exact hnormCongruence a b c hab
  have hAray (I K : (Ideal O)⁰) (a c : O) (b : ℕ)
      (ha : a ≠ 0) (hb0 : b ≠ 0) (hb : b.Coprime q)
      (haPos : ∀ φ : F →+* ℝ, 0 < φ (a : F)) (hab : a = (b : O) + q * c)
      (hIK : span {a} * (I : Ideal O) = span {(b : O)} * (K : Ideal O)) :
      A I = A K := by
    let Pa : (Ideal O)⁰ := ⟨span {a}, mem_nonZeroDivisors_iff_ne_zero.mpr
      (span_singleton_eq_bot.not.mpr ha)⟩
    let Pb : (Ideal O)⁰ := ⟨span {(b : O)}, mem_nonZeroDivisors_iff_ne_zero.mpr
      (span_singleton_eq_bot.not.mpr (Nat.cast_ne_zero.mpr hb0))⟩
    have hmul : Pa * I = Pb * K := Subtype.ext hIK
    have hmap := congrArg A hmul
    rw [map_mul, map_mul, hAprincipal a c b ha hb0 hb (hnormSign a (fun φ => (haPos φ).le)) hab] at hmap
    exact mul_left_cancel hmap
  -- Step 22: the primes above q are finite, and avoiding them is norm coprimality.
  have hfiniteBad : {v : ι | (q : O) ∈ v.asIdeal}.Finite := by
    exact (Ring.HasFiniteQuotients.finite_setOfPred_mem (q : O)
      (Nat.cast_ne_zero.mpr hq.ne_zero)).preimage
        IsDedekindDomain.HeightOneSpectrum.asIdeal_injective.injOn
  let T : Finset ι := hfiniteBad.toFinset
  have hT (v : ι) : v ∈ T ↔ (q : O) ∈ v.asIdeal := hfiniteBad.mem_toFinset
  have hcoprimeI (I : Ideal O) :
      (∀ v ∈ T, ¬ v.asIdeal ∣ I) ↔ (absNorm I).Coprime q := by
    constructor
    · intro havoid
      rw [Nat.coprime_comm, hq.coprime_iff_not_dvd]
      intro hdiv
      obtain ⟨Q, hQ, hQunder, hQI⟩ :=
        Ideal.exists_isMaximal_dvd_of_dvd_absNorm' hq I hdiv
      let : Q.IsMaximal := hQ
      let v : ι := ⟨Q, hQ.isPrime, Ideal.IsMaximal.ne_bot_of_isIntegral_int Q⟩
      have hqQ : (q : ℤ) ∈ Q.under ℤ := by
        rw [hQunder]
        exact Ideal.subset_span (Set.mem_singleton _)
      have hqv : (q : O) ∈ v.asIdeal := by
        simpa only [Ideal.mem_under, map_natCast, Int.cast_natCast] using hqQ
      exact havoid v ((hT v).mpr hqv) hQI
    · intro hcop v hv hdiv
      obtain ⟨a, b, hab⟩ := hcop.cast (R := O)
      have hnorm : (absNorm I : O) ∈ v.asIdeal :=
        (Ideal.dvd_iff_le.mp hdiv) I.absNorm_mem
      have hone : (1 : O) ∈ v.asIdeal := by
        rw [← hab]
        exact v.asIdeal.add_mem (v.asIdeal.mul_mem_left a hnorm)
          (v.asIdeal.mul_mem_left b ((hT v).mp hv))
      exact v.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem v.asIdeal hone isUnit_one)
  suffices hcharacters :
      ∀ k : Fin m, ∃ C : ℝ, 0 ≤ C ∧ ∃ ε : ℝ, 0 < ε ∧
        ∀ s : ℝ, 1 < s → s < 1 + ε →
          ‖(∑' v : ι, ω ^ (k.val * (code (frob v)).val) *
            Complex.ofReal (Real.rpow (N v : ℝ) (-s))) -
              (if k.val = 0 then (Real.log (1 / (s - 1)) : ℂ) else 0)‖ ≤ C by
    exact hfinish frob hsum hcharacters (hbadFromHigher hsum hhigher)
      (fun v _ => ⟨val v, hval v, hfrob v⟩)
  intro k
  let χ : ι → ℂ := fun v => ω ^ (k.val * (code (frob v)).val)
  have hχ (v : ι) : ‖χ v‖ = 1 := by
    simp only [χ, norm_pow, hω.norm'_eq_one hm.ne', one_pow]
  let E : ℝ → ℂ := fun s => ∑' v,
    -Complex.log (1 - χ v * Complex.ofReal (Real.rpow (N v : ℝ) (-s)))
  let P : ℝ → ℂ := fun s => ∑' v,
    χ v * Complex.ofReal (Real.rpow (N v : ℝ) (-s))
  let d : ℝ → ℂ := fun s =>
    if k.val = 0 then (Real.log (1 / (s - 1)) : ℂ) else 0
  have hE : ContinuousOn E (Set.Ioo 1 2) :=
    (hEulerContinuous χ hχ).mono (fun _ hs => hs.1)
  have hd : ContinuousOn d (Set.Ioo 1 2) := by
    by_cases hk : k.val = 0
    · simp only [d, hk, if_true]
      apply Complex.continuous_ofReal.comp_continuousOn
      apply ContinuousOn.log
      · exact continuousOn_const.div (continuousOn_id.sub continuousOn_const)
          (fun s hs => by linarith [hs.1])
      · intro s hs
        exact one_div_ne_zero (by linarith [hs.1])
    · simp only [d, hk, if_false]
      exact continuousOn_const
  obtain ⟨R, hR, htail⟩ := hEulerTail χ hχ
  suffices hL : ∃ L : ℝ → ℂ,
      ContinuousWithinAt L (Set.Ici 1) 1 ∧ L 1 ≠ 0 ∧
        ∀ s : ℝ, s ∈ Set.Ioo 1 2 → Complex.exp (E s - d s) = L s by
    obtain ⟨L, hL, hL₁, hexp⟩ := hL
    obtain ⟨C, hC, ε, hε, _, hbound⟩ := hprimeBound
      (fun s => E s - d s) L (fun s => P s - d s) (hE.sub hd) hL hL₁ hexp
      R hR (fun s hs _ => by
        have heq : (P s - d s) - (E s - d s) = P s - E s := by ring
        rw [heq]
        exact htail s hs)
    exact ⟨C, hC, ε, hε, hbound⟩
  by_cases hk : k.val = 0
  · have hprincipal :
        ∃ L : ℝ → ℂ, ContinuousWithinAt L (Set.Ici 1) 1 ∧ L 1 ≠ 0 ∧
          ∀ s : ℝ, s ∈ Set.Ioo 1 2 →
            Complex.exp ((∑' v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F),
              -Complex.log (1 - (Real.rpow (absNorm v.asIdeal : ℝ) (-s) : ℂ))) -
                (Real.log (1 / (s - 1)) : ℂ)) = L s := by
      classical
      let L : ℝ → ℂ := Function.update
        (fun s : ℝ => ((s : ℂ) - 1) * NumberField.dedekindZeta F (s : ℂ))
        1 (NumberField.dedekindZeta_residue F : ℂ)
      have hLone : L 1 = (NumberField.dedekindZeta_residue F : ℂ) := Function.update_self ..
      refine ⟨L, ?_, ?_, ?_⟩
      · apply continuousWithinAt_Ioi_iff_Ici.mp
        change Tendsto L (𝓝[>] (1 : ℝ)) (𝓝 (L 1))
        rw [hLone]
        apply (NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT F).congr'
        filter_upwards [self_mem_nhdsWithin] with s hs
        change 1 < s at hs
        simp only [L, Function.update_of_ne (ne_of_gt hs)]
      · rw [hLone, Complex.ofReal_ne_zero]
        exact NumberField.dedekindZeta_residue_ne_zero F
      · intro s hs
        let f : Ideal (NumberField.RingOfIntegers F) →*₀ ℂ :=
          { toFun := fun I => (Real.rpow (absNorm I : ℝ) (-s) : ℂ)
            map_zero' := by
              rw [map_zero, Nat.cast_zero, Real.rpow_eq_pow,
                Real.zero_rpow (by linarith [hs.1]), Complex.ofReal_zero]
            map_one' := by
              rw [map_one, Nat.cast_one, Real.rpow_eq_pow, Real.one_rpow, Complex.ofReal_one]
            map_mul' := fun I J => by
              simp only [map_mul, Nat.cast_mul, Real.rpow_eq_pow,
                Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _), Complex.ofReal_mul] }
        have hf : Summable (fun I => ‖f I‖) := by
          apply (hIdealSeries s hs.1).1.congr
          intro I
          dsimp [f]
          rw [Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
        have hsmall (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) :
            1 - f v.asIdeal ≠ 0 := by
          intro hz
          have hnorm : Real.rpow (absNorm v.asIdeal : ℝ) (-s) < 1 := by
            rw [Real.rpow_eq_pow]
            exact Real.rpow_lt_one_of_one_lt_of_neg
              (by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v)
              (by linarith [hs.1])
          have heq := congrArg Complex.re (sub_eq_zero.mp hz)
          change (1 : ℝ) = Real.rpow (absNorm v.asIdeal : ℝ) (-s) at heq
          linarith
        have heuler := (hEulerIdeal (NumberField.RingOfIntegers F) f hf hsmall).trans (hIdealSeries s hs.1).2.symm
        change Complex.exp ((∑' v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F),
          -Complex.log (1 - f v.asIdeal)) - (Real.log (1 / (s - 1)) : ℂ)) = L s
        rw [Complex.exp_sub, heuler]
        have hexp : Complex.exp (Real.log (1 / (s - 1)) : ℂ) =
            (1 / (s - 1) : ℝ) := by
          rw [← Complex.ofReal_exp, Real.exp_log (one_div_pos.mpr (sub_pos.mpr hs.1))]
        rw [hexp]
        simp only [L, Function.update_of_ne (ne_of_gt hs.1), Complex.ofReal_div,
          Complex.ofReal_one, Complex.ofReal_sub]
        rw [div_div_eq_mul_div, div_one]
        exact mul_comm _ _
    simpa only [E, d, χ, hk, if_true, zero_mul, pow_zero, one_mul] using hprincipal
  · -- Step 24: identify the actual Euler product with its ideal character series.
    let : NeZero m := ⟨hm.ne'⟩
    let ψ : J →* ℂ :=
      { toFun := fun σ => ω ^ (k.val * (code σ).val)
        map_one' := by simp [code]
        map_mul' := fun σ τ => by
          have hcodeMul : code (σ * τ) = code σ + code τ :=
            congrArg Multiplicative.toAdd (map_mul e.symm σ τ)
          have hmod : ω ^ (((code σ).val + (code τ).val) % m) =
              ω ^ ((code σ).val + (code τ).val) := by
            simpa only [← hω.eq_orderOf] using
              pow_mod_orderOf ω ((code σ).val + (code τ).val)
          rw [hcodeMul, ZMod.val_add, Nat.mul_comm k.val, pow_mul, hmod,
            ← pow_mul, Nat.mul_comm _ k.val, Nat.mul_add, pow_add] }
    have hψ (σ : J) : ‖ψ σ‖ = 1 := by
      change ‖ω ^ (k.val * (code σ).val)‖ = 1
      rw [norm_pow, hω.norm'_eq_one hm.ne', one_pow]
    let w : Ideal O →*₀ ℂ :=
      { toFun := fun I => if hI : I = 0 then 0 else
          ψ (A ⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI⟩)
        map_zero' := by exact dif_pos rfl
        map_one' := by
          rw [dif_neg one_ne_zero]
          change ψ (A 1) = 1
          rw [map_one, map_one]
        map_mul' := fun I K => by
          by_cases hI : I = 0
          · subst I
            rw [zero_mul, dif_pos rfl, zero_mul]
          by_cases hK : K = 0
          · subst K
            rw [mul_zero, dif_pos rfl, mul_zero]
          rw [dif_neg (mul_ne_zero hI hK), dif_neg hI, dif_neg hK]
          change ψ (A ((⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI⟩ : (Ideal O)⁰) *
            ⟨K, mem_nonZeroDivisors_iff_ne_zero.mpr hK⟩)) = _
          rw [map_mul, map_mul] }
    have hwval (I : Ideal O) (hI : I ≠ 0) :
        w I = ψ (A ⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI⟩) := dif_neg hI
    have hw (I : Ideal O) (hI : I ≠ 0) : ‖w I‖ = 1 := by
      rw [hwval I hI, hψ]
    have hwprime (v : ι) : w v.asIdeal = χ v := by
      rw [hwval _ v.ne_bot, hAprime]
      rfl
    have hwRay (I K : (Ideal O)⁰) (a c : O) (b : ℕ)
        (ha : a ≠ 0) (hb0 : b ≠ 0) (hb : b.Coprime q)
        (haPos : ∀ φ : F →+* ℝ, 0 < φ (a : F)) (hab : a = (b : O) + q * c)
        (hIK : span {a} * (I : Ideal O) = span {(b : O)} * (K : Ideal O)) :
        w (I : Ideal O) = w (K : Ideal O) := by
      rw [hwval _ (nonZeroDivisors.coe_ne_zero I),
        hwval _ (nonZeroDivisors.coe_ne_zero K)]
      exact congrArg ψ (hAray I K a c b ha hb0 hb haPos hab hIK)
    let S : ℝ → ℂ := fun s => ∑' I : Ideal O,
      w I * Complex.ofReal (Real.rpow (absNorm I : ℝ) (-s))
    let weighted (s : ℝ) : Ideal O →*₀ ℂ :=
      { toFun := fun I => w I * Complex.ofReal (Real.rpow (absNorm I : ℝ) (-s))
        map_zero' := by simp only [map_zero, zero_mul]
        map_one' := by
          rw [map_one, map_one, Nat.cast_one, Real.rpow_eq_pow,
            Real.one_rpow, Complex.ofReal_one, one_mul]
        map_mul' := fun I K => by
          simp only [map_mul, Nat.cast_mul, Real.rpow_eq_pow,
            Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _), Complex.ofReal_mul]
          ring }
    have hweightedNorm (s : ℝ) (hs : 1 < s) (I : Ideal O) : ‖weighted s I‖ = Real.rpow (absNorm I : ℝ) (-s) := by
      by_cases hI : I = 0
      · subst I
        rw [map_zero, norm_zero, map_zero, Nat.cast_zero, Real.rpow_eq_pow,
          Real.zero_rpow (by linarith : -s ≠ 0)]
      · change ‖w I * Complex.ofReal (Real.rpow (absNorm I : ℝ) (-s))‖ = _
        rw [norm_mul, hw I hI, one_mul, Complex.norm_real, Real.norm_eq_abs, Real.rpow_eq_pow,
          abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
    have hweightedSummable (s : ℝ) (hs : 1 < s) :
        Summable (fun I : Ideal O => ‖weighted s I‖) :=
      (hIdealSeries s hs).1.congr (fun I => (hweightedNorm s hs I).symm)
    have hseries (s : ℝ) (hs : 1 < s) : Complex.exp (E s) = S s := by
      let f := weighted s
      have hnorm := hweightedNorm s hs
      have hf := hweightedSummable s hs
      have hsmall (v : ι) : 1 - f v.asIdeal ≠ 0 := by
        intro hz
        have hlt : Real.rpow (absNorm v.asIdeal : ℝ) (-s) < 1 :=
          Real.rpow_lt_one_of_one_lt_of_neg
            (by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v)
            (by linarith)
        have heq := congrArg norm (sub_eq_zero.mp hz)
        rw [norm_one, hnorm] at heq
        linarith
      have heuler := hEulerIdeal O f hf hsmall
      have hfprime (v : ι) :
          f v.asIdeal = χ v * Complex.ofReal (Real.rpow (N v : ℝ) (-s)) := by
        change w v.asIdeal * Complex.ofReal (Real.rpow (N v : ℝ) (-s)) = _
        rw [hwprime]
      change Complex.exp (∑' v : ι, -Complex.log (1 - f v.asIdeal)) = S s at heuler
      simpa only [hfprime] using heuler
    suffices hcontinuation : ∃ L : ℝ → ℂ,
        ContinuousWithinAt L (Set.Ici 1) 1 ∧ L 1 ≠ 0 ∧
          ∀ s : ℝ, s ∈ Set.Ioo 1 2 → S s = L s by
      obtain ⟨L, hL, hLone, hSL⟩ := hcontinuation
      refine ⟨L, hL, hLone, ?_⟩
      intro s hs
      simpa only [d, hk, if_false, sub_zero] using (hseries s hs.1).trans (hSL s hs)
    -- Steps 22–25: remove precisely the Euler factors above the cyclotomic modulus.
    let Sgood : ℝ → ℂ := fun s => ∑' I : Ideal O,
      if (absNorm I).Coprime q then
        w I * Complex.ofReal (Real.rpow (absNorm I : ℝ) (-s)) else 0
    let factor : ℝ → ℂ := fun s => ∏ v ∈ T,
      (1 - w v.asIdeal * Complex.ofReal (Real.rpow (N v : ℝ) (-s)))
    have hfactorContinuous : Continuous factor := by
      apply continuous_finsetProd T
      intro v _
      apply continuous_const.sub
      apply continuous_const.mul
      apply Complex.continuous_ofReal.comp
      exact (Real.continuous_const_rpow (by
        exact_mod_cast (show N v ≠ 0 by have := hN v; omega))).comp continuous_neg
    have hfactorNonzero (s : ℝ) (hs : 1 ≤ s) : factor s ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro v _ hz
      have heq := congrArg norm (sub_eq_zero.mp hz)
      rw [norm_one, norm_mul, hw _ v.ne_bot, one_mul, Complex.norm_real,
        Real.norm_eq_abs, Real.rpow_eq_pow,
        abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)] at heq
      have hlt : Real.rpow (N v : ℝ) (-s) < 1 :=
        Real.rpow_lt_one_of_one_lt_of_neg
          (by exact_mod_cast (hN v))
          (neg_lt_zero.mpr (lt_of_lt_of_le zero_lt_one hs))
      rw [Real.rpow_eq_pow] at hlt
      exact hlt.ne heq.symm
    have hSgood (s : ℝ) (hs : 1 < s) : factor s * S s = Sgood s := by
      let f := weighted s
      have hf := hweightedSummable s hs
      change (∏ v ∈ T, (1 - f v.asIdeal)) * (∑' I : Ideal O, f I) = _
      rw [hIdealSieve O f hf T]
      exact tsum_congr (fun I => if_congr (hcoprimeI I) rfl rfl)
    have hrecover :
        (∃ Lgood : ℝ → ℂ, ContinuousWithinAt Lgood (Set.Ici 1) 1 ∧ Lgood 1 ≠ 0 ∧
          ∀ s : ℝ, s ∈ Set.Ioo 1 2 → Sgood s = Lgood s) →
        ∃ L : ℝ → ℂ, ContinuousWithinAt L (Set.Ici 1) 1 ∧ L 1 ≠ 0 ∧
          ∀ s : ℝ, s ∈ Set.Ioo 1 2 → S s = L s := by
      rintro ⟨Lgood, hLgood, hLgoodOne, heq⟩
      refine ⟨fun s => Lgood s / factor s,
        hLgood.div hfactorContinuous.continuousWithinAt (hfactorNonzero 1 le_rfl),
        div_ne_zero hLgoodOne (hfactorNonzero 1 le_rfl), ?_⟩
      intro s hs
      apply (eq_div_iff (hfactorNonzero s hs.1.le)).mpr
      rw [mul_comm, hSgood s hs.1]
      exact heq s hs
    apply hrecover
    -- Steps 15–25 still require ray-class counting and the nonvanishing argument.
    fail "Unfinished arithmetic input: continuously extend the prime-to-q ideal character series Sgood with nonzero value at one."
