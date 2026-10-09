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
    convert (J ^ n).add_mem (hβ 1 n) (hone n) using 1 <;> ring
  have hβmul (g h : G) : β (g * h) = β g * β h := by
    apply hsep
    intro n
    convert (J ^ n).sub_mem
      ((J ^ n).add_mem (hβ (g * h) n) (hmul n g h))
      ((J ^ n).add_mem
        (Ideal.mul_mem_right (a n h) (J ^ n) (hβ g n))
        ((J ^ n).mul_mem_left (β g) (hβ h n))) using 1 <;> ring
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
    convert (J ^ n).sub_mem (hb' n g) (hβ g n) using 1 <;> ring
