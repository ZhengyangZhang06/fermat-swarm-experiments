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
  classical
  have _ := hD
  let : IsLocalHom (algebraMap 𝒪 R) := hl
  let : IsNoetherianRing R := IsNoetherianRing.of_finite 𝒪 R
  let : Module.Finite R Y := Module.Finite.of_restrictScalars_finite 𝒪 R Y
  have hpR : (p : R) ∈ maximalIdeal R := by
    simpa only [map_natCast] using map_nonunit (algebraMap 𝒪 R) (p : 𝒪) hp𝒪
  have hp_le : Ideal.span {(p : R)} ≤ maximalIdeal R :=
    (Ideal.span_singleton_le_iff_mem _).mpr hpR
  -- Fix the two characters before choosing an automorphism or a precision.
  obtain ⟨c, hccont, hcfrob⟩ :=
    Submission.p09_af497904fe_adic_cyclotomic_character p hp𝒪 hl
  obtain ⟨χ, Fχ, hFχ, hχcont, _, hχfrob⟩ :=
    Submission.p09_af497904fe_finite_cyclotomic_character L
  let : FiniteDimensional ℚ Fχ := hFχ
  refine ⟨c, χ, fun σ => ?_⟩
  apply LinearMap.ext
  intro y
  change (ρY σ * ρY σ - (ρ.trace σ) • ρY σ + (c σ : R) • D (χ σ)) y = 0
  apply (Submodule.mem_bot R).mp
  rw [← Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := Y) (maximalIdeal R)
    (Ideal.IsMaximal.ne_top inferInstance)]
  apply (Submodule.mem_iInf _).mpr
  intro n
  obtain ⟨FY, hFY, hYcont⟩ := hcont n
  obtain ⟨Fρ, hFρ, hρcont⟩ := ρ.isAdicContinuous n
  obtain ⟨Fc, hFc, hc⟩ := hccont n
  let : FiniteDimensional ℚ FY := hFY
  let : FiniteDimensional ℚ Fρ := hFρ
  let : FiniteDimensional ℚ Fc := hFc
  -- A finite normal closure controls all four congruences simultaneously.
  let : IsAlgClosure ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.instIsAlgClosure ℚ
  let : Normal ℚ (AlgebraicClosure ℚ) := IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)
  let F : IntermediateField ℚ (AlgebraicClosure ℚ) := ((FY ⊔ Fρ) ⊔ Fc) ⊔ Fχ
  let E : IntermediateField ℚ (AlgebraicClosure ℚ) :=
    IntermediateField.normalClosure ℚ F (AlgebraicClosure ℚ)
  let : IsGalois ℚ E :=
    { to_isSeparable := inferInstance
      to_normal := normalClosure.normal ℚ F (AlgebraicClosure ℚ) }
  have hFE : F ≤ E := IntermediateField.le_normalClosure F
  -- Excluding all primes at most L in particular excludes every prime divisor of L.
  let B : Finset ℕ := S₀ ∪ insert p (Finset.range (L + 1))
  obtain ⟨ℓ, hℓ, hℓB, P, hP, τ, hτ, hτσ⟩ :=
    Submission.p09_af497904fe_frobenius_approximation E σ B
  have hℓS : ℓ ∉ S₀ := fun h => hℓB (Finset.mem_union_left _ h)
  have hℓp : ℓ ≠ p := by
    intro h
    apply hℓB
    simp only [B, h, Finset.mem_union, Finset.mem_insert, true_or, or_true]
  have hℓL : ¬ ℓ ∣ L := by
    intro h
    apply hℓB
    exact Finset.mem_union_right _ (Finset.mem_insert_of_mem
      (Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_of_dvd (NeZero.pos L) h))))
  have hagree : ∀ F' : IntermediateField ℚ (AlgebraicClosure ℚ), F' ≤ F →
      ∀ x ∈ F', σ x = τ x := by
    intro F' hF' x hx
    exact (hτσ x (hFE (hF' hx))).symm
  have hYagree := hagree FY
    ((le_sup_left.trans le_sup_left).trans le_sup_left)
  have hρagree := hagree Fρ
    ((le_sup_right.trans le_sup_left).trans le_sup_left)
  have hcagree := hagree Fc (le_sup_right.trans le_sup_left)
  have hχagree := hagree Fχ le_sup_right
  have hY : ∀ z : Y, (ρY σ - ρY τ) z ∈
      maximalIdeal R ^ n • (⊤ : Submodule R Y) := by
    intro z
    exact (Submodule.smul_mono_left (Ideal.pow_right_mono hp_le n))
      (Submission.p09_af497904fe_action_congruence
        (Ideal.span {(p : R)} ^ n) ρY FY hYcont σ τ hYagree z)
  have ht : ρ.trace σ - ρ.trace τ ∈ maximalIdeal R ^ n :=
    Submission.p09_af497904fe_trace_congruence (maximalIdeal R ^ n) (ρ.ρ σ) (ρ.ρ τ)
      (Submission.p09_af497904fe_action_congruence
        (maximalIdeal R ^ n) ρ.ρ Fρ hρcont σ τ hρagree)
  have hcℓ : (c σ : R) - (ℓ : R) ∈ maximalIdeal R ^ n := by
    rw [← hcfrob ℓ hℓ hℓp P hP τ hτ]
    exact hc σ τ hcagree
  have hχeq : χ σ = χ τ := hχcont σ τ hχagree
  have hzero : ρY τ * ρY τ - (ρ.trace τ) • ρY τ + (ℓ : R) • D (χ σ) = 0 := by
    rw [hχeq, hχfrob ℓ hℓ hℓL P hP τ hτ]
    exact hES ℓ hℓ hℓS hℓL hℓp P hP τ hτ
  have hquad := Submission.p09_af497904fe_quadratic_congruence
    (maximalIdeal R ^ n) (ρY σ) (ρY τ) (D (χ σ))
    (ρ.trace σ) (ρ.trace τ) (c σ : R) (ℓ : R) hY ht hcℓ y
  simpa only [hzero, sub_zero] using hquad
