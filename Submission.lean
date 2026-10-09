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

open scoped Pointwise in
/-- Finite Frobenius supply, with uniqueness obtained by excluding nontrivial inertia. -/
theorem Submission.p09_af497904fe_fa_finite_frobenius :
    ∀ (E : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ E]
      [IsGalois ℚ E] (g : E ≃ₐ[ℚ] E) (B : Finset ℕ),
      ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ∉ B ∧ ∃ V : ValuationSubring E,
        V.LiesOverPrime ℓ ∧ V.IsFrobeniusAt g ℓ ∧
        ∀ g' : E ≃ₐ[ℚ] E, V.IsFrobeniusAt g' ℓ → g' = g := by
  classical
  intro E _ _ g B
  obtain ⟨S, hS⟩ := Submission.p09_af497904fe_ff_finite_inertia_exclusion E
  obtain ⟨M, hMfin, _hMgal, ι, F, q, ζ, h, hq, hζ, hgen, hι⟩ :=
    Submission.p09_af497904fe_ff_cyclotomic_envelope E g
  have : FiniteDimensional ℚ M := hMfin
  obtain ⟨ℓ, hℓ, hℓBS, W, hWℓ, hWfrob⟩ :=
    Submission.p09_af497904fe_ff_cyclotomic_supply M F q ζ hq hζ hgen h (B ∪ S)
  have hℓB : ℓ ∉ B := fun hB => hℓBS (Finset.mem_union_left S hB)
  have hℓS : ℓ ∉ S := fun hS => hℓBS (Finset.mem_union_right B hS)
  -- Contract the supplied place along the equivariant embedding of E into M.
  let V : ValuationSubring E := W.comap ι.toRingHom
  have hnonunit (x : E) : x ∈ V.nonunits ↔ ι x ∈ W.nonunits := by
    simp only [ValuationSubring.mem_nonunits_iff_or, V,
      ValuationSubring.mem_comap, map_inv₀, map_eq_zero]
    rfl
  have hVℓ : V.LiesOverPrime ℓ := by
    apply (hnonunit (ℓ : E)).mpr
    change (ℓ : M) ∈ W.nonunits at hWℓ
    simpa only [map_natCast] using hWℓ
  have hWmem (x : M) : h x ∈ W ↔ x ∈ W := by
    have hstable : h • W = W := hWfrob.mem_decompositionSubgroup
    simpa only [hstable, AlgEquiv.smul_def] using
      (ValuationSubring.smul_mem_pointwise_smul_iff (g := h) (S := W) (x := x))
  have hgmem (x : E) : g x ∈ V ↔ x ∈ V := by
    change ι (g x) ∈ W ↔ ι x ∈ W
    rw [← hι x]
    exact hWmem (ι x)
  have hgdec : g ∈ V.decompositionSubgroup ℚ := by
    change g • V = V
    apply ValuationSubring.ext
    intro x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    change g.symm x ∈ V ↔ x ∈ V
    simpa only [AlgEquiv.apply_symm_apply] using (hgmem (g.symm x)).symm
  have hVfrob : V.IsFrobeniusAt g ℓ := by
    refine ⟨hgdec, ?_⟩
    intro z
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective z
    let gd : V.decompositionSubgroup ℚ := ⟨g, hgdec⟩
    let hd : W.decompositionSubgroup F := ⟨h, hWfrob.mem_decompositionSubgroup⟩
    let y : W := ⟨ι (x : E), x.property⟩
    -- Vanishing upstairs descends because nonunits contract along field embeddings.
    have hres : IsLocalRing.residue W (hd • y - y ^ ℓ) = 0 := by
      rw [map_sub, map_pow, IsLocalRing.ResidueField.residue_smul]
      exact sub_eq_zero.mpr (hWfrob.smul_residue_eq (IsLocalRing.residue W y))
    have hnM : ((hd • y - y ^ ℓ : W) : M) ∈ W.nonunits :=
      ValuationSubring.coe_mem_nonunits_iff.mpr ((IsLocalRing.residue_eq_zero_iff _).mp hres)
    have hnE : ((gd • x - x ^ ℓ : V) : E) ∈ V.nonunits := by
      apply (hnonunit _).mpr
      change ι (g (x : E) - (x : E) ^ ℓ) ∈ W.nonunits
      change h (ι (x : E)) - ι (x : E) ^ ℓ ∈ W.nonunits at hnM
      simpa only [map_sub, map_pow, ← hι (x : E)] using hnM
    have hz : IsLocalRing.residue V (gd • x - x ^ ℓ) = 0 :=
      (IsLocalRing.residue_eq_zero_iff _).mpr (ValuationSubring.coe_mem_nonunits_iff.mp hnE)
    rw [map_sub, map_pow, IsLocalRing.ResidueField.residue_smul] at hz
    exact sub_eq_zero.mp hz
  refine ⟨ℓ, hℓ, hℓB, V, hVℓ, hVfrob, ?_⟩
  intro g' hg'
  -- Equal Frobenius actions differ by an inertia element, which is trivial here.
  let gd : V.decompositionSubgroup ℚ := ⟨g, hVfrob.mem_decompositionSubgroup⟩
  let gd' : V.decompositionSubgroup ℚ := ⟨g', hg'.mem_decompositionSubgroup⟩
  have hinertia : gd⁻¹ * gd' ∈ V.inertiaSubgroup ℚ := by
    change MulSemiringAction.toRingAut (V.decompositionSubgroup ℚ)
      (IsLocalRing.ResidueField V) (gd⁻¹ * gd') = 1
    ext z
    change (gd⁻¹ * gd') • z = z
    rw [mul_smul]
    have heq : gd' • z = gd • z :=
      (hg'.smul_residue_eq z).trans (hVfrob.smul_residue_eq z).symm
    rw [heq, inv_smul_smul]
  have hinertiaIn : g⁻¹ * g' ∈ V.inertiaSubgroupIn ℚ :=
    ⟨gd⁻¹ * gd', hinertia, rfl⟩
  have heq : g⁻¹ * g' = 1 := hS ℓ hℓ hℓS V hVℓ _ hinertiaIn
  exact (inv_mul_eq_one.mp heq).symm
