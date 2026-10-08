/-
Copyright 2026 Anthropic, PBC. Licensed under Apache-2.0; see LICENSE.
Source: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_groupCohomology_bijective_theta_dualTwist_of_res_of_isOpen.lean
Modified: replaced the proof with sorry and removed P2M proof imports.
Requires the upstream Definitions modules and their dependencies.
-/

import Mathlib
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_ContinuousH2Map
import Definitions.Def_GroupCohomology_ContinuousH1
import Definitions.Def_GroupCohomology_CupProduct
import Definitions.Def_GroupCohomology_ContinuousDuality
import Definitions.Def_GroupCohomology_Selmer
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
attribute [-instance] groupCohomology.normal_comap_fixingSubgroup groupCohomology.finiteIndex_comap_fixingSubgroup

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory Module groupCohomology ExtCitation
theorem groupCohomology.bijective_theta_dualTwist_of_res_of_isOpen
    {p : ℕ} [Fact p.Prime] (q : Nat.Primes)
    (S : Subgroup (primeLocalGaloisGroup q)) (U : Subgroup S) [U.FiniteIndex] (hUp : IsUnit ((U.index : ℕ) : ZMod p))
    (hU : ∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧
      F₀.fixingSubgroup.comap ((primeLocalToGlobal q).comp S.subtype) ≤ U)
    (hTU : FiniteDimensional (ZMod p) (continuousH2 (((primeLocalToGlobal q).comp S.subtype).comp U.subtype) (Rep.res U.subtype (Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))))) ∧
      finrank (ZMod p) (continuousH2 (((primeLocalToGlobal q).comp S.subtype).comp U.subtype) (Rep.res U.subtype (Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))))) = 1)
    (M : Rep.{0} (ZMod p) S) [FiniteDimensional (ZMod p) M]
    (hsm : ∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s : S, ((primeLocalToGlobal q).comp S.subtype) s ∈ F.fixingSubgroup → M.ρ s m = m)
    (inv : continuousH2 ((primeLocalToGlobal q).comp S.subtype) (Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))) →ₗ[ZMod p] ZMod p)
    (hinv : Function.Bijective inv)
    (hres : ∀ (invU : continuousH2 (((primeLocalToGlobal q).comp S.subtype).comp U.subtype) (Rep.res U.subtype (Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))))) →ₗ[ZMod p] ZMod p),
      Function.Bijective invU →
      ∀ (θ₀ : (Rep.res U.subtype M).ρ.invariants →ₗ[ZMod p] Module.Dual (ZMod p)
          (continuousH2 (((primeLocalToGlobal q).comp S.subtype).comp U.subtype) (Rep.res U.subtype (M.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype))))),
        IsTheta0 (((primeLocalToGlobal q).comp S.subtype).comp U.subtype) (Module.Dual.eval (ZMod p) M : Rep.res U.subtype M →ₗ[ZMod p]
            Rep.res U.subtype (M.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype)) →ₗ[ZMod p]
            Rep.res U.subtype (Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))))) invU θ₀ →
      ∀ (θ₁ : continuousH1 (((primeLocalToGlobal q).comp S.subtype).comp U.subtype) (Rep.res U.subtype M) →ₗ[ZMod p] Module.Dual (ZMod p)
          (continuousH1 (((primeLocalToGlobal q).comp S.subtype).comp U.subtype) (Rep.res U.subtype (M.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype))))),
        IsTheta1 (((primeLocalToGlobal q).comp S.subtype).comp U.subtype) (Module.Dual.eval (ZMod p) M : Rep.res U.subtype M →ₗ[ZMod p]
            Rep.res U.subtype (M.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype)) →ₗ[ZMod p]
            Rep.res U.subtype (Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))))) invU θ₁ →
      ∀ (θ₂ : continuousH2 (((primeLocalToGlobal q).comp S.subtype).comp U.subtype) (Rep.res U.subtype M) →ₗ[ZMod p] Module.Dual (ZMod p)
          (Rep.res U.subtype (M.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype))).ρ.invariants),
        IsTheta2 (((primeLocalToGlobal q).comp S.subtype).comp U.subtype) (Module.Dual.eval (ZMod p) M : Rep.res U.subtype M →ₗ[ZMod p]
            Rep.res U.subtype (M.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype)) →ₗ[ZMod p]
            Rep.res U.subtype (Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))))) invU θ₂ →
      Function.Bijective θ₀ ∧ Function.Bijective θ₁ ∧ Function.Bijective θ₂)
    (θ₀ : M.ρ.invariants →ₗ[ZMod p] Module.Dual (ZMod p) (continuousH2 ((primeLocalToGlobal q).comp S.subtype) (M.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype))))
    (hθ₀ : IsTheta0 ((primeLocalToGlobal q).comp S.subtype) (Module.Dual.eval (ZMod p) M : M →ₗ[ZMod p] M.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype) →ₗ[ZMod p]
        Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))) inv θ₀)
    (θ₁ : continuousH1 ((primeLocalToGlobal q).comp S.subtype) M →ₗ[ZMod p] Module.Dual (ZMod p) (continuousH1 ((primeLocalToGlobal q).comp S.subtype) (M.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype))))
    (hθ₁ : IsTheta1 ((primeLocalToGlobal q).comp S.subtype) (Module.Dual.eval (ZMod p) M : M →ₗ[ZMod p] M.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype) →ₗ[ZMod p]
        Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))) inv θ₁)
    (θ₂ : continuousH2 ((primeLocalToGlobal q).comp S.subtype) M →ₗ[ZMod p] Module.Dual (ZMod p) (M.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype)).ρ.invariants)
    (hθ₂ : IsTheta2 ((primeLocalToGlobal q).comp S.subtype) (Module.Dual.eval (ZMod p) M : M →ₗ[ZMod p] M.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype) →ₗ[ZMod p]
        Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))) inv θ₂) :
    Function.Bijective θ₀ ∧ Function.Bijective θ₁ ∧ Function.Bijective θ₂ := by
  sorry

theorem Submission.p08_7d1ff633a4_linear_descent
    {k X Y X' Y' : Type} [Field k]
    [AddCommGroup X] [Module k X] [AddCommGroup Y] [Module k Y]
    [AddCommGroup X'] [Module k X'] [AddCommGroup Y'] [Module k Y']
    (n : k) (hn : n ≠ 0)
    (R_X : X →ₗ[k] X') (C_X : X' →ₗ[k] X)
    (R_Y : Y →ₗ[k] Y') (C_Y : Y' →ₗ[k] Y)
    (Θ : X →ₗ[k] Module.Dual k Y) (Θ' : X' →ₗ[k] Module.Dual k Y')
    (hX : ∀ x : X, C_X (R_X x) = n • x)
    (hY : ∀ y : Y, C_Y (R_Y y) = n • y)
    (hcompatX : ∀ (x : X) (y' : Y'), Θ' (R_X x) y' = Θ x (C_Y y'))
    (hcompatY : ∀ (x' : X') (y : Y), Θ' x' (R_Y y) = Θ (C_X x') y)
    (hΘ' : Function.Bijective Θ') : Function.Bijective Θ := by
  constructor
  · have hker : ∀ x : X, Θ x = 0 → x = 0 := by
      intro x hx
      have hRX : R_X x = 0 := hΘ'.1 (by
        ext y'
        simp only [hcompatX, hx, map_zero, LinearMap.zero_apply])
      have hnx : n • x = 0 := by
        rw [← hX x, hRX, map_zero]
      have hcancel := congrArg (fun z : X => n⁻¹ • z) hnx
      simpa only [inv_smul_smul₀ hn, smul_zero] using hcancel
    intro x₁ x₂ h
    apply sub_eq_zero.mp
    apply hker
    rw [map_sub, h, sub_self]
  · intro φ
    obtain ⟨x', hx'⟩ := hΘ'.2 (φ.comp C_Y)
    refine ⟨n⁻¹ • C_X x', ?_⟩
    ext y
    calc
      Θ (n⁻¹ • C_X x') y = n⁻¹ • Θ (C_X x') y := by
        simp only [map_smul, LinearMap.smul_apply]
      _ = n⁻¹ • Θ' x' (R_Y y) := by rw [hcompatY]
      _ = n⁻¹ • φ (C_Y (R_Y y)) := by rw [hx', LinearMap.comp_apply]
      _ = φ y := by rw [hY, map_smul, inv_smul_smul₀ hn]

theorem Submission.p08_7d1ff633a4_rank_one_transfer
    {k V W : Type} [Field k] [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (n : k) (hn : n ≠ 0) (R : V →ₗ[k] W) (C : W →ₗ[k] V) :
    (∀ v : V, C (R v) = n • v) → Module.finrank k W = 1 →
    ∀ ℓ : V →ₗ[k] k, Function.Surjective ℓ → Function.Bijective (ℓ.comp C) := by
  intro hCR hW ℓ hℓ
  obtain ⟨z, hz⟩ := hℓ 1
  let f : W →ₗ[k] k := ℓ.comp C
  let v : W := n⁻¹ • R z
  have hv : f v = 1 := by
    change ℓ (C (n⁻¹ • R z)) = 1
    rw [C.map_smul, hCR, ℓ.map_smul, ℓ.map_smul, hz]
    simp [hn]
  have hv0 : v ≠ 0 := by
    intro h
    have h01 : (0 : k) = 1 := by simpa only [h, map_zero] using hv
    exact zero_ne_one h01
  have hspan : ∀ w : W, ∃ a : k, a • v = w :=
    (finrank_eq_one_iff_of_nonzero' v hv0).mp hW
  change Function.Bijective f
  constructor
  · intro w₁ w₂ h
    obtain ⟨a, rfl⟩ := hspan w₁
    obtain ⟨b, rfl⟩ := hspan w₂
    have hab : a = b := by
      simpa only [map_smul, hv, smul_eq_mul, mul_one] using h
    rw [hab]
  · intro a
    exact ⟨a • v, by simp only [map_smul, hv, smul_eq_mul, mul_one]⟩
theorem Submission.p08_7d1ff633a4_normal_refinement :
    ∀ {ι : Type} [Finite ι] (F : ι → IntermediateField ℚ (AlgebraicClosure ℚ)),
      (∀ i, FiniteDimensional ℚ (F i)) →
      ∃ E : IntermediateField ℚ (AlgebraicClosure ℚ),
        FiniteDimensional ℚ E ∧ Normal ℚ E ∧ (∀ i, F i ≤ E) ∧
          E.fixingSubgroup.Normal ∧ E.fixingSubgroup.FiniteIndex := by
  intro ι _ F hF
  let : ∀ i, FiniteDimensional ℚ (F i) := hF
  have : IsAlgClosure ℚ (AlgebraicClosure ℚ) :=
    ⟨AlgebraicClosure.isAlgClosed ℚ, AlgebraicClosure.isAlgebraic ℚ⟩
  have : Normal ℚ (AlgebraicClosure ℚ) := IsAlgClosure.normal ℚ _
  let K : IntermediateField ℚ (AlgebraicClosure ℚ) := iSup F
  let E := IntermediateField.normalClosure ℚ K (AlgebraicClosure ℚ)
  have : FiniteDimensional ℚ K :=
    IntermediateField.finiteDimensional_iSup_of_finite
  have : FiniteDimensional ℚ E := normalClosure.is_finiteDimensional ℚ K _
  have : Normal ℚ E := normalClosure.normal ℚ K _
  refine ⟨E, inferInstance, inferInstance, ?_, ?_, ?_⟩
  · intro i
    exact (le_iSup F i).trans (IntermediateField.le_normalClosure K)
  · rw [← IntermediateField.restrictNormalHom_ker E]
    infer_instance
  · rw [← IntermediateField.restrictNormalHom_ker E]
    infer_instance
theorem Submission.p08_7d1ff633a4_ck_cyclotomic_kernel :
    ∀ {p : ℕ} [Fact p.Prime],
      ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
          σ ∈ F.fixingSubgroup → ExtCitation.cycloChar p σ = 1 := by
  classical
  intro p hp
  let : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  let R : Set (AlgebraicClosure ℚ) :=
    Set.range (fun t : rootsOfUnity p (AlgebraicClosure ℚ) =>
      ((t : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ))
  have : Finite R := (Set.finite_range _).to_subtype
  refine ⟨IntermediateField.adjoin ℚ R,
    IntermediateField.finiteDimensional_adjoin ?_, ?_⟩
  · rintro x ⟨t, rfl⟩
    refine ⟨Polynomial.X ^ p - 1, ?_, ?_⟩
    · simpa only [Polynomial.C_1] using
        Polynomial.monic_X_pow_sub_C (1 : ℚ) (NeZero.ne p)
    · simpa only [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
        Polynomial.eval₂_one, sub_eq_zero] using
        (mem_rootsOfUnity' p (t : (AlgebraicClosure ℚ)ˣ)).mp t.property
  intro σ hσ
  apply Units.ext
  change (modularCyclotomicCharacter (AlgebraicClosure ℚ)
    (ExtCitation.card_rootsOfUnity_eq_self p) σ : ZMod p) = 1
  symm
  apply modularCyclotomicCharacter.unique
  intro t ht
  change σ (t : AlgebraicClosure ℚ) = (t : AlgebraicClosure ℚ) ^ (1 : ZMod p).val
  have htF : (t : AlgebraicClosure ℚ) ∈ IntermediateField.adjoin ℚ R :=
    IntermediateField.subset_adjoin ℚ R ⟨⟨t, ht⟩, rfl⟩
  simpa only [ZMod.val_one'' (Fact.out : p.Prime).ne_one, pow_one] using
    ((IntermediateField.mem_fixingSubgroup_iff _ σ).mp hσ) (t : AlgebraicClosure ℚ) htF
theorem Submission.p08_7d1ff633a4_ck_uniform_stabilizer :
    ∀ {k G : Type} [Field k] [Group G]
      (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
      (M : Rep.{0} k G) [FiniteDimensional k M],
      (∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ),
        FiniteDimensional ℚ F ∧
        ∀ g : G, r g ∈ F.fixingSubgroup → M.ρ g m = m) →
      ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
        ∀ g : G, r g ∈ F.fixingSubgroup → ∀ m : M, M.ρ g m = m := by
  classical
  intro k G _ _ r M _ h
  let b : Basis (Fin (finrank k M)) k M := Module.finBasis k M
  choose F hF hfix using fun i => h (b i)
  let : ∀ i, FiniteDimensional ℚ (F i) := hF
  refine ⟨⨆ i, F i, inferInstance, ?_⟩
  intro g hg m
  have hρ : M.ρ g = LinearMap.id := b.ext fun i =>
    hfix i g (IntermediateField.fixingSubgroup_le (le_iSup F i) hg)
  exact LinearMap.congr_fun hρ m


theorem Submission.p08_7d1ff633a4_tt26_normal_kernel :
    ∀ {G : Type} [Group G]
      (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
      (E : IntermediateField ℚ (AlgebraicClosure ℚ)),
      FiniteDimensional ℚ E → Normal ℚ E →
        (E.fixingSubgroup.comap r).Normal ∧ (E.fixingSubgroup.comap r).FiniteIndex := by
  intro G _ r E hE hN
  have : FiniteDimensional ℚ E := hE
  have hker := @IntermediateField.restrictNormalHom_ker ℚ (AlgebraicClosure ℚ) _ _ _ E hN
  rw [← hker, MonoidHom.comap_ker]
  exact ⟨inferInstance, inferInstance⟩

theorem Submission.p08_7d1ff633a4_tt26_theta_from_pairings :
    ∀ {k G : Type} [Field k] [Group G] (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (A B N : Rep.{0} k G) (φ : A →ₗ[k] B →ₗ[k] N), let X : Fin 3 → ModuleCat k := ![ModuleCat.of k A.ρ.invariants, ModuleCat.of k (groupCohomology.continuousH1 r A), ModuleCat.of k (groupCohomology.continuousH2 r A)]; let Y : Fin 3 → ModuleCat k := ![ModuleCat.of k (groupCohomology.continuousH2 r B), ModuleCat.of k (groupCohomology.continuousH1 r B), ModuleCat.of k B.ρ.invariants]; ∀ (P : ∀ i : Fin 3, X i →ₗ[k] Y i →ₗ[k] groupCohomology.continuousH2 r N), ((∀ (m : A.ρ.invariants) (z : groupCohomology.levelCocycles₂ r B), ∃ e : groupCohomology.levelCocycles₂ r N, (∀ st : G × G, (e : G × G → N) st = φ (m : A) ((z : G × G → B) st)) ∧ P 0 m (groupCohomology.continuousH2π r B z) = groupCohomology.continuousH2π r N e) ∧ (∀ (f : groupCohomology.cocycles₁ A) (hf : groupCohomology.IsLevelConstant₁ r (⇑f)) (g : groupCohomology.cocycles₁ B) (hg : groupCohomology.IsLevelConstant₁ r (⇑g)), ∃ e : groupCohomology.levelCocycles₂ r N, (∀ st : G × G, (e : G × G → N) st = groupCohomology.cupCochain φ (⇑f) (⇑g) st) ∧ P 1 ⟨(groupCohomology.H1π A).hom f, groupCohomology.H1π_mem_continuousH1 r A hf⟩ ⟨(groupCohomology.H1π B).hom g, groupCohomology.H1π_mem_continuousH1 r B hg⟩ = groupCohomology.continuousH2π r N e) ∧ (∀ (z : groupCohomology.levelCocycles₂ r A) (d : B.ρ.invariants), ∃ e : groupCohomology.levelCocycles₂ r N, (∀ st : G × G, (e : G × G → N) st = φ ((z : G × G → A) st) (d : B)) ∧ P 2 (groupCohomology.continuousH2π r A z) d = groupCohomology.continuousH2π r N e)) → ∀ ℓ : groupCohomology.continuousH2 r N →ₗ[k] k, ∃ Θ : ∀ i : Fin 3, X i →ₗ[k] Module.Dual k (Y i), (groupCohomology.IsTheta0 r φ ℓ (Θ 0) ∧ groupCohomology.IsTheta1 r φ ℓ (Θ 1) ∧ groupCohomology.IsTheta2 r φ ℓ (Θ 2)) ∧ (∀ (i : Fin 3) (x : X i) (y : Y i), Θ i x y = ℓ (P i x y)) ∧ (∀ Ψ : ∀ i : Fin 3, X i →ₗ[k] Module.Dual k (Y i), (groupCohomology.IsTheta0 r φ ℓ (Ψ 0) ∧ groupCohomology.IsTheta1 r φ ℓ (Ψ 1) ∧ groupCohomology.IsTheta2 r φ ℓ (Ψ 2)) → ∀ i : Fin 3, Ψ i = Θ i) := by
  intro k G _ _ r A B N φ X Y P hP ℓ
  rcases hP with ⟨hP0, hP1, hP2⟩
  let Θ : ∀ i : Fin 3, X i →ₗ[k] Module.Dual k (Y i) := fun i =>
    { toFun := fun x => ℓ.comp (P i x)
      map_add' := by
        intro x x'
        ext y
        change ℓ (P i (x + x') y) = ℓ (P i x y) + ℓ (P i x' y)
        rw [map_add, LinearMap.add_apply, map_add]
      map_smul' := by
        intro c x
        ext y
        change ℓ (P i (c • x) y) = c • ℓ (P i x y)
        rw [map_smul, LinearMap.smul_apply, map_smul] }
  refine ⟨Θ, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro m z e he
    obtain ⟨e', he', hP⟩ := hP0 m z
    have heq : e' = e := Subtype.ext (funext fun st => (he' st).trans (he st).symm)
    subst e'
    change ℓ (P 0 m (continuousH2π r B z)) = ℓ (continuousH2π r N e)
    exact congrArg ℓ hP
  · intro f hf g hg e he
    obtain ⟨e', he', hP⟩ := hP1 f hf g hg
    have heq : e' = e := Subtype.ext (funext fun st => (he' st).trans (he st).symm)
    subst e'
    change ℓ (P 1 ⟨(H1π A).hom f, H1π_mem_continuousH1 r A hf⟩
      ⟨(H1π B).hom g, H1π_mem_continuousH1 r B hg⟩) = ℓ (continuousH2π r N e)
    exact congrArg ℓ hP
  · intro z d e he
    obtain ⟨e', he', hP⟩ := hP2 z d
    have heq : e' = e := Subtype.ext (funext fun st => (he' st).trans (he st).symm)
    subst e'
    change ℓ (P 2 (continuousH2π r A z) d) = ℓ (continuousH2π r N e)
    exact congrArg ℓ hP
  · intro i x y
    rfl
  · intro Ψ hΨ i
    rcases hΨ with ⟨hΨ0, hΨ1, hΨ2⟩
    fin_cases i
    · apply LinearMap.ext
      intro x
      apply LinearMap.ext
      intro y
      change Ψ 0 x y = ℓ (P 0 x y)
      obtain ⟨z, rfl⟩ :=
        (show Function.Surjective (continuousH2π r B) from Submodule.mkQ_surjective _) y
      obtain ⟨e, he, hP⟩ := hP0 x z
      exact (hΨ0 x z e he).trans (congrArg ℓ hP).symm
    · apply LinearMap.ext
      intro x
      apply LinearMap.ext
      intro y
      change Ψ 1 x y = ℓ (P 1 x y)
      obtain ⟨f, hf, hfx⟩ := (mem_continuousH1_iff r A x.val).mp x.property
      obtain ⟨g, hg, hgy⟩ := (mem_continuousH1_iff r B y.val).mp y.property
      have hx : (⟨(H1π A).hom f, H1π_mem_continuousH1 r A hf⟩ : continuousH1 r A) = x :=
        Subtype.ext hfx
      have hy : (⟨(H1π B).hom g, H1π_mem_continuousH1 r B hg⟩ : continuousH1 r B) = y :=
        Subtype.ext hgy
      rw [← hx, ← hy]
      obtain ⟨e, he, hP⟩ := hP1 f hf g hg
      exact (hΨ1 f hf g hg e he).trans (congrArg ℓ hP).symm
    · apply LinearMap.ext
      intro x
      apply LinearMap.ext
      intro y
      change Ψ 2 x y = ℓ (P 2 x y)
      obtain ⟨z, rfl⟩ :=
        (show Function.Surjective (continuousH2π r A) from Submodule.mkQ_surjective _) x
      obtain ⟨e, he, hP⟩ := hP2 z y
      exact (hΨ2 z y e he).trans (congrArg ℓ hP).symm

namespace Submission

theorem p08_7d1ff633a4_common_kernel
    {p : ℕ} [Fact p.Prime] (q : Nat.Primes)
    (S : Subgroup (ExtCitation.primeLocalGaloisGroup q)) (U : Subgroup S)
    (M : Rep.{0} (ZMod p) S) [FiniteDimensional (ZMod p) M]
    (hU : ∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧
      F₀.fixingSubgroup.comap ((ExtCitation.primeLocalToGlobal q).comp S.subtype) ≤ U)
    (hsm : ∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ),
      FiniteDimensional ℚ F ∧ ∀ s : S,
        ((ExtCitation.primeLocalToGlobal q).comp S.subtype) s ∈ F.fixingSubgroup →
          M.ρ s m = m) :
    ∃ E : IntermediateField ℚ (AlgebraicClosure ℚ),
      FiniteDimensional ℚ E ∧ Normal ℚ E ∧
      E.fixingSubgroup.comap ((ExtCitation.primeLocalToGlobal q).comp S.subtype) ≤ U ∧
      (∀ s : S, ((ExtCitation.primeLocalToGlobal q).comp S.subtype) s ∈ E.fixingSubgroup →
        (∀ m : M, M.ρ s m = m) ∧
        (∀ d : M.dualTwist
            (((ExtCitation.cycloChar p).comp (ExtCitation.primeLocalToGlobal q)).comp S.subtype),
          (M.dualTwist
            (((ExtCitation.cycloChar p).comp (ExtCitation.primeLocalToGlobal q)).comp S.subtype)).ρ
              s d = d) ∧
        (∀ a : Rep.res S.subtype
            (groupCohomology.ofChar (k := ZMod p)
              ((ExtCitation.cycloChar p).comp (ExtCitation.primeLocalToGlobal q))),
          (Rep.res S.subtype
            (groupCohomology.ofChar (k := ZMod p)
              ((ExtCitation.cycloChar p).comp (ExtCitation.primeLocalToGlobal q)))).ρ s a = a)) := by
  obtain ⟨F₀, hF₀, hF₀U⟩ := hU
  obtain ⟨FM, hFM, hFMfix⟩ :=
    p08_7d1ff633a4_ck_uniform_stabilizer
      ((ExtCitation.primeLocalToGlobal q).comp S.subtype) M hsm
  obtain ⟨FC, hFC, hFCfix⟩ := p08_7d1ff633a4_ck_cyclotomic_kernel (p := p)
  have hfinite : ∀ i : Fin 3, FiniteDimensional ℚ (![F₀, FM, FC] i) := by
    intro i
    fin_cases i
    · exact hF₀
    · exact hFM
    · exact hFC
  obtain ⟨E, hE, hEnormal, hFE, _, _⟩ :=
    p08_7d1ff633a4_normal_refinement ![F₀, FM, FC] hfinite
  have hMfix : ∀ s : S,
      ((ExtCitation.primeLocalToGlobal q).comp S.subtype) s ∈ E.fixingSubgroup →
        ∀ m : M, M.ρ s m = m := by
    intro s hs
    exact hFMfix s (IntermediateField.fixingSubgroup_le (hFE 1) hs)
  refine ⟨E, hE, hEnormal, ?_, ?_⟩
  · intro s hs
    exact hF₀U (IntermediateField.fixingSubgroup_le (hFE 0) hs)
  · intro s hs
    have hχ : (((ExtCitation.cycloChar p).comp
        (ExtCitation.primeLocalToGlobal q)).comp S.subtype) s = 1 :=
      hFCfix _ (IntermediateField.fixingSubgroup_le (hFE 2) hs)
    have hinv : ((ExtCitation.primeLocalToGlobal q).comp S.subtype) s⁻¹ ∈
        E.fixingSubgroup := by
      rw [map_inv]
      exact E.fixingSubgroup.inv_mem hs
    refine ⟨hMfix s hs, ?_, ?_⟩
    · intro d
      rw [Rep.dualTwist_ρ_apply, hχ, Units.val_one, one_smul]
      ext m
      exact congrArg d (hMfix s⁻¹ hinv m)
    · intro a
      change (((((ExtCitation.cycloChar p).comp
        (ExtCitation.primeLocalToGlobal q)).comp S.subtype) s : ZMod p) • a) = a
      rw [hχ, Units.val_one, one_smul]

end Submission
theorem Submission.p08_7d1ff633a4_tp26_low_degree_prism :
    ∀ {X V : Type} [AddCommGroup V] (α β : X → X),
      (∀ F : X → X → V,
        (∀ x y z : X, F y z - F x z + F x y = 0) →
        ∀ x y : X, F (β x) (β y) - F (α x) (α y) =
          F (α y) (β y) - F (α x) (β x)) ∧
      (∀ F : X → X → X → V,
        (∀ w x y z : X, F x y z - F w y z + F w x z - F w x y = 0) →
        let h : X → X → V := fun x y =>
          F (α x) (β x) (β y) - F (α x) (α y) (β y)
        ∀ x y z : X, F (β x) (β y) (β z) - F (α x) (α y) (α z) =
          h y z - h x z + h x y) := by
  intro X V _ α β
  constructor
  · intro F hF x y
    apply sub_eq_zero.mp
    calc
      _ = (F (β x) (β y) - F (α x) (β y) + F (α x) (β x)) -
          (F (α y) (β y) - F (α x) (β y) + F (α x) (α y)) := by abel
      _ = 0 := by simp only [hF, sub_self]
  · intro F hF
    dsimp only
    intro x y z
    apply sub_eq_zero.mp
    calc
      _ = (F (β x) (β y) (β z) - F (α x) (β y) (β z) +
            F (α x) (β x) (β z) - F (α x) (β x) (β y)) -
          (F (α y) (β y) (β z) - F (α x) (β y) (β z) +
            F (α x) (α y) (β z) - F (α x) (α y) (β y)) +
          (F (α y) (α z) (β z) - F (α x) (α z) (β z) +
            F (α x) (α y) (β z) - F (α x) (α y) (α z)) := by abel
      _ = 0 := by simp only [hF, sub_self, add_zero]
theorem Submission.p08_7d1ff633a4_tp26_bilinear_averaging :
    ∀ {k G X Y ι : Type} [Field k] [Group G] [MulAction G X] [MulAction G Y] [Fintype ι] (A B N : Rep.{0} k G) (φ : A →ₗ[k] B →ₗ[k] N), (∀ (s : G) (a : A) (b : B), φ (A.ρ s a) (B.ρ s b) = N.ρ s (φ a b)) → ∀ (t : ι → G) (F : X → A) (Q : Y → B), ((∀ (s : G) (x : X), F (s • x) = A.ρ s (F x)) → ∀ (x : X) (y : Y), (∑ c : ι, N.ρ (t c) (φ (F ((t c)⁻¹ • x)) (Q ((t c)⁻¹ • y)))) = φ (F x) (∑ c : ι, B.ρ (t c) (Q ((t c)⁻¹ • y)))) ∧ ((∀ (s : G) (y : Y), Q (s • y) = B.ρ s (Q y)) → ∀ (x : X) (y : Y), (∑ c : ι, N.ρ (t c) (φ (F ((t c)⁻¹ • x)) (Q ((t c)⁻¹ • y)))) = φ (∑ c : ι, A.ρ (t c) (F ((t c)⁻¹ • x))) (Q y)) := by
  intro k G X Y ι _ _ _ _ _ A B N φ hφ t F Q
  constructor
  · intro hF x y
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro c _
    rw [← hφ, ← hF, smul_inv_smul]
  · intro hQ x y
    rw [map_sum, LinearMap.sum_apply]
    apply Finset.sum_congr rfl
    intro c _
    rw [← hφ, ← hQ, smul_inv_smul]
theorem Submission.p08_7d1ff633a4_tp26_normal_level_retraction :
    ∀ {G : Type} [Group G] (H : Subgroup G), ∃ a : G → H,
      (∀ h : H, a (h : G) = h) ∧
      (∀ (h : H) (g : G), a ((h : G) * g) = h * a g) ∧
      (∀ K : Subgroup G, K.Normal → K ≤ H → ∀ g u : G, u ∈ K →
        (a g : G)⁻¹ * (a (g * u) : G) ∈ K) := by
  classical
  intro G _ H
  let q : G → Quotient (QuotientGroup.rightRel H) := Quotient.mk _
  let t : Quotient (QuotientGroup.rightRel H) → G :=
    fun c => if c = q 1 then 1 else c.out
  have ht (c : Quotient (QuotientGroup.rightRel H)) : q (t c) = c := by
    by_cases hc : c = q 1
    · change q (if c = q 1 then 1 else c.out) = c
      rw [if_pos hc]
      exact hc.symm
    · simpa only [t, if_neg hc] using c.out_eq
  let a : G → H := fun g =>
    ⟨g * (t (q g))⁻¹, QuotientGroup.rightRel_apply.mp (Quotient.exact (ht (q g)))⟩
  have hq (h : H) (g : G) : q ((h : G) * g) = q g := by
    symm
    apply Quotient.sound
    apply QuotientGroup.rightRel_apply.mpr
    simpa only [mul_inv_cancel_right] using h.property
  have ha (h : H) (g : G) : a ((h : G) * g) = h * a g := by
    apply Subtype.ext
    change ((h : G) * g) * (t (q ((h : G) * g)))⁻¹ =
      (h : G) * (g * (t (q g))⁻¹)
    rw [hq, mul_assoc]
  have ha1 : a 1 = 1 := by
    apply Subtype.ext
    simp [a, t]
  refine ⟨a, ?_, ha, ?_⟩
  · intro h
    simpa only [mul_one, ha1] using ha h 1
  · intro K hK hKH g u hu
    have hqu : q (g * u) = q g := by
      symm
      apply Quotient.sound
      apply QuotientGroup.rightRel_apply.mpr
      exact hKH (hK.conj_mem u hu g)
    have heq : (a g : G)⁻¹ * (a (g * u) : G) =
        t (q g) * u * (t (q g))⁻¹ := by
      change (g * (t (q g))⁻¹)⁻¹ * ((g * u) * (t (q (g * u)))⁻¹) = _
      rw [hqu]
      group
    rw [heq]
    exact hK.conj_mem u hu (t (q g))

theorem Submission.p08_7d1ff633a4_tp26_coset_averaging :
    ∀ {k G X : Type} [Field k] [Group G] [MulAction G X]
      (H : Subgroup G) [Fintype (G ⧸ H)] (V : Rep.{0} k G) (t : (G ⧸ H) → G),
      (∀ c : G ⧸ H, (t c : G ⧸ H) = c) →
      ∃ T : (X → V) →ₗ[k] (X → V),
        (∀ (F : X → V) (x : X),
          T F x = ∑ c : G ⧸ H, V.ρ (t c) (F ((t c)⁻¹ • x))) ∧
        (∀ F : X → V,
          (∀ (h : H) (x : X), F ((h : G) • x) = V.ρ (h : G) (F x)) →
          ∀ (s : G) (x : X), T F (s • x) = V.ρ s (T F x)) ∧
        (∀ F : X → V,
          (∀ (s : G) (x : X), F (s • x) = V.ρ s (F x)) →
          ∀ x : X, T F x = (H.index : k) • F x) ∧
        (∀ u : (G ⧸ H) → G, (∀ c : G ⧸ H, (u c : G ⧸ H) = c) →
          ∀ F : X → V,
          (∀ (h : H) (x : X), F ((h : G) • x) = V.ρ (h : G) (F x)) →
          ∀ x : X, T F x = ∑ c : G ⧸ H, V.ρ (u c) (F ((u c)⁻¹ • x))) := by
  classical
  intro k G X _ _ _ H _ V t ht
  let T : (X → V) →ₗ[k] (X → V) :=
    { toFun := fun F x => ∑ c : G ⧸ H, V.ρ (t c) (F ((t c)⁻¹ • x))
      map_add' := by
        intro F F'
        funext x
        simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]
      map_smul' := by
        intro b F
        funext x
        simp only [Pi.smul_apply, map_smul, Finset.smul_sum, RingHom.id_apply] }
  have hrep (F : X → V)
      (hF : ∀ (h : H) (x : X), F ((h : G) • x) = V.ρ (h : G) (F x))
      (a b : G) (hab : (a : G ⧸ H) = (b : G ⧸ H)) (x : X) :
      V.ρ a (F (a⁻¹ • x)) = V.ρ b (F (b⁻¹ • x)) := by
    let h : H := ⟨a⁻¹ * b, QuotientGroup.eq.mp hab⟩
    have hb : b = a * (h : G) := by simp [h]
    rw [hb, mul_inv_rev, mul_smul]
    rw [← Subgroup.coe_inv, hF h⁻¹]
    simp only [Subgroup.coe_inv, map_mul, Module.End.mul_apply,
      Representation.self_inv_apply]
  refine ⟨T, fun _ _ => rfl, ?_, ?_, ?_⟩
  · intro F hF s x
    change (∑ c : G ⧸ H, V.ρ (t c) (F ((t c)⁻¹ • (s • x)))) =
      V.ρ s (∑ c : G ⧸ H, V.ρ (t c) (F ((t c)⁻¹ • x)))
    calc
      _ = ∑ c : G ⧸ H, V.ρ (t (s • c)) (F ((t (s • c))⁻¹ • (s • x))) :=
        (Equiv.sum_comp (MulAction.toPerm s) _).symm
      _ = ∑ c : G ⧸ H, V.ρ s (V.ρ (t c) (F ((t c)⁻¹ • x))) := by
        apply Finset.sum_congr rfl
        intro c _
        have hc : (t (s • c) : G ⧸ H) = ((s * t c : G) : G ⧸ H) := by
          exact (ht (s • c)).trans
            (congrArg (fun d : G ⧸ H => s • d) (ht c).symm)
        rw [hrep F hF _ _ hc]
        simp only [mul_inv_rev, mul_smul, inv_smul_smul, map_mul, Module.End.mul_apply]
      _ = _ := (map_sum (V.ρ s) _ _).symm
  · intro F hF x
    change (∑ c : G ⧸ H, V.ρ (t c) (F ((t c)⁻¹ • x))) = _
    have hc (c : G ⧸ H) : V.ρ (t c) (F ((t c)⁻¹ • x)) = F x := by
      rw [← hF, smul_inv_smul]
    simp only [hc, Finset.sum_const, Finset.card_univ]
    rw [Subgroup.index_eq_card, Nat.card_eq_fintype_card, Nat.cast_smul_eq_nsmul]
  · intro u hu F hF x
    change (∑ c : G ⧸ H, V.ρ (t c) (F ((t c)⁻¹ • x))) = _
    apply Finset.sum_congr rfl
    intro c _
    exact hrep F hF (t c) (u c) ((ht c).trans (hu c).symm) x
/-- Finite-index transfer and both projection formulas on the frozen carriers. -/
theorem Submission.p08_7d1ff633a4_tt26_transfer_projection :
    ∀ {k G : Type} [Field k] [Group G] (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (H : Subgroup G) [H.FiniteIndex] (A B N : Rep.{0} k G) (E₀ : IntermediateField ℚ (AlgebraicClosure ℚ)), FiniteDimensional ℚ E₀ → Normal ℚ E₀ → E₀.fixingSubgroup.comap r ≤ H → (∀ g : G, r g ∈ E₀.fixingSubgroup → ∀ a : A, A.ρ g a = a) → (∀ g : G, r g ∈ E₀.fixingSubgroup → ∀ b : B, B.ρ g b = b) → (∀ g : G, r g ∈ E₀.fixingSubgroup → ∀ z : N, N.ρ g z = z) → ∀ φ : A →ₗ[k] B →ₗ[k] N, (∀ (g : G) (a : A) (b : B), φ (A.ρ g a) (B.ρ g b) = N.ρ g (φ a b)) → let rH := r.comp H.subtype; let AH := Rep.res H.subtype A; let BH := Rep.res H.subtype B; let NH := Rep.res H.subtype N; let φH : AH →ₗ[k] BH →ₗ[k] NH := φ; let X : Fin 3 → ModuleCat k := ![ModuleCat.of k A.ρ.invariants, ModuleCat.of k (groupCohomology.continuousH1 r A), ModuleCat.of k (groupCohomology.continuousH2 r A)]; let Y : Fin 3 → ModuleCat k := ![ModuleCat.of k (groupCohomology.continuousH2 r B), ModuleCat.of k (groupCohomology.continuousH1 r B), ModuleCat.of k B.ρ.invariants]; let XH : Fin 3 → ModuleCat k := ![ModuleCat.of k AH.ρ.invariants, ModuleCat.of k (groupCohomology.continuousH1 rH AH), ModuleCat.of k (groupCohomology.continuousH2 rH AH)]; let YH : Fin 3 → ModuleCat k := ![ModuleCat.of k (groupCohomology.continuousH2 rH BH), ModuleCat.of k (groupCohomology.continuousH1 rH BH), ModuleCat.of k BH.ρ.invariants]; ∀ (P : ∀ i : Fin 3, X i →ₗ[k] Y i →ₗ[k] groupCohomology.continuousH2 r N) (PH : ∀ i : Fin 3, XH i →ₗ[k] YH i →ₗ[k] groupCohomology.continuousH2 rH NH), ((∀ (m : A.ρ.invariants) (z : groupCohomology.levelCocycles₂ r B), ∃ e : groupCohomology.levelCocycles₂ r N, (∀ st : G × G, (e : G × G → N) st = φ (m : A) ((z : G × G → B) st)) ∧ P 0 m (groupCohomology.continuousH2π r B z) = groupCohomology.continuousH2π r N e) ∧ (∀ (f : groupCohomology.cocycles₁ A) (hf : groupCohomology.IsLevelConstant₁ r (⇑f)) (g : groupCohomology.cocycles₁ B) (hg : groupCohomology.IsLevelConstant₁ r (⇑g)), ∃ e : groupCohomology.levelCocycles₂ r N, (∀ st : G × G, (e : G × G → N) st = groupCohomology.cupCochain φ (⇑f) (⇑g) st) ∧ P 1 ⟨(groupCohomology.H1π A).hom f, groupCohomology.H1π_mem_continuousH1 r A hf⟩ ⟨(groupCohomology.H1π B).hom g, groupCohomology.H1π_mem_continuousH1 r B hg⟩ = groupCohomology.continuousH2π r N e) ∧ (∀ (z : groupCohomology.levelCocycles₂ r A) (d : B.ρ.invariants), ∃ e : groupCohomology.levelCocycles₂ r N, (∀ st : G × G, (e : G × G → N) st = φ ((z : G × G → A) st) (d : B)) ∧ P 2 (groupCohomology.continuousH2π r A z) d = groupCohomology.continuousH2π r N e)) → ((∀ (m : AH.ρ.invariants) (z : groupCohomology.levelCocycles₂ rH BH), ∃ e : groupCohomology.levelCocycles₂ rH NH, (∀ st : H × H, (e : H × H → NH) st = φH (m : AH) ((z : H × H → BH) st)) ∧ PH 0 m (groupCohomology.continuousH2π rH BH z) = groupCohomology.continuousH2π rH NH e) ∧ (∀ (f : groupCohomology.cocycles₁ AH) (hf : groupCohomology.IsLevelConstant₁ rH (⇑f)) (g : groupCohomology.cocycles₁ BH) (hg : groupCohomology.IsLevelConstant₁ rH (⇑g)), ∃ e : groupCohomology.levelCocycles₂ rH NH, (∀ st : H × H, (e : H × H → NH) st = groupCohomology.cupCochain φH (⇑f) (⇑g) st) ∧ PH 1 ⟨(groupCohomology.H1π AH).hom f, groupCohomology.H1π_mem_continuousH1 rH AH hf⟩ ⟨(groupCohomology.H1π BH).hom g, groupCohomology.H1π_mem_continuousH1 rH BH hg⟩ = groupCohomology.continuousH2π rH NH e) ∧ (∀ (z : groupCohomology.levelCocycles₂ rH AH) (d : BH.ρ.invariants), ∃ e : groupCohomology.levelCocycles₂ rH NH, (∀ st : H × H, (e : H × H → NH) st = φH ((z : H × H → AH) st) (d : BH)) ∧ PH 2 (groupCohomology.continuousH2π rH AH z) d = groupCohomology.continuousH2π rH NH e)) → ∃ (RX : ∀ i : Fin 3, X i →ₗ[k] XH i) (CX : ∀ i : Fin 3, XH i →ₗ[k] X i) (RY : ∀ i : Fin 3, Y i →ₗ[k] YH i) (CY : ∀ i : Fin 3, YH i →ₗ[k] Y i) (RN : groupCohomology.continuousH2 r N →ₗ[k] groupCohomology.continuousH2 rH NH) (CN : groupCohomology.continuousH2 rH NH →ₗ[k] groupCohomology.continuousH2 r N), (∀ (i : Fin 3) (x : X i), CX i (RX i x) = (H.index : k) • x) ∧ (∀ (i : Fin 3) (y : Y i), CY i (RY i y) = (H.index : k) • y) ∧ (∀ z : groupCohomology.continuousH2 r N, CN (RN z) = (H.index : k) • z) ∧ (∀ (i : Fin 3) (x : X i) (y : YH i), CN (PH i (RX i x) y) = P i x (CY i y)) ∧ (∀ (i : Fin 3) (x : XH i) (y : Y i), CN (PH i x (RY i y)) = P i (CX i x) y) := by
  classical
  intro k G _ _ r H _ A B N E₀ hE₀ hNormal₀ hKH hA hB hN φ hφ
    rH AH BH NH φH X Y XH YH P PH hP hPH
  -- In zero index characteristic, the six zero maps satisfy the exact conclusion.
  by_cases hindex : (H.index : k) = 0
  · refine ⟨0, 0, 0, 0, 0, 0, ?_⟩
    simp [hindex]
  -- Fix the same retraction and left-coset representatives in every degree.
  obtain ⟨a, haH, haEq, haLevel⟩ :=
    Submission.p08_7d1ff633a4_tp26_normal_level_retraction H
  let : Fintype (G ⧸ H) := Fintype.ofFinite _
  let t : (G ⧸ H) → G := Quotient.out
  have ht : ∀ c : G ⧸ H, (t c : G ⧸ H) = c := Quotient.out_eq
  have hρ : ∀ (V : Rep.{0} k G) (s u : G) (v : V),
      V.ρ s (V.ρ u v) = V.ρ (s * u) v := by
    intro V s u v
    rw [Rep.ρ_mul]
    rfl
  -- A finite family of witness fields has a common normal level containing E₀.
  have commonLevel : ∀ (F : IntermediateField ℚ (AlgebraicClosure ℚ)),
      FiniteDimensional ℚ F →
      ∃ E : IntermediateField ℚ (AlgebraicClosure ℚ),
        FiniteDimensional ℚ E ∧ Normal ℚ E ∧ E₀ ≤ E ∧ F ≤ E ∧
        (E.fixingSubgroup.comap r).Normal ∧
        (E.fixingSubgroup.comap r).FiniteIndex ∧ E.fixingSubgroup.comap r ≤ H := by
    intro F hF
    obtain ⟨E, hE, hnE, hle, _, _⟩ :=
      Submission.p08_7d1ff633a4_normal_refinement (fun b : Bool => if b then E₀ else F)
        (by intro b; cases b; exact hF; exact hE₀)
    have h₀ : E₀ ≤ E := by simpa using hle true
    have hF' : F ≤ E := by simpa using hle false
    obtain ⟨hKn, hKf⟩ := Submission.p08_7d1ff633a4_tt26_normal_kernel r E hE hnE
    refine ⟨E, hE, hnE, h₀, hF', hKn, hKf, ?_⟩
    intro g hg
    exact hKH (IntermediateField.fixingSubgroup_antitone h₀ hg)
  -- Restriction in degree zero uses the original underlying coefficient module.
  let R₀ (V : Rep.{0} k G) : V.ρ.invariants →ₗ[k] (Rep.res H.subtype V).ρ.invariants :=
    { toFun := fun v => ⟨v, fun h => v.property (h : G)⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  -- Restriction on the frozen H² quotient is already supplied by the pinned library.
  let R₂ (V : Rep.{0} k G) : continuousH2 r V →ₗ[k]
      continuousH2 rH (Rep.res H.subtype V) :=
    continuousH2Map H.subtype (fun _ => rfl) (LinearMap.id : V →ₗ[k] V)
      (fun _ _ => rfl)
  -- Homogeneous cocycles, used for the retraction/prism argument.
  let hom₁ (V : Rep.{0} k G) (f : G → V) : G → G → V :=
    fun x y => V.ρ x (f (x⁻¹ * y))
  let hom₂ (V : Rep.{0} k G) (z : G × G → V) : G → G → G → V :=
    fun x y w => V.ρ x (z (x⁻¹ * y, y⁻¹ * w))
  have hom₁_eq : ∀ (V : Rep.{0} k G) (f : G → V) (s x y : G),
      hom₁ V f (s * x) (s * y) = V.ρ s (hom₁ V f x y) := by
    intro V f s x y
    simp only [hom₁, mul_inv_rev, mul_assoc, inv_mul_cancel_left, hρ]
  have hom₂_eq : ∀ (V : Rep.{0} k G) (z : G × G → V) (s x y w : G),
      hom₂ V z (s * x) (s * y) (s * w) = V.ρ s (hom₂ V z x y w) := by
    intro V z s x y w
    simp only [hom₂, mul_inv_rev, mul_assoc, inv_mul_cancel_left, hρ]
  have hom₁_closed : ∀ (V : Rep.{0} k G) (f : cocycles₁ V) (x y z : G),
      hom₁ V f y z - hom₁ V f x z + hom₁ V f x y = 0 := by
    intro V f x y z
    have hc := congrArg (V.ρ x) ((mem_cocycles₁_def (⇑f)).mp f.property
      (x⁻¹ * y) (y⁻¹ * z))
    simpa only [hom₁, map_add, map_sub, map_zero, hρ, mul_assoc,
      inv_mul_cancel_left, mul_inv_cancel_left] using hc
  have hom₂_closed : ∀ (V : Rep.{0} k G) (z : cocycles₂ V) (w x y u : G),
      hom₂ V z x y u - hom₂ V z w y u + hom₂ V z w x u - hom₂ V z w x y = 0 := by
    intro V z w x y u
    have hc := congrArg (V.ρ w) ((mem_cocycles₂_def (⇑z)).mp z.property
      (w⁻¹ * x) (x⁻¹ * y) (y⁻¹ * u))
    simpa only [hom₂, map_add, map_sub, map_zero, hρ, mul_assoc,
      inv_mul_cancel_left, mul_inv_cancel_left] using hc
  -- The two exact child prism identities give the required explicit primitives.
  have prism₁ : ∀ (V : Rep.{0} k G) (f : cocycles₁ V) (x y : G),
      hom₁ V f x y - hom₁ V f (a x) (a y) =
        hom₁ V f (a y) y - hom₁ V f (a x) x := by
    intro V f
    exact (Submission.p08_7d1ff633a4_tp26_low_degree_prism
      (fun x : G => (a x : G)) id).1 (hom₁ V f) (hom₁_closed V f)
  have prism₂ : ∀ (V : Rep.{0} k G) (z : cocycles₂ V),
      let p : G → G → V := fun x y =>
        hom₂ V z (a x) x y - hom₂ V z (a x) (a y) y
      ∀ x y u : G, hom₂ V z x y u - hom₂ V z (a x) (a y) (a u) =
        p y u - p x u + p x y := by
    intro V z
    exact (Submission.p08_7d1ff633a4_tp26_low_degree_prism
      (fun x : G => (a x : G)) id).2 (hom₂ V z) (hom₂_closed V z)
  -- Use the same averaging operation for every coefficient and vertex domain.
  let avg (V : Rep.{0} k G) (D : Type) [MulAction G D] :
      (D → V) →ₗ[k] (D → V) :=
    Classical.choose (Submission.p08_7d1ff633a4_tp26_coset_averaging H V t ht)
  have avg_spec (V : Rep.{0} k G) (D : Type) [MulAction G D] :=
    Classical.choose_spec (Submission.p08_7d1ff633a4_tp26_coset_averaging
      (X := D) H V t ht)
  have avg_apply (V : Rep.{0} k G) (D : Type) [MulAction G D]
      (F : D → V) (x : D) :
      avg V D F x = ∑ c : G ⧸ H, V.ρ (t c) (F ((t c)⁻¹ • x)) :=
    (avg_spec V D).1 F x
  have avg_equivariant (V : Rep.{0} k G) (D : Type) [MulAction G D]
      (F : D → V) (hF : ∀ (h : H) (x : D), F ((h : G) • x) = V.ρ (h : G) (F x)) :
      ∀ (s : G) (x : D), avg V D F (s • x) = V.ρ s (avg V D F x) :=
    (avg_spec V D).2.1 F hF
  have avg_index (V : Rep.{0} k G) (D : Type) [MulAction G D]
      (F : D → V) (hF : ∀ (s : G) (x : D), F (s • x) = V.ρ s (F x)) :
      ∀ x : D, avg V D F x = (H.index : k) • F x :=
    (avg_spec V D).2.2.1 F hF
  have norm_invariant (V : Rep.{0} k G) (v : (Rep.res H.subtype V).ρ.invariants) :
      (∑ c : G ⧸ H, V.ρ (t c) (v : V)) ∈ V.ρ.invariants := by
    intro s
    have heq := avg_equivariant V G (fun _ => (v : V))
      (fun h _ => (v.property h).symm) s 1
    simpa only [avg_apply] using heq.symm
  let C₀ (V : Rep.{0} k G) : (Rep.res H.subtype V).ρ.invariants →ₗ[k] V.ρ.invariants :=
    { toFun := fun v => ⟨∑ c : G ⧸ H, V.ρ (t c) (v : V), norm_invariant V v⟩
      map_add' := by
        intro v w
        apply Subtype.ext
        simp only [Submodule.coe_add, map_add, Finset.sum_add_distrib]
      map_smul' := by
        intro c v
        apply Subtype.ext
        simp only [Submodule.coe_smul, map_smul, Finset.smul_sum, RingHom.id_apply] }
  have C₀_R₀ (V : Rep.{0} k G) (v : V.ρ.invariants) :
      C₀ V (R₀ V v) = (H.index : k) • v := by
    apply Subtype.ext
    have heq := avg_index V G (fun _ => (v : V)) (fun s _ => (v.property s).symm) 1
    change (∑ c : G ⧸ H, V.ρ (t c) (v : V)) = (H.index : k) • (v : V)
    simpa only [avg_apply] using heq
  -- Both projection identities already hold for arbitrary homogeneous cochains.
  have avg_product (D D' : Type) [MulAction G D] [MulAction G D']
      (F : D → A) (Q : D' → B) :=
    Submission.p08_7d1ff633a4_tp26_bilinear_averaging A B N φ hφ t F Q
  -- Coordinate pullback along a preserves the subgroup equivariance.
  let lift₁ (V : Rep.{0} k G) (f : H → Rep.res H.subtype V) : G × G → V :=
    fun xy => V.ρ (a xy.1) (f ((a xy.1)⁻¹ * a xy.2))
  let lift₂ (V : Rep.{0} k G) (z : H × H → Rep.res H.subtype V) : G × G × G → V :=
    fun xyz => V.ρ (a xyz.1) (z ((a xyz.1)⁻¹ * a xyz.2.1,
      (a xyz.2.1)⁻¹ * a xyz.2.2))
  have lift₁_eq (V : Rep.{0} k G) (f : H → Rep.res H.subtype V) (h : H) (xy : G × G) :
      lift₁ V f ((h : G) • xy) = V.ρ (h : G) (lift₁ V f xy) := by
    change V.ρ (a ((h : G) * xy.1))
      (f ((a ((h : G) * xy.1))⁻¹ * a ((h : G) * xy.2))) = _
    simp only [haEq, mul_inv_rev, mul_assoc, inv_mul_cancel_left]
    change V.ρ ((h : G) * (a xy.1 : G)) _ = _
    rw [← hρ]
  have lift₂_eq (V : Rep.{0} k G) (z : H × H → Rep.res H.subtype V)
      (h : H) (xyz : G × G × G) :
      lift₂ V z ((h : G) • xyz) = V.ρ (h : G) (lift₂ V z xyz) := by
    change V.ρ (a ((h : G) * xyz.1))
      (z ((a ((h : G) * xyz.1))⁻¹ * a ((h : G) * xyz.2.1),
        (a ((h : G) * xyz.2.1))⁻¹ * a ((h : G) * xyz.2.2))) = _
    simp only [haEq, mul_inv_rev, mul_assoc, inv_mul_cancel_left]
    change V.ρ ((h : G) * (a xyz.1 : G)) _ = _
    rw [← hρ]
  let transferCochain₁ (V : Rep.{0} k G) : (H → Rep.res H.subtype V) →ₗ[k] (G → V) :=
    { toFun := fun f s => avg V (G × G) (lift₁ V f) (1, s)
      map_add' := by
        intro f g
        ext s
        simp [avg_apply, lift₁, map_add, Finset.sum_add_distrib]
      map_smul' := by
        intro c f
        ext s
        simp [avg_apply, lift₁, map_smul, Finset.smul_sum] }
  let transferCochain₂ (V : Rep.{0} k G) :
      (H × H → Rep.res H.subtype V) →ₗ[k] (G × G → V) :=
    { toFun := fun z st => avg V (G × G × G) (lift₂ V z) (1, st.1, st.1 * st.2)
      map_add' := by
        intro z w
        ext st
        simp [avg_apply, lift₂, map_add, Finset.sum_add_distrib]
      map_smul' := by
        intro c z
        ext st
        simp [avg_apply, lift₂, map_smul, Finset.smul_sum] }
  -- The averaged pullbacks are closed whenever their inputs are closed.
  have lift₁_closed (V : Rep.{0} k G) (f : cocycles₁ (Rep.res H.subtype V))
      (x y z : G) : lift₁ V f (y, z) - lift₁ V f (x, z) + lift₁ V f (x, y) = 0 := by
    have hc := congrArg (V.ρ (a x : G))
      ((mem_cocycles₁_def (⇑f)).mp f.property ((a x)⁻¹ * a y) ((a y)⁻¹ * a z))
    change V.ρ (a x : G) (V.ρ ((a x : G)⁻¹ * (a y : G))
      (f ((a y)⁻¹ * a z)) - f (((a x)⁻¹ * a y) * ((a y)⁻¹ * a z)) +
        f ((a x)⁻¹ * a y)) = V.ρ (a x : G) 0 at hc
    simpa only [lift₁, map_add, map_sub, map_zero, hρ, mul_assoc,
      inv_mul_cancel_left, mul_inv_cancel_left] using hc
  have lift₂_closed (V : Rep.{0} k G) (z : cocycles₂ (Rep.res H.subtype V))
      (w x y u : G) :
      lift₂ V z (x, y, u) - lift₂ V z (w, y, u) +
        lift₂ V z (w, x, u) - lift₂ V z (w, x, y) = 0 := by
    have hc := congrArg (V.ρ (a w : G)) ((mem_cocycles₂_def (⇑z)).mp z.property
      ((a w)⁻¹ * a x) ((a x)⁻¹ * a y) ((a y)⁻¹ * a u))
    change V.ρ (a w : G)
      (V.ρ ((a w : G)⁻¹ * (a x : G)) (z ((a x)⁻¹ * a y, (a y)⁻¹ * a u)) -
        z (((a w)⁻¹ * a x) * ((a x)⁻¹ * a y), (a y)⁻¹ * a u) +
        z ((a w)⁻¹ * a x, ((a x)⁻¹ * a y) * ((a y)⁻¹ * a u)) -
        z ((a w)⁻¹ * a x, (a x)⁻¹ * a y)) = V.ρ (a w : G) 0 at hc
    simpa only [lift₂, map_add, map_sub, map_zero, hρ, mul_assoc,
      inv_mul_cancel_left, mul_inv_cancel_left] using hc
  have avg_closed₁ (V : Rep.{0} k G) (F : G × G → V)
      (hF : ∀ x y z : G, F (y, z) - F (x, z) + F (x, y) = 0)
      (x y z : G) :
      avg V (G × G) F (y, z) - avg V (G × G) F (x, z) +
        avg V (G × G) F (x, y) = 0 := by
    simp only [avg_apply, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro c _
    change V.ρ (t c) (F ((t c)⁻¹ * y, (t c)⁻¹ * z)) -
      V.ρ (t c) (F ((t c)⁻¹ * x, (t c)⁻¹ * z)) +
      V.ρ (t c) (F ((t c)⁻¹ * x, (t c)⁻¹ * y)) = 0
    rw [← map_sub, ← map_add, hF, map_zero]
  have avg_closed₂ (V : Rep.{0} k G) (F : G × G × G → V)
      (hF : ∀ w x y z : G, F (x, y, z) - F (w, y, z) + F (w, x, z) - F (w, x, y) = 0)
      (w x y z : G) :
      avg V (G × G × G) F (x, y, z) - avg V (G × G × G) F (w, y, z) +
        avg V (G × G × G) F (w, x, z) - avg V (G × G × G) F (w, x, y) = 0 := by
    simp only [avg_apply, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro c _
    change V.ρ (t c) (F ((t c)⁻¹ * x, (t c)⁻¹ * y, (t c)⁻¹ * z)) -
      V.ρ (t c) (F ((t c)⁻¹ * w, (t c)⁻¹ * y, (t c)⁻¹ * z)) +
      V.ρ (t c) (F ((t c)⁻¹ * w, (t c)⁻¹ * x, (t c)⁻¹ * z)) -
      V.ρ (t c) (F ((t c)⁻¹ * w, (t c)⁻¹ * x, (t c)⁻¹ * y)) = 0
    rw [← map_sub, ← map_add, ← map_sub, hF, map_zero]
  have transfer_closed₁ (V : Rep.{0} k G) (f : cocycles₁ (Rep.res H.subtype V)) :
      transferCochain₁ V (⇑f) ∈ cocycles₁ V := by
    rw [mem_cocycles₁_def]
    intro s u
    have heq := avg_equivariant V (G × G) (lift₁ V f) (lift₁_eq V f) s (1, u)
    change avg V (G × G) (lift₁ V f) (s * 1, s * u) = _ at heq
    simp only [mul_one] at heq
    change V.ρ s (avg V (G × G) (lift₁ V f) (1, u)) -
      avg V (G × G) (lift₁ V f) (1, s * u) + avg V (G × G) (lift₁ V f) (1, s) = 0
    rw [← heq]
    exact avg_closed₁ V _ (lift₁_closed V f) 1 s (s * u)
  have transfer_closed₂ (V : Rep.{0} k G) (z : cocycles₂ (Rep.res H.subtype V)) :
      transferCochain₂ V (⇑z) ∈ cocycles₂ V := by
    rw [mem_cocycles₂_def]
    intro s u v
    have heq := avg_equivariant V (G × G × G) (lift₂ V z) (lift₂_eq V z) s (1, u, u * v)
    change avg V (G × G × G) (lift₂ V z) (s * 1, s * u, s * (u * v)) = _ at heq
    simp only [mul_one] at heq
    change V.ρ s (avg V (G × G × G) (lift₂ V z) (1, u, u * v)) -
      avg V (G × G × G) (lift₂ V z) (1, s * u, (s * u) * v) +
      avg V (G × G × G) (lift₂ V z) (1, s, s * (u * v)) -
      avg V (G × G × G) (lift₂ V z) (1, s, s * u) = 0
    rw [← heq, mul_assoc]
    exact avg_closed₂ V _ (lift₂_closed V z) 1 s (s * u) (s * (u * v))
  -- Normality controls consecutive differences under independent coordinate changes.
  have difference_level (K : Subgroup G) (hK : K.Normal) (x x' y y' : G)
      (hx : x⁻¹ * x' ∈ K) (hy : y⁻¹ * y' ∈ K) :
      (x⁻¹ * y)⁻¹ * (x'⁻¹ * y') ∈ K := by
    have hc := K.mul_mem (hK.conj_mem _ (K.inv_mem hx) (x⁻¹ * y)⁻¹) hy
    convert hc using 1; group
  have lift₁_level (V : Rep.{0} k G)
      (hV : ∀ g : G, r g ∈ E₀.fixingSubgroup → ∀ v : V, V.ρ g v = v)
      (f : H → Rep.res H.subtype V) (hf : IsLevelConstant₁ rH f) :
      ∃ E : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ E ∧
        ∀ x y u v : G, r u ∈ E.fixingSubgroup → r v ∈ E.fixingSubgroup →
          lift₁ V f (x * u, y * v) = lift₁ V f (x, y) := by
    obtain ⟨F, hF, hf⟩ := hf
    obtain ⟨E, hE, _, h₀, hFE, hKn, _, hKE⟩ := commonLevel F hF
    refine ⟨E, hE, ?_⟩
    intro x y u v hu hv
    let K := E.fixingSubgroup.comap r
    have hx := haLevel K hKn hKE x u hu
    have hy := haLevel K hKn hKE y v hv
    let d : H := (a x)⁻¹ * a y
    let d' : H := (a (x * u))⁻¹ * a (y * v)
    have hd : rH (d⁻¹ * d') ∈ E.fixingSubgroup :=
      difference_level K hKn (a x) (a (x * u)) (a y) (a (y * v)) hx hy
    have hfd : f d' = f d := by
      simpa only [mul_inv_cancel_left] using
        hf d (d⁻¹ * d') (IntermediateField.fixingSubgroup_antitone hFE hd)
    have hact : ∀ w : V, V.ρ (a (x * u) : G) w = V.ρ (a x : G) w := by
      intro w
      calc
        V.ρ (a (x * u) : G) w =
            V.ρ (a x : G) (V.ρ ((a x : G)⁻¹ * (a (x * u) : G)) w) := by
          rw [hρ, mul_inv_cancel_left]
        _ = V.ρ (a x : G) w := by
          rw [hV _ (IntermediateField.fixingSubgroup_antitone h₀ hx)]
    change V.ρ (a (x * u) : G) (f d') = V.ρ (a x : G) (f d)
    rw [hfd, hact]
  have lift₂_level (V : Rep.{0} k G)
      (hV : ∀ g : G, r g ∈ E₀.fixingSubgroup → ∀ v : V, V.ρ g v = v)
      (z : H × H → Rep.res H.subtype V) (hz : IsLevelConstant₂ rH z) :
      ∃ E : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ E ∧
        ∀ x y w u v q : G, r u ∈ E.fixingSubgroup → r v ∈ E.fixingSubgroup →
          r q ∈ E.fixingSubgroup →
          lift₂ V z (x * u, y * v, w * q) = lift₂ V z (x, y, w) := by
    obtain ⟨F, hF, hz⟩ := hz
    obtain ⟨E, hE, _, h₀, hFE, hKn, _, hKE⟩ := commonLevel F hF
    refine ⟨E, hE, ?_⟩
    intro x y w u v q hu hv hq
    let K := E.fixingSubgroup.comap r
    have hx := haLevel K hKn hKE x u hu
    have hy := haLevel K hKn hKE y v hv
    have hw := haLevel K hKn hKE w q hq
    let d : H := (a x)⁻¹ * a y
    let d' : H := (a (x * u))⁻¹ * a (y * v)
    let e : H := (a y)⁻¹ * a w
    let e' : H := (a (y * v))⁻¹ * a (w * q)
    have hd : rH (d⁻¹ * d') ∈ E.fixingSubgroup :=
      difference_level K hKn (a x) (a (x * u)) (a y) (a (y * v)) hx hy
    have he : rH (e⁻¹ * e') ∈ E.fixingSubgroup :=
      difference_level K hKn (a y) (a (y * v)) (a w) (a (w * q)) hy hw
    have hzd : z (d', e') = z (d, e) := by
      simpa only [mul_inv_cancel_left] using
        hz d e (d⁻¹ * d') (e⁻¹ * e')
          (IntermediateField.fixingSubgroup_antitone hFE hd)
          (IntermediateField.fixingSubgroup_antitone hFE he)
    have hact : ∀ v : V, V.ρ (a (x * u) : G) v = V.ρ (a x : G) v := by
      intro v
      calc
        V.ρ (a (x * u) : G) v =
            V.ρ (a x : G) (V.ρ ((a x : G)⁻¹ * (a (x * u) : G)) v) := by
          rw [hρ, mul_inv_cancel_left]
        _ = V.ρ (a x : G) v := by
          rw [hV _ (IntermediateField.fixingSubgroup_antitone h₀ hx)]
    change V.ρ (a (x * u) : G) (z (d', e')) = V.ρ (a x : G) (z (d, e))
    rw [hzd, hact]
  have transfer_level₁ (V : Rep.{0} k G)
      (hV : ∀ g : G, r g ∈ E₀.fixingSubgroup → ∀ v : V, V.ρ g v = v)
      (f : H → Rep.res H.subtype V) (hf : IsLevelConstant₁ rH f) :
      IsLevelConstant₁ r (transferCochain₁ V f) := by
    obtain ⟨E, hE, hlev⟩ := lift₁_level V hV f hf
    refine ⟨E, hE, ?_⟩
    intro s u hu
    change avg V (G × G) (lift₁ V f) (1, s * u) = avg V (G × G) (lift₁ V f) (1, s)
    simp only [avg_apply]
    apply Finset.sum_congr rfl
    intro c _
    congr 1
    change lift₁ V f ((t c)⁻¹ * 1, (t c)⁻¹ * (s * u)) =
      lift₁ V f ((t c)⁻¹ * 1, (t c)⁻¹ * s)
    simpa only [mul_one, mul_assoc] using hlev (t c)⁻¹ ((t c)⁻¹ * s) 1 u
      (by simpa only [map_one] using E.fixingSubgroup.one_mem) hu
  have transfer_level₂ (V : Rep.{0} k G)
      (hV : ∀ g : G, r g ∈ E₀.fixingSubgroup → ∀ v : V, V.ρ g v = v)
      (z : H × H → Rep.res H.subtype V) (hz : IsLevelConstant₂ rH z) :
      IsLevelConstant₂ r (transferCochain₂ V z) := by
    obtain ⟨E, hE, hlev⟩ := lift₂_level V hV z hz
    obtain ⟨D, hD, _, _, hED, hDn, _, _⟩ := commonLevel E hE
    refine ⟨D, hD, ?_⟩
    intro s w u v hu hv
    let K := D.fixingSubgroup.comap r
    have hprod : w⁻¹ * u * w * v ∈ K := by
      apply K.mul_mem _ hv
      simpa only [inv_inv] using hDn.conj_mem u hu w⁻¹
    change avg V (G × G × G) (lift₂ V z) (1, s * u, (s * u) * (w * v)) =
      avg V (G × G × G) (lift₂ V z) (1, s, s * w)
    simp only [avg_apply]
    apply Finset.sum_congr rfl
    intro c _
    congr 1
    change lift₂ V z ((t c)⁻¹ * 1, (t c)⁻¹ * (s * u), (t c)⁻¹ * ((s * u) * (w * v))) =
      lift₂ V z ((t c)⁻¹ * 1, (t c)⁻¹ * s, (t c)⁻¹ * (s * w))
    simpa only [mul_one, mul_assoc, mul_inv_cancel_left] using
      hlev (t c)⁻¹ ((t c)⁻¹ * s) ((t c)⁻¹ * (s * w)) 1 u (w⁻¹ * u * w * v)
        (by simpa only [map_one] using E.fixingSubgroup.one_mem)
        (IntermediateField.fixingSubgroup_antitone hED hu)
        (IntermediateField.fixingSubgroup_antitone hED hprod)
  -- A level primitive is transferred by the very same degree-one cochain map.
  have lift_d₁₂ (V : Rep.{0} k G) (f : H → Rep.res H.subtype V) (x y z : G) :
      lift₂ V ((d₁₂ (Rep.res H.subtype V)).hom f) (x, y, z) =
        lift₁ V f (y, z) - lift₁ V f (x, z) + lift₁ V f (x, y) := by
    change V.ρ (a x : G) ((d₁₂ (Rep.res H.subtype V)).hom f
      ((a x)⁻¹ * a y, (a y)⁻¹ * a z)) = _
    rw [d₁₂_hom_apply]
    change V.ρ (a x : G) (V.ρ ((a x : G)⁻¹ * (a y : G)) (f ((a y)⁻¹ * a z)) -
      f (((a x)⁻¹ * a y) * ((a y)⁻¹ * a z)) + f ((a x)⁻¹ * a y)) = _
    simp only [lift₁, map_add, map_sub, hρ, mul_assoc, mul_inv_cancel_left]
  have transfer_d₁₂ (V : Rep.{0} k G) (f : H → Rep.res H.subtype V) :
      transferCochain₂ V ((d₁₂ (Rep.res H.subtype V)).hom f) =
        (d₁₂ V).hom (transferCochain₁ V f) := by
    ext ⟨s, u⟩
    have heq := avg_equivariant V (G × G) (lift₁ V f) (lift₁_eq V f) s (1, u)
    change avg V (G × G) (lift₁ V f) (s * 1, s * u) = _ at heq
    simp only [mul_one] at heq
    rw [d₁₂_hom_apply]
    change avg V (G × G × G) (lift₂ V ((d₁₂ (Rep.res H.subtype V)).hom f)) (1, s, s * u) =
      V.ρ s (avg V (G × G) (lift₁ V f) (1, u)) -
        avg V (G × G) (lift₁ V f) (1, s * u) + avg V (G × G) (lift₁ V f) (1, s)
    rw [← heq]
    simp only [avg_apply, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro c _
    change V.ρ (t c) (lift₂ V ((d₁₂ (Rep.res H.subtype V)).hom f)
      ((t c)⁻¹ * 1, (t c)⁻¹ * s, (t c)⁻¹ * (s * u))) = _
    rw [lift_d₁₂, map_add, map_sub]
    rfl
  let transferZ₂ (V : Rep.{0} k G)
      (hV : ∀ g : G, r g ∈ E₀.fixingSubgroup → ∀ v : V, V.ρ g v = v) :
      levelCocycles₂ rH (Rep.res H.subtype V) →ₗ[k] levelCocycles₂ r V :=
    (transferCochain₂ V).restrict (fun z hz =>
      ⟨transfer_closed₂ V ⟨z, hz.1⟩, transfer_level₂ V hV z hz.2⟩)
  let C₂ (V : Rep.{0} k G)
      (hV : ∀ g : G, r g ∈ E₀.fixingSubgroup → ∀ v : V, V.ρ g v = v) :
      continuousH2 rH (Rep.res H.subtype V) →ₗ[k] continuousH2 r V :=
    Submodule.mapQ _ _ (transferZ₂ V hV) (by
      intro z hz
      obtain ⟨f, hf, heq⟩ := (mem_levelCoboundaries₂_iff rH (Rep.res H.subtype V) z).mp hz
      change transferCochain₂ V z ∈ levelCoboundaries₂ r V
      apply (mem_levelCoboundaries₂_iff r V _).mpr
      refine ⟨transferCochain₁ V f, transfer_level₁ V hV f hf, ?_⟩
      rw [← transfer_d₁₂, heq])
  have C₂_rep (V : Rep.{0} k G)
      (hV : ∀ g : G, r g ∈ E₀.fixingSubgroup → ∀ v : V, V.ρ g v = v)
      (z : levelCocycles₂ rH (Rep.res H.subtype V)) :
      C₂ V hV (continuousH2π rH (Rep.res H.subtype V) z) =
        continuousH2π r V (transferZ₂ V hV z) := rfl
  let transferCochain₀ (V : Rep.{0} k G) : V →ₗ[k] V :=
    { toFun := fun v => ∑ c : G ⧸ H, V.ρ (t c) (V.ρ (a (t c)⁻¹ : G) v)
      map_add' := by intro v w; simp only [map_add, Finset.sum_add_distrib]
      map_smul' := by intro c v; simp only [map_smul, Finset.smul_sum, RingHom.id_apply] }
  have lift₀_eq (V : Rep.{0} k G) (v : V) (h : H) (x : G) :
      V.ρ (a ((h : G) • x) : G) v = V.ρ (h : G) (V.ρ (a x : G) v) := by
    change V.ρ (a ((h : G) * x) : G) v = _
    rw [haEq, hρ]
    rfl
  have transfer_d₀₁ (V : Rep.{0} k G) (v : V) :
      transferCochain₁ V ((d₀₁ (Rep.res H.subtype V)).hom v) =
        (d₀₁ V).hom (transferCochain₀ V v) := by
    ext s
    have heq := avg_equivariant V G (fun x => V.ρ (a x : G) v) (lift₀_eq V v) s 1
    change avg V G (fun x => V.ρ (a x : G) v) (s * 1) = _ at heq
    simp only [mul_one, avg_apply] at heq
    change (∑ c : G ⧸ H, V.ρ (t c) (V.ρ (a ((t c)⁻¹ * s) : G) v)) =
      V.ρ s (∑ c : G ⧸ H, V.ρ (t c) (V.ρ (a ((t c)⁻¹ * 1) : G) v)) at heq
    simp only [mul_one] at heq
    rw [d₀₁_hom_apply]
    change avg V (G × G) (lift₁ V ((d₀₁ (Rep.res H.subtype V)).hom v)) (1, s) =
      V.ρ s (∑ c : G ⧸ H, V.ρ (t c) (V.ρ (a (t c)⁻¹ : G) v)) -
        ∑ c : G ⧸ H, V.ρ (t c) (V.ρ (a (t c)⁻¹ : G) v)
    rw [← heq]
    simp only [avg_apply, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro c _
    change V.ρ (t c) (V.ρ (a ((t c)⁻¹ * 1) : G)
      ((d₀₁ (Rep.res H.subtype V)).hom v
        ((a ((t c)⁻¹ * 1))⁻¹ * a ((t c)⁻¹ * s)))) = _
    rw [d₀₁_hom_apply]
    change V.ρ (t c) (V.ρ (a ((t c)⁻¹ * 1) : G)
      (V.ρ ((a ((t c)⁻¹ * 1) : G)⁻¹ * (a ((t c)⁻¹ * s) : G)) v - v)) = _
    simp only [map_sub, hρ, mul_inv_cancel_left, mul_one]
  let transferZ₁ (V : Rep.{0} k G) :
      cocycles₁ (Rep.res H.subtype V) →ₗ[k] cocycles₁ V :=
    (transferCochain₁ V).restrict (fun f hf => transfer_closed₁ V ⟨f, hf⟩)
  have transfer_boundary₁ (V : Rep.{0} k G)
      (f : cocycles₁ (Rep.res H.subtype V)) (hf : ⇑f ∈ coboundaries₁ (Rep.res H.subtype V)) :
      (H1π V).hom (transferZ₁ V f) = 0 := by
    apply (H1π_eq_zero_iff _).mpr
    obtain ⟨v, hv⟩ := hf
    refine ⟨transferCochain₀ V v, ?_⟩
    change (d₀₁ V).hom (transferCochain₀ V v) = transferCochain₁ V f
    rw [← transfer_d₀₁, hv]
  let transferH₁ (V : Rep.{0} k G) : H1 (Rep.res H.subtype V) →ₗ[k] H1 V :=
    H1desc ((H1π V).hom ∘ₗ transferZ₁ V) (transfer_boundary₁ V)
  have transferH₁_rep (V : Rep.{0} k G) (f : cocycles₁ (Rep.res H.subtype V)) :
      transferH₁ V ((H1π (Rep.res H.subtype V)).hom f) = (H1π V).hom (transferZ₁ V f) :=
    H1desc_H1π _ _ f
  let C₁ (V : Rep.{0} k G)
      (hV : ∀ g : G, r g ∈ E₀.fixingSubgroup → ∀ v : V, V.ρ g v = v) :
      continuousH1 rH (Rep.res H.subtype V) →ₗ[k] continuousH1 r V :=
    (transferH₁ V).restrict (by
      intro x hx
      obtain ⟨f, hf, rfl⟩ := (mem_continuousH1_iff rH (Rep.res H.subtype V) x).mp hx
      rw [transferH₁_rep]
      exact H1π_mem_continuousH1 r V (transfer_level₁ V hV f hf))
  let resH₁ (V : Rep.{0} k G) : H1 V →ₗ[k] H1 (Rep.res H.subtype V) :=
    (groupCohomology.map H.subtype (𝟙 (Rep.res H.subtype V)) 1).hom
  have resH₁_rep (V : Rep.{0} k G) (f : cocycles₁ V) :
      resH₁ V ((H1π V).hom f) =
        (H1π (Rep.res H.subtype V)).hom (mapCocycles₁ H.subtype (𝟙 (Rep.res H.subtype V)) f) :=
    H1π_comp_map_apply H.subtype (𝟙 (Rep.res H.subtype V)) f
  let R₁ (V : Rep.{0} k G) : continuousH1 r V →ₗ[k] continuousH1 rH (Rep.res H.subtype V) :=
    (resH₁ V).restrict (by
      intro x hx
      obtain ⟨f, hf, rfl⟩ := (mem_continuousH1_iff r V x).mp hx
      rw [resH₁_rep]
      apply H1π_mem_continuousH1
      change IsLevelConstant₁ rH (fun h : H => f (h : G))
      exact IsLevelConstant₁.precomp H.subtype (fun _ => rfl) hf)
  -- Averaging commutes with each of the two low-degree deletion differentials.
  have avg_δ₀ (V : Rep.{0} k G) (F : G → V) (x y : G) :
      avg V (G × G) (fun xy => F xy.2 - F xy.1) (x, y) =
        avg V G F y - avg V G F x := by
    simp only [avg_apply, map_sub, Finset.sum_sub_distrib]
    rfl
  have avg_δ₁ (V : Rep.{0} k G) (F : G × G → V) (x y z : G) :
      avg V (G × G × G) (fun xyz => F (xyz.2.1, xyz.2.2) -
        F (xyz.1, xyz.2.2) + F (xyz.1, xyz.2.1)) (x, y, z) =
        avg V (G × G) F (y, z) - avg V (G × G) F (x, z) + avg V (G × G) F (x, y) := by
    simp only [avg_apply, map_sub, map_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    rfl
  -- Transfer after restriction in H¹: the averaged prism is an ordinary boundary.
  have transfer_res₁ (V : Rep.{0} k G) (f : cocycles₁ V) :
      transferH₁ V (resH₁ V ((H1π V).hom f)) = (H.index : k) • (H1π V).hom f := by
    let fH := mapCocycles₁ H.subtype (𝟙 (Rep.res H.subtype V)) f
    let p : G → V := fun x => hom₁ V f (a x) x
    have hpH : ∀ (h : H) (x : G), p ((h : G) • x) = V.ρ (h : G) (p x) := by
      intro h x
      change hom₁ V f (a ((h : G) * x)) ((h : G) * x) = _
      rw [haEq]
      exact hom₁_eq V f (h : G) (a x) x
    have hpr : (fun xy : G × G => hom₁ V f xy.1 xy.2) - lift₁ V fH =
        fun xy => p xy.2 - p xy.1 := by
      funext xy
      exact prism₁ V f xy.1 xy.2
    have hi : ∀ s : G, avg V (G × G) (fun xy => hom₁ V f xy.1 xy.2) (1, s) =
        (H.index : k) • f s := by
      intro s
      have hh := avg_index V (G × G) (fun xy => hom₁ V f xy.1 xy.2)
        (fun s xy => hom₁_eq V f s xy.1 xy.2) (1, s)
      simpa only [hom₁, map_one, Module.End.one_apply, inv_one, one_mul] using hh
    have hdiff : ∀ s : G, (H.index : k) • f s - transferCochain₁ V fH s =
        V.ρ s (avg V G p 1) - avg V G p 1 := by
      intro s
      have heq := congrArg (fun F : G × G → V => avg V (G × G) F (1, s)) hpr
      rw [map_sub, Pi.sub_apply, hi, avg_δ₀] at heq
      have heqv := avg_equivariant V G p hpH s 1
      change avg V G p (s * 1) = _ at heqv
      simp only [mul_one] at heqv
      rw [heqv] at heq
      exact heq
    rw [resH₁_rep, transferH₁_rep, ← map_smul]
    apply (H1π_eq_iff _ _).mpr
    refine ⟨-(avg V G p 1), ?_⟩
    funext s
    rw [d₀₁_hom_apply, map_neg]
    change -V.ρ s (avg V G p 1) - -avg V G p 1 =
      transferCochain₁ V fH s - (H.index : k) • f s
    calc
      -V.ρ s (avg V G p 1) - -avg V G p 1 =
          -(V.ρ s (avg V G p 1) - avg V G p 1) := by abel
      _ = -((H.index : k) • f s - transferCochain₁ V fH s) :=
        congrArg Neg.neg (hdiff s).symm
      _ = _ := neg_sub _ _
  have C₁_R₁ (V : Rep.{0} k G)
      (hV : ∀ g : G, r g ∈ E₀.fixingSubgroup → ∀ v : V, V.ρ g v = v)
      (x : continuousH1 r V) : C₁ V hV (R₁ V x) = (H.index : k) • x := by
    apply Subtype.ext
    obtain ⟨f, _, hf⟩ := (mem_continuousH1_iff r V x.val).mp x.property
    change transferH₁ V (resH₁ V x.val) = (H.index : k) • x.val
    rw [← hf]
    exact transfer_res₁ V f
  have hom₂_level (V : Rep.{0} k G)
      (hV : ∀ g : G, r g ∈ E₀.fixingSubgroup → ∀ v : V, V.ρ g v = v)
      (z : G × G → V) (hz : IsLevelConstant₂ r z) :
      ∃ E : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ E ∧
        (E.fixingSubgroup.comap r).Normal ∧ E.fixingSubgroup.comap r ≤ H ∧
        ∀ x x' y y' w w' : G,
          r (x⁻¹ * x') ∈ E.fixingSubgroup → r (y⁻¹ * y') ∈ E.fixingSubgroup →
          r (w⁻¹ * w') ∈ E.fixingSubgroup → hom₂ V z x' y' w' = hom₂ V z x y w := by
    obtain ⟨F, hF, hz⟩ := hz
    obtain ⟨E, hE, _, h₀, hFE, hKn, _, hKE⟩ := commonLevel F hF
    refine ⟨E, hE, hKn, hKE, ?_⟩
    intro x x' y y' w w' hx hy hw
    let K := E.fixingSubgroup.comap r
    have hd := difference_level K hKn x x' y y' hx hy
    have he := difference_level K hKn y y' w w' hy hw
    have hzd : z (x'⁻¹ * y', y'⁻¹ * w') = z (x⁻¹ * y, y⁻¹ * w) := by
      simpa only [mul_inv_cancel_left] using
        hz (x⁻¹ * y) (y⁻¹ * w) ((x⁻¹ * y)⁻¹ * (x'⁻¹ * y'))
          ((y⁻¹ * w)⁻¹ * (y'⁻¹ * w'))
          (IntermediateField.fixingSubgroup_antitone hFE hd)
          (IntermediateField.fixingSubgroup_antitone hFE he)
    change V.ρ x' (z (x'⁻¹ * y', y'⁻¹ * w')) = V.ρ x (z (x⁻¹ * y, y⁻¹ * w))
    rw [hzd]
    calc
      V.ρ x' _ = V.ρ x (V.ρ (x⁻¹ * x') _) := by rw [hρ, mul_inv_cancel_left]
      _ = _ := by rw [hV _ (IntermediateField.fixingSubgroup_antitone h₀ hx)]
  have avg_level₁ (V : Rep.{0} k G) (F : G × G → V)
      (E : IntermediateField ℚ (AlgebraicClosure ℚ)) (hE : FiniteDimensional ℚ E)
      (hlev : ∀ x y u v : G, r u ∈ E.fixingSubgroup → r v ∈ E.fixingSubgroup →
        F (x * u, y * v) = F (x, y)) :
      IsLevelConstant₁ r (fun s => avg V (G × G) F (1, s)) := by
    refine ⟨E, hE, ?_⟩
    intro s u hu
    simp only [avg_apply]
    apply Finset.sum_congr rfl
    intro c _
    congr 1
    change F ((t c)⁻¹ * 1, (t c)⁻¹ * (s * u)) = F ((t c)⁻¹ * 1, (t c)⁻¹ * s)
    simpa only [mul_one, mul_assoc] using hlev (t c)⁻¹ ((t c)⁻¹ * s) 1 u
      (by simpa only [map_one] using E.fixingSubgroup.one_mem) hu
  have avg_boundary₂ (V : Rep.{0} k G) (F : G × G → V)
      (hFH : ∀ (h : H) (xy : G × G), F ((h : G) • xy) = V.ρ (h : G) (F xy))
      (s u : G) :
      (d₁₂ V).hom (fun s => avg V (G × G) F (1, s)) (s, u) =
        avg V (G × G × G) (fun xyz => F (xyz.2.1, xyz.2.2) -
          F (xyz.1, xyz.2.2) + F (xyz.1, xyz.2.1)) (1, s, s * u) := by
    rw [avg_δ₁, d₁₂_hom_apply]
    have heq := avg_equivariant V (G × G) F hFH s (1, u)
    change avg V (G × G) F (s * 1, s * u) = _ at heq
    simpa only [mul_one, heq] using congrArg
      (fun v : V => v - avg V (G × G) F (1, s * u) + avg V (G × G) F (1, s)) heq.symm
  have C₂_R₂ (V : Rep.{0} k G)
      (hV : ∀ g : G, r g ∈ E₀.fixingSubgroup → ∀ v : V, V.ρ g v = v)
      (x : continuousH2 r V) : C₂ V hV (R₂ V x) = (H.index : k) • x := by
    obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective
      ((levelCoboundaries₂ r V).comap (levelCocycles₂ r V).subtype) x
    let zH : levelCocycles₂ rH (Rep.res H.subtype V) := levelCocycles₂Map H.subtype (fun _ => rfl)
      (LinearMap.id : V →ₗ[k] V) (fun _ _ => rfl) z
    let p : G × G → V := fun xy =>
      hom₂ V z (a xy.1) xy.1 xy.2 - hom₂ V z (a xy.1) (a xy.2) xy.2
    have hpH : ∀ (h : H) (xy : G × G), p ((h : G) • xy) = V.ρ (h : G) (p xy) := by
      intro h xy
      change hom₂ V z (a ((h : G) * xy.1)) ((h : G) * xy.1) ((h : G) * xy.2) -
        hom₂ V z (a ((h : G) * xy.1)) (a ((h : G) * xy.2)) ((h : G) * xy.2) = _
      simp only [haEq, Subgroup.coe_mul, hom₂_eq, p, map_sub]
    have hplevel : IsLevelConstant₁ r (fun s => avg V (G × G) p (1, s)) := by
      obtain ⟨E, hE, hKn, hKH', hz⟩ := hom₂_level V hV z z.property.2
      apply avg_level₁ V p E hE
      intro x y u v hu hv
      have hx := haLevel (E.fixingSubgroup.comap r) hKn hKH' x u hu
      have hy := haLevel (E.fixingSubgroup.comap r) hKn hKH' y v hv
      have hxu : r (x⁻¹ * (x * u)) ∈ E.fixingSubgroup := by simpa only [inv_mul_cancel_left] using hu
      have hyv : r (y⁻¹ * (y * v)) ∈ E.fixingSubgroup := by simpa only [inv_mul_cancel_left] using hv
      exact congrArg₂ (· - ·) (hz (a x) (a (x * u)) x (x * u) y (y * v) hx hxu hyv)
        (hz (a x) (a (x * u)) (a y) (a (y * v)) y (y * v) hx hy hyv)
    have hpr : (fun xyz : G × G × G => hom₂ V z xyz.1 xyz.2.1 xyz.2.2) - lift₂ V zH =
        fun xyz => p (xyz.2.1, xyz.2.2) - p (xyz.1, xyz.2.2) + p (xyz.1, xyz.2.1) := by
      funext xyz
      exact prism₂ V ⟨z, z.property.1⟩ xyz.1 xyz.2.1 xyz.2.2
    have hi : ∀ s u : G, avg V (G × G × G) (fun xyz => hom₂ V z xyz.1 xyz.2.1 xyz.2.2)
        (1, s, s * u) = (H.index : k) • (z : G × G → V) (s, u) := by
      intro s u
      have hh := avg_index V (G × G × G) (fun xyz => hom₂ V z xyz.1 xyz.2.1 xyz.2.2)
        (fun s xyz => hom₂_eq V z s xyz.1 xyz.2.1 xyz.2.2) (1, s, s * u)
      simpa only [hom₂, map_one, Module.End.one_apply, inv_one, one_mul, inv_mul_cancel_left] using hh
    have hb : (H.index : k) • (z : G × G → V) - transferCochain₂ V zH ∈ levelCoboundaries₂ r V := by
      apply (mem_levelCoboundaries₂_iff r V _).mpr
      refine ⟨fun s => avg V (G × G) p (1, s), hplevel, ?_⟩
      funext st
      rcases st with ⟨s, u⟩
      rw [avg_boundary₂ V p hpH]
      have heq := congrArg (fun F : G × G × G → V => avg V (G × G × G) F (1, s, s * u)) hpr
      rw [map_sub, Pi.sub_apply, hi] at heq
      exact heq.symm
    change C₂ V hV (continuousH2π rH (Rep.res H.subtype V) zH) =
      (H.index : k) • continuousH2π r V z
    rw [C₂_rep V hV, ← map_smul]
    symm
    apply sub_eq_zero.mp
    rw [← map_sub]
    exact (continuousH2π_eq_zero_iff r V _).mpr hb
  have projection₀_left (m : A.ρ.invariants) (y : continuousH2 rH BH) :
      C₂ N hN (PH 0 (R₀ A m) y) = P 0 m (C₂ B hB y) := by
    obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective
      ((levelCoboundaries₂ rH BH).comap (levelCocycles₂ rH BH).subtype) y
    obtain ⟨eH, heH, hPHrep⟩ := hPH.1 (R₀ A m) z
    obtain ⟨eG, heG, hPrep⟩ := hP.1 m (transferZ₂ B hB z)
    rw [hPHrep, C₂_rep N hN, C₂_rep B hB, hPrep]
    congr 1
    apply Subtype.ext
    funext st
    rcases st with ⟨s, u⟩
    have hfun : lift₂ N eH = fun xyz => φ (m : A) (lift₂ B z xyz) := by
      funext xyz
      change N.ρ (a xyz.1 : G) ((eH : H × H → NH)
        ((a xyz.1)⁻¹ * a xyz.2.1, (a xyz.2.1)⁻¹ * a xyz.2.2)) = _
      rw [heH]
      change N.ρ (a xyz.1 : G) (φ (m : A) ((z : H × H → BH) _)) = _
      rw [← hφ, m.property]
    change avg N (G × G × G) (lift₂ N eH) (1, s, s * u) = (eG : G × G → N) (s, u)
    rw [hfun, heG]
    change avg N (G × G × G) (fun xyz => φ (m : A) (lift₂ B z xyz)) (1, s, s * u) =
      φ (m : A) (avg B (G × G × G) (lift₂ B z) (1, s, s * u))
    simp only [avg_apply]
    exact (avg_product (G × G × G) (G × G × G) (fun _ => (m : A)) (lift₂ B z)).1
      (fun g _ => (m.property g).symm) (1, s, s * u) (1, s, s * u)
  have projection₂_right (x : continuousH2 rH AH) (d : B.ρ.invariants) :
      C₂ N hN (PH 2 x (R₀ B d)) = P 2 (C₂ A hA x) d := by
    obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective
      ((levelCoboundaries₂ rH AH).comap (levelCocycles₂ rH AH).subtype) x
    obtain ⟨eH, heH, hPHrep⟩ := hPH.2.2 z (R₀ B d)
    obtain ⟨eG, heG, hPrep⟩ := hP.2.2 (transferZ₂ A hA z) d
    rw [hPHrep, C₂_rep N hN, C₂_rep A hA, hPrep]
    congr 1
    apply Subtype.ext
    funext st
    rcases st with ⟨s, u⟩
    have hfun : lift₂ N eH = fun xyz => φ (lift₂ A z xyz) (d : B) := by
      funext xyz
      change N.ρ (a xyz.1 : G) ((eH : H × H → NH)
        ((a xyz.1)⁻¹ * a xyz.2.1, (a xyz.2.1)⁻¹ * a xyz.2.2)) = _
      rw [heH]
      change N.ρ (a xyz.1 : G) (φ ((z : H × H → AH) _) (d : B)) = _
      rw [← hφ, d.property]
    change avg N (G × G × G) (lift₂ N eH) (1, s, s * u) = (eG : G × G → N) (s, u)
    rw [hfun, heG]
    change avg N (G × G × G) (fun xyz => φ (lift₂ A z xyz) (d : B)) (1, s, s * u) =
      φ (avg A (G × G × G) (lift₂ A z) (1, s, s * u)) (d : B)
    simp only [avg_apply]
    exact (avg_product (G × G × G) (G × G × G) (lift₂ A z) (fun _ => (d : B))).2
      (fun g _ => (d.property g).symm) (1, s, s * u) (1, s, s * u)
  have prism_data₂ (V : Rep.{0} k G)
      (hV : ∀ g : G, r g ∈ E₀.fixingSubgroup → ∀ v : V, V.ρ g v = v)
      (z : levelCocycles₂ r V) :
      ∃ p : G × G → V,
        (∀ (h : H) (xy : G × G), p ((h : G) • xy) = V.ρ (h : G) (p xy)) ∧
        IsLevelConstant₂ r p ∧
        ∀ x y u : G, hom₂ V z x y u - hom₂ V z (a x) (a y) (a u) =
          p (y, u) - p (x, u) + p (x, y) := by
    let p : G × G → V := fun xy =>
      hom₂ V z (a xy.1) xy.1 xy.2 - hom₂ V z (a xy.1) (a xy.2) xy.2
    refine ⟨p, ?_, ?_, prism₂ V ⟨z, z.property.1⟩⟩
    · intro h xy
      change hom₂ V z (a ((h : G) * xy.1)) ((h : G) * xy.1) ((h : G) * xy.2) -
        hom₂ V z (a ((h : G) * xy.1)) (a ((h : G) * xy.2)) ((h : G) * xy.2) = _
      simp only [haEq, Subgroup.coe_mul, hom₂_eq, p, map_sub]
    · obtain ⟨E, hE, hKn, hKH', hz⟩ := hom₂_level V hV z z.property.2
      refine ⟨E, hE, ?_⟩
      intro x y u v hu hv
      have hx := haLevel (E.fixingSubgroup.comap r) hKn hKH' x u hu
      have hy := haLevel (E.fixingSubgroup.comap r) hKn hKH' y v hv
      have hxu : r (x⁻¹ * (x * u)) ∈ E.fixingSubgroup := by simpa only [inv_mul_cancel_left] using hu
      have hyv : r (y⁻¹ * (y * v)) ∈ E.fixingSubgroup := by simpa only [inv_mul_cancel_left] using hv
      exact congrArg₂ (· - ·) (hz (a x) (a (x * u)) x (x * u) y (y * v) hx hxu hyv)
        (hz (a x) (a (x * u)) (a y) (a (y * v)) y (y * v) hx hy hyv)
  have eq_of_avg_boundary (e e' : levelCocycles₂ r N) (p : G × G → N)
      (hpH : ∀ (h : H) (xy : G × G), p ((h : G) • xy) = N.ρ (h : G) (p xy))
      (hplev : IsLevelConstant₂ r p)
      (heq : ∀ s u : G, (e : G × G → N) (s, u) - (e' : G × G → N) (s, u) =
        avg N (G × G × G) (fun xyz => p (xyz.2.1, xyz.2.2) -
          p (xyz.1, xyz.2.2) + p (xyz.1, xyz.2.1)) (1, s, s * u)) :
      continuousH2π r N e = continuousH2π r N e' := by
    apply sub_eq_zero.mp
    rw [← map_sub]
    apply (continuousH2π_eq_zero_iff r N _).mpr
    apply (mem_levelCoboundaries₂_iff r N _).mpr
    obtain ⟨E, hE, hp⟩ := hplev
    refine ⟨fun s => avg N (G × G) p (1, s), avg_level₁ N p E hE hp, ?_⟩
    funext st
    rcases st with ⟨s, u⟩
    rw [avg_boundary₂ N p hpH]
    exact (heq s u).symm
  have projection₀_right (m : AH.ρ.invariants) (y : continuousH2 r B) :
      C₂ N hN (PH 0 m (R₂ B y)) = P 0 (C₀ A m) y := by
    obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective
      ((levelCoboundaries₂ r B).comap (levelCocycles₂ r B).subtype) y
    let zH : levelCocycles₂ rH BH := levelCocycles₂Map H.subtype (fun _ => rfl)
      (LinearMap.id : B →ₗ[k] B) (fun _ _ => rfl) z
    obtain ⟨eH, heH, hPHrep⟩ := hPH.1 m zH
    obtain ⟨eG, heG, hPrep⟩ := hP.1 (C₀ A m) z
    change C₂ N hN (PH 0 m (continuousH2π rH BH zH)) = P 0 (C₀ A m) (continuousH2π r B z)
    rw [hPHrep, C₂_rep N hN, hPrep]
    obtain ⟨p, hpH, hplev, hp⟩ := prism_data₂ B hB z
    symm
    apply eq_of_avg_boundary eG (transferZ₂ N hN eH) (fun xy => φ (m : A) (p xy))
    · intro h xy
      rw [hpH, ← hφ]
      rw [show A.ρ (h : G) (m : A) = (m : A) from m.property h]
    · exact hplev.comp (φ (m : A))
    · intro s u
      let F : G × G × G → N := fun xyz => φ (m : A) (hom₂ B z xyz.1 xyz.2.1 xyz.2.2)
      have hF : avg N (G × G × G) F (1, s, s * u) = (eG : G × G → N) (s, u) := by
        rw [heG, avg_apply]
        change _ = φ (∑ c : G ⧸ H, A.ρ (t c) (m : A)) ((z : G × G → B) (s, u))
        have hh := (avg_product (G × G × G) (G × G × G) (fun _ => (m : A))
          (fun xyz => hom₂ B z xyz.1 xyz.2.1 xyz.2.2)).2
          (fun g xyz => hom₂_eq B z g xyz.1 xyz.2.1 xyz.2.2) (1, s, s * u) (1, s, s * u)
        simpa only [F, hom₂, map_one, Module.End.one_apply, inv_one, one_mul,
          inv_mul_cancel_left] using hh
      have hd : F - lift₂ N eH = fun xyz =>
          φ (m : A) (p (xyz.2.1, xyz.2.2)) - φ (m : A) (p (xyz.1, xyz.2.2)) +
            φ (m : A) (p (xyz.1, xyz.2.1)) := by
        funext xyz
        have hl : lift₂ N eH xyz = φ (m : A) (hom₂ B z (a xyz.1) (a xyz.2.1) (a xyz.2.2)) := by
          change N.ρ (a xyz.1 : G) ((eH : H × H → NH) _) = _
          rw [heH]
          change N.ρ (a xyz.1 : G) (φ (m : A) ((zH : H × H → BH) _)) = _
          rw [← hφ, show A.ρ (a xyz.1 : G) (m : A) = (m : A) from m.property (a xyz.1)]
          rfl
        change F xyz - lift₂ N eH xyz = _
        rw [hl]
        change φ (m : A) (hom₂ B z xyz.1 xyz.2.1 xyz.2.2) -
          φ (m : A) (hom₂ B z (a xyz.1) (a xyz.2.1) (a xyz.2.2)) = _
        rw [← map_sub, hp, map_add, map_sub]
      have hh := congrArg (fun F => avg N (G × G × G) F (1, s, s * u)) hd
      rw [map_sub, Pi.sub_apply, hF] at hh
      exact hh
  have projection₂_left (x : continuousH2 r A) (d : BH.ρ.invariants) :
      C₂ N hN (PH 2 (R₂ A x) d) = P 2 x (C₀ B d) := by
    obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective
      ((levelCoboundaries₂ r A).comap (levelCocycles₂ r A).subtype) x
    let zH : levelCocycles₂ rH AH := levelCocycles₂Map H.subtype (fun _ => rfl)
      (LinearMap.id : A →ₗ[k] A) (fun _ _ => rfl) z
    obtain ⟨eH, heH, hPHrep⟩ := hPH.2.2 zH d
    obtain ⟨eG, heG, hPrep⟩ := hP.2.2 z (C₀ B d)
    change C₂ N hN (PH 2 (continuousH2π rH AH zH) d) = P 2 (continuousH2π r A z) (C₀ B d)
    rw [hPHrep, C₂_rep N hN, hPrep]
    obtain ⟨p, hpH, hplev, hp⟩ := prism_data₂ A hA z
    symm
    apply eq_of_avg_boundary eG (transferZ₂ N hN eH) (fun xy => φ (p xy) (d : B))
    · intro h xy
      rw [hpH, ← hφ]
      rw [show B.ρ (h : G) (d : B) = (d : B) from d.property h]
    · exact hplev.comp (fun v => φ v (d : B))
    · intro s u
      let F : G × G × G → N := fun xyz => φ (hom₂ A z xyz.1 xyz.2.1 xyz.2.2) (d : B)
      have hF : avg N (G × G × G) F (1, s, s * u) = (eG : G × G → N) (s, u) := by
        rw [heG, avg_apply]
        change _ = φ ((z : G × G → A) (s, u)) (∑ c : G ⧸ H, B.ρ (t c) (d : B))
        have hh := (avg_product (G × G × G) (G × G × G)
          (fun xyz => hom₂ A z xyz.1 xyz.2.1 xyz.2.2) (fun _ => (d : B))).1
          (fun g xyz => hom₂_eq A z g xyz.1 xyz.2.1 xyz.2.2) (1, s, s * u) (1, s, s * u)
        simpa only [F, hom₂, map_one, Module.End.one_apply, inv_one, one_mul,
          inv_mul_cancel_left] using hh
      have hd : F - lift₂ N eH = fun xyz =>
          φ (p (xyz.2.1, xyz.2.2)) (d : B) - φ (p (xyz.1, xyz.2.2)) (d : B) +
            φ (p (xyz.1, xyz.2.1)) (d : B) := by
        funext xyz
        have hl : lift₂ N eH xyz = φ (hom₂ A z (a xyz.1) (a xyz.2.1) (a xyz.2.2)) (d : B) := by
          change N.ρ (a xyz.1 : G) ((eH : H × H → NH) _) = _
          rw [heH]
          change N.ρ (a xyz.1 : G) (φ ((zH : H × H → AH) _) (d : B)) = _
          rw [← hφ, show B.ρ (a xyz.1 : G) (d : B) = (d : B) from d.property (a xyz.1)]
          rfl
        change F xyz - lift₂ N eH xyz = _
        rw [hl]
        change φ (hom₂ A z xyz.1 xyz.2.1 xyz.2.2) (d : B) -
          φ (hom₂ A z (a xyz.1) (a xyz.2.1) (a xyz.2.2)) (d : B) = _
        rw [← LinearMap.sub_apply, ← map_sub, hp, map_add, map_sub,
          LinearMap.add_apply, LinearMap.sub_apply]
      have hh := congrArg (fun F => avg N (G × G × G) F (1, s, s * u)) hd
      rw [map_sub, Pi.sub_apply, hF] at hh
      exact hh
  have prism_data₁ (V : Rep.{0} k G)
      (hV : ∀ g : G, r g ∈ E₀.fixingSubgroup → ∀ v : V, V.ρ g v = v)
      (f : cocycles₁ V) (hf : IsLevelConstant₁ r (⇑f)) :
      ∃ p : G → V,
        (∀ (h : H) (x : G), p ((h : G) • x) = V.ρ (h : G) (p x)) ∧
        IsLevelConstant₁ r p ∧
        ∀ x y : G, hom₁ V f x y - hom₁ V f (a x) (a y) = p y - p x := by
    let p : G → V := fun x => hom₁ V f (a x) x
    refine ⟨p, ?_, ?_, prism₁ V f⟩
    · intro h x
      change hom₁ V f (a ((h : G) * x)) ((h : G) * x) = _
      rw [haEq]
      exact hom₁_eq V f (h : G) (a x) x
    · obtain ⟨F, hF, hf⟩ := hf
      obtain ⟨E, hE, _, h₀, hFE, hKn, _, hKH'⟩ := commonLevel F hF
      refine ⟨E, hE, ?_⟩
      intro x u hu
      have hx := haLevel (E.fixingSubgroup.comap r) hKn hKH' x u hu
      have hxu : r (x⁻¹ * (x * u)) ∈ E.fixingSubgroup := by simpa only [inv_mul_cancel_left] using hu
      have hd := difference_level (E.fixingSubgroup.comap r) hKn
        (a x) (a (x * u)) x (x * u) hx hxu
      have hfd : f ((a (x * u) : G)⁻¹ * (x * u)) = f ((a x : G)⁻¹ * x) := by
        simpa only [mul_inv_cancel_left] using hf ((a x : G)⁻¹ * x)
          (((a x : G)⁻¹ * x)⁻¹ * ((a (x * u) : G)⁻¹ * (x * u)))
          (IntermediateField.fixingSubgroup_antitone hFE hd)
      change V.ρ (a (x * u) : G) (f ((a (x * u) : G)⁻¹ * (x * u))) =
        V.ρ (a x : G) (f ((a x : G)⁻¹ * x))
      rw [hfd]
      calc
        V.ρ (a (x * u) : G) _ = V.ρ (a x : G) (V.ρ ((a x : G)⁻¹ * (a (x * u) : G)) _) := by
          rw [hρ, mul_inv_cancel_left]
        _ = _ := by rw [hV _ (IntermediateField.fixingSubgroup_antitone h₀ hx)]
  have combine_level₂ {U V W : Type} (f : G × G → U) (g : G × G → V)
      (hf : IsLevelConstant₂ r f) (hg : IsLevelConstant₂ r g) (b : U → V → W) :
      IsLevelConstant₂ r (fun xy => b (f xy) (g xy)) := by
    obtain ⟨E, hE, hf⟩ := hf
    obtain ⟨F, hF, hg⟩ := hg
    let : FiniteDimensional ℚ E := hE
    let : FiniteDimensional ℚ F := hF
    refine ⟨E ⊔ F, inferInstance, ?_⟩
    intro x y u v hu hv
    change b (f (x * u, y * v)) (g (x * u, y * v)) = b (f (x, y)) (g (x, y))
    rw [hf x y u v (IntermediateField.fixingSubgroup_antitone le_sup_left hu)
      (IntermediateField.fixingSubgroup_antitone le_sup_left hv),
      hg x y u v (IntermediateField.fixingSubgroup_antitone le_sup_right hu)
      (IntermediateField.fixingSubgroup_antitone le_sup_right hv)]
  let rep₁ (V : Rep.{0} k G) (f : cocycles₁ V) (hf : IsLevelConstant₁ r (⇑f)) :
      continuousH1 r V := ⟨(H1π V).hom f, H1π_mem_continuousH1 r V hf⟩
  let repH₁ (V : Rep.{0} k G) (f : cocycles₁ (Rep.res H.subtype V))
      (hf : IsLevelConstant₁ rH (⇑f)) : continuousH1 rH (Rep.res H.subtype V) :=
    ⟨(H1π (Rep.res H.subtype V)).hom f, H1π_mem_continuousH1 rH (Rep.res H.subtype V) hf⟩
  let resZ₁ (V : Rep.{0} k G) := mapCocycles₁ H.subtype (𝟙 (Rep.res H.subtype V))
  have resZ₁_level (V : Rep.{0} k G) (f : cocycles₁ V) (hf : IsLevelConstant₁ r (⇑f)) :
      IsLevelConstant₁ rH (⇑(resZ₁ V f)) :=
    IsLevelConstant₁.precomp H.subtype (fun _ => rfl) hf
  have R₁_rep (V : Rep.{0} k G) (f : cocycles₁ V) (hf : IsLevelConstant₁ r (⇑f)) :
      R₁ V (rep₁ V f hf) = repH₁ V (resZ₁ V f) (resZ₁_level V f hf) := by
    apply Subtype.ext
    exact resH₁_rep V f
  have C₁_rep (V : Rep.{0} k G)
      (hV : ∀ g : G, r g ∈ E₀.fixingSubgroup → ∀ v : V, V.ρ g v = v)
      (f : cocycles₁ (Rep.res H.subtype V)) (hf : IsLevelConstant₁ rH (⇑f)) :
      C₁ V hV (repH₁ V f hf) = rep₁ V (transferZ₁ V f) (transfer_level₁ V hV f hf) := by
    apply Subtype.ext
    exact transferH₁_rep V f
  have rep₁_surj (V : Rep.{0} k G) (x : continuousH1 r V) :
      ∃ (f : cocycles₁ V) (hf : IsLevelConstant₁ r (⇑f)), x = rep₁ V f hf := by
    obtain ⟨f, hf, heq⟩ := (mem_continuousH1_iff r V x.val).mp x.property
    exact ⟨f, hf, Subtype.ext heq.symm⟩
  have repH₁_surj (V : Rep.{0} k G) (x : continuousH1 rH (Rep.res H.subtype V)) :
      ∃ (f : cocycles₁ (Rep.res H.subtype V)) (hf : IsLevelConstant₁ rH (⇑f)), x = repH₁ V f hf := by
    obtain ⟨f, hf, heq⟩ := (mem_continuousH1_iff rH (Rep.res H.subtype V) x.val).mp x.property
    exact ⟨f, hf, Subtype.ext heq.symm⟩
  have lift_cup (f : H → AH) (g : H → BH) (e : levelCocycles₂ rH NH)
      (he : ∀ st : H × H, (e : H × H → NH) st = cupCochain φH f g st) (xyz : G × G × G) :
      lift₂ N e xyz = φ (lift₁ A f (xyz.1, xyz.2.1)) (lift₁ B g (xyz.2.1, xyz.2.2)) := by
    change N.ρ (a xyz.1 : G) ((e : H × H → NH) _) = _
    rw [he, cupCochain_apply]
    change N.ρ (a xyz.1 : G) (φ (f ((a xyz.1)⁻¹ * a xyz.2.1))
      (B.ρ ((a xyz.1 : G)⁻¹ * (a xyz.2.1 : G)) (g ((a xyz.2.1)⁻¹ * a xyz.2.2)))) = _
    rw [← hφ, hρ, mul_inv_cancel_left]
  have projection₁_left (x : continuousH1 r A) (y : continuousH1 rH BH) :
      C₂ N hN (PH 1 (R₁ A x) y) = P 1 x (C₁ B hB y) := by
    obtain ⟨f, hf, rfl⟩ := rep₁_surj A x
    obtain ⟨g, hg, rfl⟩ := repH₁_surj B y
    obtain ⟨eH, heH, hPHrep⟩ := hPH.2.1 (resZ₁ A f) (resZ₁_level A f hf) g hg
    obtain ⟨eG, heG, hPrep⟩ := hP.2.1 f hf (transferZ₁ B g) (transfer_level₁ B hB g hg)
    rw [R₁_rep A f hf, C₁_rep B hB g hg, hPHrep, C₂_rep N hN, hPrep]
    obtain ⟨p, hpH, hplev, hp⟩ := prism_data₁ A hA f hf
    let q : G × G → N := fun xy => φ (p xy.1) (lift₁ B g xy)
    symm
    apply eq_of_avg_boundary eG (transferZ₂ N hN eH) q
    · intro h xy
      change φ (p ((h : G) • xy.1)) (lift₁ B g ((h : G) • xy)) = _
      rw [hpH, lift₁_eq, hφ]
    · apply combine_level₂ (fun xy => p xy.1) (lift₁ B g) _ (lift₁_level B hB g hg) (fun v w => φ v w)
      obtain ⟨E, hE, hp⟩ := hplev
      exact ⟨E, hE, fun x _ u _ hu _ => hp x u hu⟩
    · intro s u
      let F : G × G × G → N := fun xyz =>
        φ (hom₁ A f xyz.1 xyz.2.1) (lift₁ B g (xyz.2.1, xyz.2.2))
      have hF : avg N (G × G × G) F (1, s, s * u) = (eG : G × G → N) (s, u) := by
        rw [heG, cupCochain_apply]
        change avg N (G × G × G) F (1, s, s * u) =
          φ (f s) (B.ρ s (avg B (G × G) (lift₁ B g) (1, u)))
        have heq := avg_equivariant B (G × G) (lift₁ B g) (lift₁_eq B g) s (1, u)
        change avg B (G × G) (lift₁ B g) (s * 1, s * u) = _ at heq
        simp only [mul_one] at heq
        rw [← heq, avg_apply]
        have hh := (avg_product (G × G) (G × G) (fun xy => hom₁ A f xy.1 xy.2) (lift₁ B g)).1
          (fun g xy => hom₁_eq A f g xy.1 xy.2) (1, s) (s, s * u)
        simpa only [F, hom₁, map_one, Module.End.one_apply, inv_one, one_mul, avg_apply,
          Prod.smul_mk, Prod.fst, Prod.snd] using hh
      have hd : F - lift₂ N eH = fun xyz => q (xyz.2.1, xyz.2.2) - q (xyz.1, xyz.2.2) + q (xyz.1, xyz.2.1) := by
        funext xyz
        change F xyz - lift₂ N eH xyz = _
        rw [lift_cup (resZ₁ A f) g eH heH]
        change φ (hom₁ A f xyz.1 xyz.2.1) (lift₁ B g (xyz.2.1, xyz.2.2)) -
          φ (hom₁ A f (a xyz.1) (a xyz.2.1)) (lift₁ B g (xyz.2.1, xyz.2.2)) = _
        rw [← LinearMap.sub_apply, ← map_sub, hp]
        have hc := lift₁_closed B g xyz.1 xyz.2.1 xyz.2.2
        have hq : lift₁ B g (xyz.2.1, xyz.2.2) + lift₁ B g (xyz.1, xyz.2.1) =
            lift₁ B g (xyz.1, xyz.2.2) := sub_eq_zero.mp (by
          rw [← sub_add_eq_add_sub]
          exact hc)
        simp only [q, map_sub, LinearMap.sub_apply]
        rw [← hq, map_add]
        abel
      have hh := congrArg (fun F => avg N (G × G × G) F (1, s, s * u)) hd
      rw [map_sub, Pi.sub_apply, hF] at hh
      exact hh
  have projection₁_right (x : continuousH1 rH AH) (y : continuousH1 r B) :
      C₂ N hN (PH 1 x (R₁ B y)) = P 1 (C₁ A hA x) y := by
    obtain ⟨f, hf, rfl⟩ := repH₁_surj A x
    obtain ⟨g, hg, rfl⟩ := rep₁_surj B y
    obtain ⟨eH, heH, hPHrep⟩ := hPH.2.1 f hf (resZ₁ B g) (resZ₁_level B g hg)
    obtain ⟨eG, heG, hPrep⟩ := hP.2.1 (transferZ₁ A f) (transfer_level₁ A hA f hf) g hg
    rw [R₁_rep B g hg, C₁_rep A hA f hf, hPHrep, C₂_rep N hN, hPrep]
    obtain ⟨p, hpH, hplev, hp⟩ := prism_data₁ B hB g hg
    let q : G × G → N := fun xy => -φ (lift₁ A f xy) (p xy.2)
    symm
    apply eq_of_avg_boundary eG (transferZ₂ N hN eH) q
    · intro h xy
      change -φ (lift₁ A f ((h : G) • xy)) (p ((h : G) • xy.2)) = _
      rw [lift₁_eq, hpH, hφ, map_neg]
    · have hq : IsLevelConstant₂ r (fun xy => φ (lift₁ A f xy) (p xy.2)) := by
        apply combine_level₂ (lift₁ A f) (fun xy => p xy.2) (lift₁_level A hA f hf) _ (fun v w => φ v w)
        obtain ⟨E, hE, hp⟩ := hplev
        exact ⟨E, hE, fun _ y _ v _ hv => hp y v hv⟩
      exact hq.comp Neg.neg
    · intro s u
      let F : G × G × G → N := fun xyz =>
        φ (lift₁ A f (xyz.1, xyz.2.1)) (hom₁ B g xyz.2.1 xyz.2.2)
      have hF : avg N (G × G × G) F (1, s, s * u) = (eG : G × G → N) (s, u) := by
        rw [heG, cupCochain_apply]
        change avg N (G × G × G) F (1, s, s * u) =
          φ (avg A (G × G) (lift₁ A f) (1, s)) (B.ρ s (g u))
        rw [avg_apply]
        have hh := (avg_product (G × G) (G × G) (lift₁ A f) (fun xy => hom₁ B g xy.1 xy.2)).2
          (fun s xy => hom₁_eq B g s xy.1 xy.2) (1, s) (s, s * u)
        simpa only [F, hom₁, inv_mul_cancel_left, avg_apply, Prod.smul_mk, Prod.fst, Prod.snd] using hh
      have hd : F - lift₂ N eH = fun xyz => q (xyz.2.1, xyz.2.2) - q (xyz.1, xyz.2.2) + q (xyz.1, xyz.2.1) := by
        funext xyz
        change F xyz - lift₂ N eH xyz = _
        rw [lift_cup f (resZ₁ B g) eH heH]
        change φ (lift₁ A f (xyz.1, xyz.2.1)) (hom₁ B g xyz.2.1 xyz.2.2) -
          φ (lift₁ A f (xyz.1, xyz.2.1)) (hom₁ B g (a xyz.2.1) (a xyz.2.2)) = _
        rw [← map_sub, hp, map_sub]
        have hc := lift₁_closed A f xyz.1 xyz.2.1 xyz.2.2
        have hq : lift₁ A f (xyz.2.1, xyz.2.2) + lift₁ A f (xyz.1, xyz.2.1) =
            lift₁ A f (xyz.1, xyz.2.2) := sub_eq_zero.mp (by
          rw [← sub_add_eq_add_sub]
          exact hc)
        simp only [q]
        rw [← hq, map_add, LinearMap.add_apply]
        abel
      have hh := congrArg (fun F => avg N (G × G × G) F (1, s, s * u)) hd
      rw [map_sub, Pi.sub_apply, hF] at hh
      exact hh
  -- Package one common choice of maps in the two required degree orders.
  let RX : ∀ i : Fin 3, X i →ₗ[k] XH i :=
    fun i => Fin.cases (R₀ A) (fun j => Fin.cases (R₁ A) (fun l => Fin.cases (R₂ A) (fun z => Fin.elim0 z) l) j) i
  let CX : ∀ i : Fin 3, XH i →ₗ[k] X i :=
    fun i => Fin.cases (C₀ A) (fun j => Fin.cases (C₁ A hA) (fun l => Fin.cases (C₂ A hA) (fun z => Fin.elim0 z) l) j) i
  let RY : ∀ i : Fin 3, Y i →ₗ[k] YH i :=
    fun i => Fin.cases (R₂ B) (fun j => Fin.cases (R₁ B) (fun l => Fin.cases (R₀ B) (fun z => Fin.elim0 z) l) j) i
  let CY : ∀ i : Fin 3, YH i →ₗ[k] Y i :=
    fun i => Fin.cases (C₂ B hB) (fun j => Fin.cases (C₁ B hB) (fun l => Fin.cases (C₀ B) (fun z => Fin.elim0 z) l) j) i
  refine ⟨RX, CX, RY, CY, R₂ N, C₂ N hN, ?_, ?_, C₂_R₂ N hN, ?_, ?_⟩
  · intro i x
    fin_cases i
    · exact C₀_R₀ A x
    · exact C₁_R₁ A hA x
    · exact C₂_R₂ A hA x
  · intro i y
    fin_cases i
    · exact C₂_R₂ B hB y
    · exact C₁_R₁ B hB y
    · exact C₀_R₀ B y
  · intro i x y
    fin_cases i
    · exact projection₀_left x y
    · exact projection₁_left x y
    · exact projection₂_left x y
  · intro i x y
    fin_cases i
    · exact projection₀_right x y
    · exact projection₁_right x y
    · exact projection₂_right x y

theorem Submission.p08_7d1ff633a4_cp11_left_level_boundary :
    ∀ {k G : Type} [Field k] [Group G] (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (A B N : Rep.{0} k G) (φ : A →ₗ[k] B →ₗ[k] N), (∀ (s : G) (a : A) (b : B), φ (A.ρ s a) (B.ρ s b) = N.ρ s (φ a b)) → ∀ (a : A) (g : groupCohomology.cocycles₁ B), groupCohomology.IsLevelConstant₁ r (⇑g) → groupCohomology.cupCochain φ (fun s : G => A.ρ s a - a) (⇑g) ∈ groupCohomology.levelCoboundaries₂ r N := by
  intro k G _ _ r A B N φ hφ a g hg
  apply (groupCohomology.mem_levelCoboundaries₂_iff r N _).2
  refine ⟨fun t => φ a (g t), hg.comp (φ a), ?_⟩
  funext p
  obtain ⟨s, t⟩ := p
  rw [groupCohomology.d₁₂_hom_apply]
  change N.ρ s (φ a (g t)) - φ a (g (s * t)) + φ a (g s) =
    φ (A.ρ s a - a) (B.ρ s (g t))
  rw [(groupCohomology.mem_cocycles₁_iff (⇑g)).1 g.2 s t, ← hφ s a (g t)]
  simp only [map_add, map_sub, LinearMap.sub_apply]
  abel

theorem Submission.p08_7d1ff633a4_tt26_cp_zero_two :
    ∀ {k G : Type} [Field k] [Group G]
      (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
      (A B N : Rep.{0} k G) (φ : A →ₗ[k] B →ₗ[k] N),
      (∀ (s : G) (a : A) (b : B),
        φ (A.ρ s a) (B.ρ s b) = N.ρ s (φ a b)) →
      ∃ P : A.ρ.invariants →ₗ[k] continuousH2 r B →ₗ[k] continuousH2 r N,
        ∀ (m : A.ρ.invariants) (z : levelCocycles₂ r B),
          ∃ e : levelCocycles₂ r N,
            (∀ st : G × G, (e : G × G → N) st =
              φ (m : A) ((z : G × G → B) st)) ∧
            P m (continuousH2π r B z) = continuousH2π r N e := by
  intro k G _ _ r A B N φ hφ
  have heq (m : A.ρ.invariants) (s : G) (b : B) :
      φ (m : A) (B.ρ ((MonoidHom.id G) s) b) = N.ρ s (φ (m : A) b) := by
    simpa only [MonoidHom.id_apply, m.property s] using hφ s (m : A) b
  let e (m : A.ρ.invariants) : levelCocycles₂ r B →ₗ[k] levelCocycles₂ r N :=
    levelCocycles₂Map (MonoidHom.id G) (fun _ => rfl) (φ (m : A)) (heq m)
  let F (m : A.ρ.invariants) : continuousH2 r B →ₗ[k] continuousH2 r N :=
    continuousH2Map (MonoidHom.id G) (fun _ => rfl) (φ (m : A)) (heq m)
  have hF (m : A.ρ.invariants) (z : levelCocycles₂ r B) :
      F m (continuousH2π r B z) = continuousH2π r N (e m z) := rfl
  let P : A.ρ.invariants →ₗ[k] continuousH2 r B →ₗ[k] continuousH2 r N :=
    { toFun := F
      map_add' := by
        intro m m'
        apply LinearMap.ext
        intro y
        obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective
          ((levelCoboundaries₂ r B).comap (levelCocycles₂ r B).subtype) y
        change F (m + m') (continuousH2π r B z) =
          F m (continuousH2π r B z) + F m' (continuousH2π r B z)
        rw [hF, hF, hF, ← map_add]
        apply congrArg (continuousH2π r N)
        apply Subtype.ext
        funext st
        change φ ((m : A) + (m' : A)) ((z : G × G → B) st) =
          φ (m : A) ((z : G × G → B) st) + φ (m' : A) ((z : G × G → B) st)
        simp only [map_add, LinearMap.add_apply]
      map_smul' := by
        intro c m
        apply LinearMap.ext
        intro y
        obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective
          ((levelCoboundaries₂ r B).comap (levelCocycles₂ r B).subtype) y
        change F (c • m) (continuousH2π r B z) = c • F m (continuousH2π r B z)
        rw [hF, hF, ← map_smul]
        apply congrArg (continuousH2π r N)
        apply Subtype.ext
        funext st
        change φ (c • (m : A)) ((z : G × G → B) st) =
          c • φ (m : A) ((z : G × G → B) st)
        simp only [map_smul, LinearMap.smul_apply] }
  refine ⟨P, fun m z => ⟨e m z, ?_, hF m z⟩⟩
  intro st
  rfl

theorem Submission.p08_7d1ff633a4_cp11_right_level_boundary :
    ∀ {k G : Type} [Field k] [Group G] (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (A B N : Rep.{0} k G) (E₀ : IntermediateField ℚ (AlgebraicClosure ℚ)), FiniteDimensional ℚ E₀ → (∀ s : G, r s ∈ E₀.fixingSubgroup → ∀ b : B, B.ρ s b = b) → ∀ φ : A →ₗ[k] B →ₗ[k] N, (∀ (s : G) (a : A) (b : B), φ (A.ρ s a) (B.ρ s b) = N.ρ s (φ a b)) → ∀ (f : groupCohomology.cocycles₁ A) (b : B), groupCohomology.IsLevelConstant₁ r (⇑f) → groupCohomology.cupCochain φ (⇑f) (fun t : G => B.ρ t b - b) ∈ groupCohomology.levelCoboundaries₂ r N := by
  intro k G _ _ r A B N E₀ hE₀ hB φ hφ f b hf
  obtain ⟨Ff, hFf, hf⟩ := hf
  let := hE₀
  let := hFf
  apply (groupCohomology.mem_levelCoboundaries₂_iff r N _).2
  refine ⟨fun s => -(φ (f s) (B.ρ s b)), ?_, ?_⟩
  · refine ⟨E₀ ⊔ Ff, inferInstance, ?_⟩
    intro s t ht
    dsimp only
    rw [hf s t (IntermediateField.fixingSubgroup_antitone le_sup_right ht),
      Rep.ρ_mul, LinearMap.comp_apply,
      hB t (IntermediateField.fixingSubgroup_antitone le_sup_left ht) b]
  · funext p
    obtain ⟨s, t⟩ := p
    rw [groupCohomology.d₁₂_hom_apply]
    change N.ρ s (-(φ (f t) (B.ρ t b))) -
        (-(φ (f (s * t)) (B.ρ (s * t) b))) + (-(φ (f s) (B.ρ s b))) =
      φ (f s) (B.ρ s (B.ρ t b - b))
    rw [map_neg, (groupCohomology.mem_cocycles₁_iff (⇑f)).1 f.2 s t,
      ← hφ s (f t) (B.ρ t b), Rep.ρ_mul, LinearMap.comp_apply]
    simp only [map_add, map_sub, LinearMap.add_apply]
    abel
theorem Submission.p08_7d1ff633a4_tt26_theta_from_pairings :
    ∀ {k G : Type} [Field k] [Group G] (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (A B N : Rep.{0} k G) (φ : A →ₗ[k] B →ₗ[k] N), let X : Fin 3 → ModuleCat k := ![ModuleCat.of k A.ρ.invariants, ModuleCat.of k (groupCohomology.continuousH1 r A), ModuleCat.of k (groupCohomology.continuousH2 r A)]; let Y : Fin 3 → ModuleCat k := ![ModuleCat.of k (groupCohomology.continuousH2 r B), ModuleCat.of k (groupCohomology.continuousH1 r B), ModuleCat.of k B.ρ.invariants]; ∀ (P : ∀ i : Fin 3, X i →ₗ[k] Y i →ₗ[k] groupCohomology.continuousH2 r N), ((∀ (m : A.ρ.invariants) (z : groupCohomology.levelCocycles₂ r B), ∃ e : groupCohomology.levelCocycles₂ r N, (∀ st : G × G, (e : G × G → N) st = φ (m : A) ((z : G × G → B) st)) ∧ P 0 m (groupCohomology.continuousH2π r B z) = groupCohomology.continuousH2π r N e) ∧ (∀ (f : groupCohomology.cocycles₁ A) (hf : groupCohomology.IsLevelConstant₁ r (⇑f)) (g : groupCohomology.cocycles₁ B) (hg : groupCohomology.IsLevelConstant₁ r (⇑g)), ∃ e : groupCohomology.levelCocycles₂ r N, (∀ st : G × G, (e : G × G → N) st = groupCohomology.cupCochain φ (⇑f) (⇑g) st) ∧ P 1 ⟨(groupCohomology.H1π A).hom f, groupCohomology.H1π_mem_continuousH1 r A hf⟩ ⟨(groupCohomology.H1π B).hom g, groupCohomology.H1π_mem_continuousH1 r B hg⟩ = groupCohomology.continuousH2π r N e) ∧ (∀ (z : groupCohomology.levelCocycles₂ r A) (d : B.ρ.invariants), ∃ e : groupCohomology.levelCocycles₂ r N, (∀ st : G × G, (e : G × G → N) st = φ ((z : G × G → A) st) (d : B)) ∧ P 2 (groupCohomology.continuousH2π r A z) d = groupCohomology.continuousH2π r N e)) → ∀ ℓ : groupCohomology.continuousH2 r N →ₗ[k] k, ∃ Θ : ∀ i : Fin 3, X i →ₗ[k] Module.Dual k (Y i), (groupCohomology.IsTheta0 r φ ℓ (Θ 0) ∧ groupCohomology.IsTheta1 r φ ℓ (Θ 1) ∧ groupCohomology.IsTheta2 r φ ℓ (Θ 2)) ∧ (∀ (i : Fin 3) (x : X i) (y : Y i), Θ i x y = ℓ (P i x y)) ∧ (∀ Ψ : ∀ i : Fin 3, X i →ₗ[k] Module.Dual k (Y i), (groupCohomology.IsTheta0 r φ ℓ (Ψ 0) ∧ groupCohomology.IsTheta1 r φ ℓ (Ψ 1) ∧ groupCohomology.IsTheta2 r φ ℓ (Ψ 2)) → ∀ i : Fin 3, Ψ i = Θ i) := by
  intro k G _ _ r A B N φ X Y P hP ℓ
  rcases hP with ⟨hP0, hP1, hP2⟩
  let Θ : ∀ i : Fin 3, X i →ₗ[k] Module.Dual k (Y i) := fun i =>
    { toFun := fun x => ℓ.comp (P i x)
      map_add' := by
        intro x x'
        ext y
        change ℓ (P i (x + x') y) = ℓ (P i x y) + ℓ (P i x' y)
        rw [map_add, LinearMap.add_apply, map_add]
      map_smul' := by
        intro c x
        ext y
        change ℓ (P i (c • x) y) = c • ℓ (P i x y)
        rw [map_smul, LinearMap.smul_apply, map_smul] }
  refine ⟨Θ, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro m z e he
    obtain ⟨e', he', hP⟩ := hP0 m z
    have heq : e' = e := Subtype.ext (funext fun st => (he' st).trans (he st).symm)
    subst e'
    change ℓ (P 0 m (continuousH2π r B z)) = ℓ (continuousH2π r N e)
    exact congrArg ℓ hP
  · intro f hf g hg e he
    obtain ⟨e', he', hP⟩ := hP1 f hf g hg
    have heq : e' = e := Subtype.ext (funext fun st => (he' st).trans (he st).symm)
    subst e'
    change ℓ (P 1 ⟨(H1π A).hom f, H1π_mem_continuousH1 r A hf⟩
      ⟨(H1π B).hom g, H1π_mem_continuousH1 r B hg⟩) = ℓ (continuousH2π r N e)
    exact congrArg ℓ hP
  · intro z d e he
    obtain ⟨e', he', hP⟩ := hP2 z d
    have heq : e' = e := Subtype.ext (funext fun st => (he' st).trans (he st).symm)
    subst e'
    change ℓ (P 2 (continuousH2π r A z) d) = ℓ (continuousH2π r N e)
    exact congrArg ℓ hP
  · intro i x y
    rfl
  · intro Ψ hΨ i
    rcases hΨ with ⟨hΨ0, hΨ1, hΨ2⟩
    fin_cases i
    · apply LinearMap.ext
      intro x
      apply LinearMap.ext
      intro y
      change Ψ 0 x y = ℓ (P 0 x y)
      obtain ⟨z, rfl⟩ :=
        (show Function.Surjective (continuousH2π r B) from Submodule.mkQ_surjective _) y
      obtain ⟨e, he, hP⟩ := hP0 x z
      exact (hΨ0 x z e he).trans (congrArg ℓ hP).symm
    · apply LinearMap.ext
      intro x
      apply LinearMap.ext
      intro y
      change Ψ 1 x y = ℓ (P 1 x y)
      obtain ⟨f, hf, hfx⟩ := (mem_continuousH1_iff r A x.val).mp x.property
      obtain ⟨g, hg, hgy⟩ := (mem_continuousH1_iff r B y.val).mp y.property
      have hx : (⟨(H1π A).hom f, H1π_mem_continuousH1 r A hf⟩ : continuousH1 r A) = x :=
        Subtype.ext hfx
      have hy : (⟨(H1π B).hom g, H1π_mem_continuousH1 r B hg⟩ : continuousH1 r B) = y :=
        Subtype.ext hgy
      rw [← hx, ← hy]
      obtain ⟨e, he, hP⟩ := hP1 f hf g hg
      exact (hΨ1 f hf g hg e he).trans (congrArg ℓ hP).symm
    · apply LinearMap.ext
      intro x
      apply LinearMap.ext
      intro y
      change Ψ 2 x y = ℓ (P 2 x y)
      obtain ⟨z, rfl⟩ :=
        (show Function.Surjective (continuousH2π r A) from Submodule.mkQ_surjective _) x
      obtain ⟨e, he, hP⟩ := hP2 z y
      exact (hΨ2 z y e he).trans (congrArg ℓ hP).symm

namespace Submission

theorem p08_7d1ff633a4_common_kernel
    {p : ℕ} [Fact p.Prime] (q : Nat.Primes)
    (S : Subgroup (ExtCitation.primeLocalGaloisGroup q)) (U : Subgroup S)
    (M : Rep.{0} (ZMod p) S) [FiniteDimensional (ZMod p) M]
    (hU : ∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧
      F₀.fixingSubgroup.comap ((ExtCitation.primeLocalToGlobal q).comp S.subtype) ≤ U)
    (hsm : ∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ),
      FiniteDimensional ℚ F ∧ ∀ s : S,
        ((ExtCitation.primeLocalToGlobal q).comp S.subtype) s ∈ F.fixingSubgroup →
          M.ρ s m = m) :
    ∃ E : IntermediateField ℚ (AlgebraicClosure ℚ),
      FiniteDimensional ℚ E ∧ Normal ℚ E ∧
      E.fixingSubgroup.comap ((ExtCitation.primeLocalToGlobal q).comp S.subtype) ≤ U ∧
      (∀ s : S, ((ExtCitation.primeLocalToGlobal q).comp S.subtype) s ∈ E.fixingSubgroup →
        (∀ m : M, M.ρ s m = m) ∧
        (∀ d : M.dualTwist
            (((ExtCitation.cycloChar p).comp (ExtCitation.primeLocalToGlobal q)).comp S.subtype),
          (M.dualTwist
            (((ExtCitation.cycloChar p).comp (ExtCitation.primeLocalToGlobal q)).comp S.subtype)).ρ
              s d = d) ∧
        (∀ a : Rep.res S.subtype
            (groupCohomology.ofChar (k := ZMod p)
              ((ExtCitation.cycloChar p).comp (ExtCitation.primeLocalToGlobal q))),
          (Rep.res S.subtype
            (groupCohomology.ofChar (k := ZMod p)
              ((ExtCitation.cycloChar p).comp (ExtCitation.primeLocalToGlobal q)))).ρ s a = a)) := by
  obtain ⟨F₀, hF₀, hF₀U⟩ := hU
  obtain ⟨FM, hFM, hFMfix⟩ :=
    p08_7d1ff633a4_ck_uniform_stabilizer
      ((ExtCitation.primeLocalToGlobal q).comp S.subtype) M hsm
  obtain ⟨FC, hFC, hFCfix⟩ := p08_7d1ff633a4_ck_cyclotomic_kernel (p := p)
  have hfinite : ∀ i : Fin 3, FiniteDimensional ℚ (![F₀, FM, FC] i) := by
    intro i
    fin_cases i
    · exact hF₀
    · exact hFM
    · exact hFC
  obtain ⟨E, hE, hEnormal, hFE, _, _⟩ :=
    p08_7d1ff633a4_normal_refinement ![F₀, FM, FC] hfinite
  have hMfix : ∀ s : S,
      ((ExtCitation.primeLocalToGlobal q).comp S.subtype) s ∈ E.fixingSubgroup →
        ∀ m : M, M.ρ s m = m := by
    intro s hs
    exact hFMfix s (IntermediateField.fixingSubgroup_le (hFE 1) hs)
  refine ⟨E, hE, hEnormal, ?_, ?_⟩
  · intro s hs
    exact hF₀U (IntermediateField.fixingSubgroup_le (hFE 0) hs)
  · intro s hs
    have hχ : (((ExtCitation.cycloChar p).comp
        (ExtCitation.primeLocalToGlobal q)).comp S.subtype) s = 1 :=
      hFCfix _ (IntermediateField.fixingSubgroup_le (hFE 2) hs)
    have hinv : ((ExtCitation.primeLocalToGlobal q).comp S.subtype) s⁻¹ ∈
        E.fixingSubgroup := by
      rw [map_inv]
      exact E.fixingSubgroup.inv_mem hs
    refine ⟨hMfix s hs, ?_, ?_⟩
    · intro d
      rw [Rep.dualTwist_ρ_apply, hχ, Units.val_one, one_smul]
      ext m
      exact congrArg d (hMfix s⁻¹ hinv m)
    · intro a
      change (((((ExtCitation.cycloChar p).comp
        (ExtCitation.primeLocalToGlobal q)).comp S.subtype) s : ZMod p) • a) = a
      rw [hχ, Units.val_one, one_smul]

end Submission
theorem Submission.p08_7d1ff633a4_tp26_low_degree_prism :
    ∀ {X V : Type} [AddCommGroup V] (α β : X → X),
      (∀ F : X → X → V,
        (∀ x y z : X, F y z - F x z + F x y = 0) →
        ∀ x y : X, F (β x) (β y) - F (α x) (α y) =
          F (α y) (β y) - F (α x) (β x)) ∧
      (∀ F : X → X → X → V,
        (∀ w x y z : X, F x y z - F w y z + F w x z - F w x y = 0) →
        let h : X → X → V := fun x y =>
          F (α x) (β x) (β y) - F (α x) (α y) (β y)
        ∀ x y z : X, F (β x) (β y) (β z) - F (α x) (α y) (α z) =
          h y z - h x z + h x y) := by
  intro X V _ α β
  constructor
  · intro F hF x y
    apply sub_eq_zero.mp
    calc
      _ = (F (β x) (β y) - F (α x) (β y) + F (α x) (β x)) -
          (F (α y) (β y) - F (α x) (β y) + F (α x) (α y)) := by abel
      _ = 0 := by simp only [hF, sub_self]
  · intro F hF
    dsimp only
    intro x y z
    apply sub_eq_zero.mp
    calc
      _ = (F (β x) (β y) (β z) - F (α x) (β y) (β z) +
            F (α x) (β x) (β z) - F (α x) (β x) (β y)) -
          (F (α y) (β y) (β z) - F (α x) (β y) (β z) +
            F (α x) (α y) (β z) - F (α x) (α y) (β y)) +
          (F (α y) (α z) (β z) - F (α x) (α z) (β z) +
            F (α x) (α y) (β z) - F (α x) (α y) (α z)) := by abel
      _ = 0 := by simp only [hF, sub_self, add_zero]
theorem Submission.p08_7d1ff633a4_tp26_bilinear_averaging :
    ∀ {k G X Y ι : Type} [Field k] [Group G] [MulAction G X] [MulAction G Y] [Fintype ι] (A B N : Rep.{0} k G) (φ : A →ₗ[k] B →ₗ[k] N), (∀ (s : G) (a : A) (b : B), φ (A.ρ s a) (B.ρ s b) = N.ρ s (φ a b)) → ∀ (t : ι → G) (F : X → A) (Q : Y → B), ((∀ (s : G) (x : X), F (s • x) = A.ρ s (F x)) → ∀ (x : X) (y : Y), (∑ c : ι, N.ρ (t c) (φ (F ((t c)⁻¹ • x)) (Q ((t c)⁻¹ • y)))) = φ (F x) (∑ c : ι, B.ρ (t c) (Q ((t c)⁻¹ • y)))) ∧ ((∀ (s : G) (y : Y), Q (s • y) = B.ρ s (Q y)) → ∀ (x : X) (y : Y), (∑ c : ι, N.ρ (t c) (φ (F ((t c)⁻¹ • x)) (Q ((t c)⁻¹ • y)))) = φ (∑ c : ι, A.ρ (t c) (F ((t c)⁻¹ • x))) (Q y)) := by
  intro k G X Y ι _ _ _ _ _ A B N φ hφ t F Q
  constructor
  · intro hF x y
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro c _
    rw [← hφ, ← hF, smul_inv_smul]
  · intro hQ x y
    rw [map_sum, LinearMap.sum_apply]
    apply Finset.sum_congr rfl
    intro c _
    rw [← hφ, ← hQ, smul_inv_smul]

theorem Submission.p08_7d1ff633a4_cp11_level_cocycle :
    ∀ {k G : Type} [Field k] [Group G] (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (A B N : Rep.{0} k G) (E₀ : IntermediateField ℚ (AlgebraicClosure ℚ)), FiniteDimensional ℚ E₀ → (∀ s : G, r s ∈ E₀.fixingSubgroup → ∀ b : B, B.ρ s b = b) → ∀ φ : A →ₗ[k] B →ₗ[k] N, (∀ (s : G) (a : A) (b : B), φ (A.ρ s a) (B.ρ s b) = N.ρ s (φ a b)) → ∀ (f : groupCohomology.cocycles₁ A) (g : groupCohomology.cocycles₁ B), groupCohomology.IsLevelConstant₁ r (⇑f) → groupCohomology.IsLevelConstant₁ r (⇑g) → groupCohomology.cupCochain φ (⇑f) (⇑g) ∈ groupCohomology.levelCocycles₂ r N := by
  intro k G _ _ r A B N E₀ hE₀ hB φ hφ f g hf hg
  rw [mem_levelCocycles₂_iff]
  constructor
  · rw [← cup_coe φ hφ f g]
    exact (cup φ hφ f g).property
  · obtain ⟨Ff, hFf, hf⟩ := hf
    obtain ⟨Fg, hFg, hg⟩ := hg
    let := hE₀
    let := hFf
    let := hFg
    letI := hE₀
    letI := hFf
    letI := hFg
    refine ⟨(E₀ ⊔ Ff) ⊔ Fg, inferInstance, ?_⟩
    intro s t h l hh hl
    have hh₀ : r h ∈ E₀.fixingSubgroup :=
      IntermediateField.fixingSubgroup_antitone
        (le_sup_left.trans le_sup_left : E₀ ≤ (E₀ ⊔ Ff) ⊔ Fg) hh
    have hhf : r h ∈ Ff.fixingSubgroup :=
      IntermediateField.fixingSubgroup_antitone
        (le_sup_right.trans le_sup_left : Ff ≤ (E₀ ⊔ Ff) ⊔ Fg) hh
    have hlg : r l ∈ Fg.fixingSubgroup :=
      IntermediateField.fixingSubgroup_antitone le_sup_right hl
    simp only [cupCochain_apply]
    rw [hf s h hhf, hg t l hlg, Rep.ρ_mul]
    change φ (f s) (B.ρ s (B.ρ h (g t))) = φ (f s) (B.ρ s (g t))
    rw [hB h hh₀]


/-- The cup product of level one-cocycles descends to the frozen continuous H¹ images. -/
theorem Submission.p08_7d1ff633a4_tt26_cp_one_one :
    ∀ {k G : Type} [Field k] [Group G]
      (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
      (A B N : Rep.{0} k G) (E₀ : IntermediateField ℚ (AlgebraicClosure ℚ)),
      FiniteDimensional ℚ E₀ →
      (∀ s : G, r s ∈ E₀.fixingSubgroup → ∀ b : B, B.ρ s b = b) →
      ∀ φ : A →ₗ[k] B →ₗ[k] N,
      (∀ (s : G) (a : A) (b : B), φ (A.ρ s a) (B.ρ s b) = N.ρ s (φ a b)) →
      ∃ P : continuousH1 r A →ₗ[k] continuousH1 r B →ₗ[k] continuousH2 r N,
        ∀ (f : cocycles₁ A) (hf : IsLevelConstant₁ r (⇑f))
          (g : cocycles₁ B) (hg : IsLevelConstant₁ r (⇑g)),
        ∃ e : levelCocycles₂ r N,
          (∀ st : G × G, (e : G × G → N) st = cupCochain φ (⇑f) (⇑g) st) ∧
          P ⟨(H1π A).hom f, H1π_mem_continuousH1 r A hf⟩
            ⟨(H1π B).hom g, H1π_mem_continuousH1 r B hg⟩ = continuousH2π r N e := by
  classical
  intro k G _ _ r A B N E₀ hE₀ hB φ hφ
  -- The child supplies an actual level two-cocycle for each pair of representatives.
  let C : levelCocycles₁ r A →ₗ[k] levelCocycles₁ r B →ₗ[k] levelCocycles₂ r N :=
    LinearMap.mk₂ k
      (fun f g => ⟨cupCochain φ (⇑f.val) (⇑g.val),
        Submission.p08_7d1ff633a4_cp11_level_cocycle r A B N E₀ hE₀ hB φ hφ
          f.val g.val f.property g.property⟩)
      (fun f f' g => by
        apply Subtype.ext
        funext st
        change φ (f.val st.1 + f'.val st.1) (B.ρ st.1 (g.val st.2)) =
          φ (f.val st.1) (B.ρ st.1 (g.val st.2)) +
            φ (f'.val st.1) (B.ρ st.1 (g.val st.2))
        rw [map_add, LinearMap.add_apply])
      (fun c f g => by
        apply Subtype.ext
        funext st
        change φ (c • f.val st.1) (B.ρ st.1 (g.val st.2)) =
          c • φ (f.val st.1) (B.ρ st.1 (g.val st.2))
        rw [map_smul, LinearMap.smul_apply])
      (fun f g g' => by
        apply Subtype.ext
        funext st
        change φ (f.val st.1) (B.ρ st.1 (g.val st.2 + g'.val st.2)) =
          φ (f.val st.1) (B.ρ st.1 (g.val st.2)) +
            φ (f.val st.1) (B.ρ st.1 (g'.val st.2))
        rw [map_add, map_add])
      (fun c f g => by
        apply Subtype.ext
        funext st
        change φ (f.val st.1) (B.ρ st.1 (c • g.val st.2)) =
          c • φ (f.val st.1) (B.ρ st.1 (g.val st.2))
        rw [map_smul, map_smul])
  let Q : levelCocycles₁ r A →ₗ[k] levelCocycles₁ r B →ₗ[k] continuousH2 r N :=
    C.compr₂ (continuousH2π r N)
  -- The image definition gives a surjective projection from level cocycles.
  let π (M : Rep.{0} k G) : levelCocycles₁ r M →ₗ[k] continuousH1 r M :=
    ((H1π M).hom.comp (levelCocycles₁ r M).subtype).codRestrict
      (continuousH1 r M) (fun f => H1π_mem_continuousH1 r M f.property)
  have hπ (M : Rep.{0} k G) : Function.Surjective (π M) := by
    intro x
    obtain ⟨f, hf, hfx⟩ := (mem_continuousH1_iff r M x.val).mp x.property
    exact ⟨⟨f, hf⟩, Subtype.ext hfx⟩
  -- The two boundary children kill the kernels in the respective variables.
  have hleft : LinearMap.ker (π A) ≤ LinearMap.ker Q := by
    intro f hf
    apply LinearMap.mem_ker.mpr
    ext g
    change continuousH2π r N (C f g) = 0
    apply (continuousH2π_eq_zero_iff r N (C f g)).mpr
    have hf0 : (H1π A).hom f.val = 0 :=
      congrArg Subtype.val (LinearMap.mem_ker.mp hf)
    obtain ⟨a, ha⟩ := (H1π_eq_zero_iff f.val).mp hf0
    have hfa : (⇑f.val) = fun s : G => A.ρ s a - a := by
      funext s
      rw [← ha, d₀₁_hom_apply]
    change cupCochain φ (⇑f.val) (⇑g.val) ∈ levelCoboundaries₂ r N
    rw [hfa]
    exact Submission.p08_7d1ff633a4_cp11_left_level_boundary r A B N φ hφ
      a g.val g.property
  have hright : LinearMap.ker (π B) ≤ LinearMap.ker Q.flip := by
    intro g hg
    apply LinearMap.mem_ker.mpr
    ext f
    change continuousH2π r N (C f g) = 0
    apply (continuousH2π_eq_zero_iff r N (C f g)).mpr
    have hg0 : (H1π B).hom g.val = 0 :=
      congrArg Subtype.val (LinearMap.mem_ker.mp hg)
    obtain ⟨b, hb⟩ := (H1π_eq_zero_iff g.val).mp hg0
    have hgb : (⇑g.val) = fun t : G => B.ρ t b - b := by
      funext t
      rw [← hb, d₀₁_hom_apply]
    change cupCochain φ (⇑f.val) (⇑g.val) ∈ levelCoboundaries₂ r N
    rw [hgb]
    exact Submission.p08_7d1ff633a4_cp11_right_level_boundary r A B N E₀ hE₀ hB
      φ hφ f.val b f.property
  -- Kernel vanishing makes Q independent of either level representative.
  have hQl (f f' : levelCocycles₁ r A) (g : levelCocycles₁ r B)
      (h : π A f = π A f') : Q f g = Q f' g := by
    have hz : Q (f + (-1 : k) • f') = 0 := hleft (by
      rw [LinearMap.mem_ker, map_add, map_smul, h, neg_one_smul, add_neg_cancel])
    have he := LinearMap.congr_fun hz g
    simpa only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      neg_one_smul, LinearMap.zero_apply, ← sub_eq_add_neg, sub_eq_zero] using he
  have hQr (f : levelCocycles₁ r A) (g g' : levelCocycles₁ r B)
      (h : π B g = π B g') : Q f g = Q f g' := by
    have hz : Q.flip (g + (-1 : k) • g') = 0 := hright (by
      rw [LinearMap.mem_ker, map_add, map_smul, h, neg_one_smul, add_neg_cancel])
    have he := LinearMap.congr_fun hz f
    simpa only [LinearMap.flip_apply, map_add, map_smul, LinearMap.add_apply,
      LinearMap.smul_apply, neg_one_smul, LinearMap.zero_apply,
      ← sub_eq_add_neg, sub_eq_zero] using he
  let R (M : Rep.{0} k G) (x : continuousH1 r M) : levelCocycles₁ r M :=
    (hπ M x).choose
  have hR (M : Rep.{0} k G) (x : continuousH1 r M) : π M (R M x) = x :=
    (hπ M x).choose_spec
  let P : continuousH1 r A →ₗ[k] continuousH1 r B →ₗ[k] continuousH2 r N :=
    LinearMap.mk₂ k (fun x y => Q (R A x) (R B y))
      (fun x x' y => by
        calc
          Q (R A (x + x')) (R B y) = Q (R A x + R A x') (R B y) :=
            hQl _ _ _ (by rw [hR, map_add, hR, hR])
          _ = Q (R A x) (R B y) + Q (R A x') (R B y) := by
            rw [map_add, LinearMap.add_apply])
      (fun c x y => by
        calc
          Q (R A (c • x)) (R B y) = Q (c • R A x) (R B y) :=
            hQl _ _ _ (by rw [hR, map_smul, hR])
          _ = c • Q (R A x) (R B y) := by rw [map_smul, LinearMap.smul_apply])
      (fun x y y' => by
        calc
          Q (R A x) (R B (y + y')) = Q (R A x) (R B y + R B y') :=
            hQr _ _ _ (by rw [hR, map_add, hR, hR])
          _ = Q (R A x) (R B y) + Q (R A x) (R B y') := by rw [map_add])
      (fun c x y => by
        calc
          Q (R A x) (R B (c • y)) = Q (R A x) (c • R B y) :=
            hQr _ _ _ (by rw [hR, map_smul, hR])
          _ = c • Q (R A x) (R B y) := by rw [map_smul])
  refine ⟨P, ?_⟩
  intro f hf g hg
  refine ⟨C ⟨f, hf⟩ ⟨g, hg⟩, fun _ => rfl, ?_⟩
  change Q (R A (π A ⟨f, hf⟩)) (R B (π B ⟨g, hg⟩)) = Q ⟨f, hf⟩ ⟨g, hg⟩
  exact (hQl _ _ _ (hR A (π A ⟨f, hf⟩))).trans
    (hQr _ _ _ (hR B (π B ⟨g, hg⟩)))
theorem Submission.p08_7d1ff633a4_tt26_cup_pairings :
    ∀ {k G : Type} [Field k] [Group G]
      (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
      (A B N : Rep.{0} k G) (E₀ : IntermediateField ℚ (AlgebraicClosure ℚ)),
      FiniteDimensional ℚ E₀ →
      (∀ g : G, r g ∈ E₀.fixingSubgroup → ∀ b : B, B.ρ g b = b) →
      ∀ φ : A →ₗ[k] B →ₗ[k] N,
      (∀ (g : G) (a : A) (b : B), φ (A.ρ g a) (B.ρ g b) = N.ρ g (φ a b)) →
      let X : Fin 3 → ModuleCat k :=
        ![ModuleCat.of k A.ρ.invariants, ModuleCat.of k (continuousH1 r A),
          ModuleCat.of k (continuousH2 r A)];
      let Y : Fin 3 → ModuleCat k :=
        ![ModuleCat.of k (continuousH2 r B), ModuleCat.of k (continuousH1 r B),
          ModuleCat.of k B.ρ.invariants];
      ∃ (P : ∀ i : Fin 3, X i →ₗ[k] Y i →ₗ[k] continuousH2 r N),
        ((∀ (m : A.ρ.invariants) (z : levelCocycles₂ r B),
          ∃ e : levelCocycles₂ r N,
            (∀ st : G × G, (e : G × G → N) st = φ (m : A) ((z : G × G → B) st)) ∧
              P 0 m (continuousH2π r B z) = continuousH2π r N e) ∧
        (∀ (f : cocycles₁ A) (hf : IsLevelConstant₁ r (⇑f))
          (g : cocycles₁ B) (hg : IsLevelConstant₁ r (⇑g)),
          ∃ e : levelCocycles₂ r N,
            (∀ st : G × G, (e : G × G → N) st = cupCochain φ (⇑f) (⇑g) st) ∧
              P 1 ⟨(H1π A).hom f, H1π_mem_continuousH1 r A hf⟩
                ⟨(H1π B).hom g, H1π_mem_continuousH1 r B hg⟩ = continuousH2π r N e) ∧
        (∀ (z : levelCocycles₂ r A) (d : B.ρ.invariants),
          ∃ e : levelCocycles₂ r N,
            (∀ st : G × G, (e : G × G → N) st = φ ((z : G × G → A) st) (d : B)) ∧
              P 2 (continuousH2π r A z) d = continuousH2π r N e)) := by
  intro k G _ _ r A B N E₀ hE₀ hB φ hφ
  obtain ⟨P₀, hP₀⟩ := Submission.p08_7d1ff633a4_tt26_cp_zero_two r A B N φ hφ
  obtain ⟨P₁, hP₁⟩ :=
    Submission.p08_7d1ff633a4_tt26_cp_one_one r A B N E₀ hE₀ hB φ hφ
  -- Reverse both inputs to the endpoint child to obtain the (2,0) pairing.
  obtain ⟨P₂, hP₂⟩ :=
    Submission.p08_7d1ff633a4_tt26_cp_zero_two r B A N φ.flip (fun s b a => hφ s a b)
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Fin.cases P₀ (Fin.cases P₁ (Fin.cases P₂.flip (fun i => Fin.elim0 i)))
  · exact hP₀
  · exact hP₁
  · intro z d
    exact hP₂ d z
theorem Submission.p08_7d1ff633a4_transfer_theta :
    ∀ {k G : Type} [Field k] [Group G]
      (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
      (H : Subgroup G) [H.FiniteIndex] (A B N : Rep.{0} k G)
      (E₀ : IntermediateField ℚ (AlgebraicClosure ℚ)),
      FiniteDimensional ℚ E₀ → Normal ℚ E₀ → E₀.fixingSubgroup.comap r ≤ H →
      (∀ g : G, r g ∈ E₀.fixingSubgroup → ∀ a : A, A.ρ g a = a) →
      (∀ g : G, r g ∈ E₀.fixingSubgroup → ∀ b : B, B.ρ g b = b) →
      (∀ g : G, r g ∈ E₀.fixingSubgroup → ∀ z : N, N.ρ g z = z) →
      ∀ φ : A →ₗ[k] B →ₗ[k] N,
      (∀ (g : G) (a : A) (b : B), φ (A.ρ g a) (B.ρ g b) = N.ρ g (φ a b)) →
      let rH := r.comp H.subtype
      let AH := Rep.res H.subtype A
      let BH := Rep.res H.subtype B
      let NH := Rep.res H.subtype N
      let φH : AH →ₗ[k] BH →ₗ[k] NH := φ
      let X : Fin 3 → ModuleCat k :=
        ![ModuleCat.of k A.ρ.invariants,
          ModuleCat.of k (groupCohomology.continuousH1 r A),
          ModuleCat.of k (groupCohomology.continuousH2 r A)]
      let Y : Fin 3 → ModuleCat k :=
        ![ModuleCat.of k (groupCohomology.continuousH2 r B),
          ModuleCat.of k (groupCohomology.continuousH1 r B), ModuleCat.of k B.ρ.invariants]
      let XH : Fin 3 → ModuleCat k :=
        ![ModuleCat.of k AH.ρ.invariants,
          ModuleCat.of k (groupCohomology.continuousH1 rH AH),
          ModuleCat.of k (groupCohomology.continuousH2 rH AH)]
      let YH : Fin 3 → ModuleCat k :=
        ![ModuleCat.of k (groupCohomology.continuousH2 rH BH),
          ModuleCat.of k (groupCohomology.continuousH1 rH BH), ModuleCat.of k BH.ρ.invariants]
      ∃ (RX : ∀ i : Fin 3, X i →ₗ[k] XH i) (CX : ∀ i : Fin 3, XH i →ₗ[k] X i)
        (RY : ∀ i : Fin 3, Y i →ₗ[k] YH i) (CY : ∀ i : Fin 3, YH i →ₗ[k] Y i)
        (RN : groupCohomology.continuousH2 r N →ₗ[k] groupCohomology.continuousH2 rH NH)
        (CN : groupCohomology.continuousH2 rH NH →ₗ[k] groupCohomology.continuousH2 r N),
        (∀ (i : Fin 3) (x : X i), CX i (RX i x) = (H.index : k) • x) ∧
        (∀ (i : Fin 3) (y : Y i), CY i (RY i y) = (H.index : k) • y) ∧
        (∀ z : groupCohomology.continuousH2 r N, CN (RN z) = (H.index : k) • z) ∧
        ∀ ℓ : groupCohomology.continuousH2 r N →ₗ[k] k,
        ∃ (Θ : ∀ i : Fin 3, X i →ₗ[k] Module.Dual k (Y i))
          (ΘH : ∀ i : Fin 3, XH i →ₗ[k] Module.Dual k (YH i)),
          (groupCohomology.IsTheta0 r φ ℓ (Θ 0) ∧
            groupCohomology.IsTheta1 r φ ℓ (Θ 1) ∧
            groupCohomology.IsTheta2 r φ ℓ (Θ 2)) ∧
          (groupCohomology.IsTheta0 rH φH (ℓ.comp CN) (ΘH 0) ∧
            groupCohomology.IsTheta1 rH φH (ℓ.comp CN) (ΘH 1) ∧
            groupCohomology.IsTheta2 rH φH (ℓ.comp CN) (ΘH 2)) ∧
          (∀ Ψ : ∀ i : Fin 3, X i →ₗ[k] Module.Dual k (Y i),
            (groupCohomology.IsTheta0 r φ ℓ (Ψ 0) ∧
              groupCohomology.IsTheta1 r φ ℓ (Ψ 1) ∧
              groupCohomology.IsTheta2 r φ ℓ (Ψ 2)) → ∀ i : Fin 3, Ψ i = Θ i) ∧
          (∀ (i : Fin 3) (x : X i) (y : YH i), ΘH i (RX i x) y = Θ i x (CY i y)) ∧
          (∀ (i : Fin 3) (x : XH i) (y : Y i), ΘH i x (RY i y) = Θ i (CX i x) y) := by
  intro k G _ _ r H _ A B N E₀ hE₀ hnormal hKH hA hB hN φ hφ
  dsimp only
  let rH := r.comp H.subtype
  let AH := Rep.res H.subtype A
  let BH := Rep.res H.subtype B
  let NH := Rep.res H.subtype N
  let φH : AH →ₗ[k] BH →ₗ[k] NH := φ
  have hBH : ∀ g : H, rH g ∈ E₀.fixingSubgroup → ∀ b : BH, BH.ρ g b = b := by
    intro g hg b
    exact hB g hg b
  have hφH : ∀ (g : H) (a : AH) (b : BH),
      φH (AH.ρ g a) (BH.ρ g b) = NH.ρ g (φH a b) := by
    intro g a b
    exact hφ g a b
  -- Choose the cup pairings and transfer maps before choosing the functional.
  obtain ⟨P, hP⟩ := Submission.p08_7d1ff633a4_tt26_cup_pairings
    r A B N E₀ hE₀ hB φ hφ
  obtain ⟨PH, hPH⟩ := Submission.p08_7d1ff633a4_tt26_cup_pairings
    rH AH BH NH E₀ hE₀ hBH φH hφH
  obtain ⟨RX, CX, RY, CY, RN, CN, hRX, hRY, hRN, hleft, hright⟩ :=
    Submission.p08_7d1ff633a4_tt26_transfer_projection
      r H A B N E₀ hE₀ hnormal hKH hA hB hN φ hφ P PH hP hPH
  refine ⟨RX, CX, RY, CY, RN, CN, hRX, hRY, hRN, ?_⟩
  intro ℓ
  obtain ⟨Θ, hΘ, hΘeval, hunique⟩ := Submission.p08_7d1ff633a4_tt26_theta_from_pairings
    r A B N φ P hP ℓ
  obtain ⟨ΘH, hΘH, hΘHeval, _⟩ := Submission.p08_7d1ff633a4_tt26_theta_from_pairings
    rH AH BH NH φH PH hPH (ℓ.comp CN)
  refine ⟨Θ, ΘH, hΘ, hΘH, hunique, ?_, ?_⟩
  · intro i x y
    calc
      ΘH i (RX i x) y = ℓ (CN (PH i (RX i x) y)) := hΘHeval i (RX i x) y
      _ = ℓ (P i x (CY i y)) := congrArg ℓ (hleft i x y)
      _ = Θ i x (CY i y) := (hΘeval i x (CY i y)).symm
  · intro i x y
    calc
      ΘH i x (RY i y) = ℓ (CN (PH i x (RY i y))) := hΘHeval i x (RY i y)
      _ = ℓ (P i (CX i x) y) := congrArg ℓ (hright i x y)
      _ = Θ i (CX i x) y := (hΘeval i (CX i x) y).symm
theorem Submission.p08_7d1ff633a4_cp11_left_level_boundary :
    ∀ {k G : Type} [Field k] [Group G] (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (A B N : Rep.{0} k G) (φ : A →ₗ[k] B →ₗ[k] N), (∀ (s : G) (a : A) (b : B), φ (A.ρ s a) (B.ρ s b) = N.ρ s (φ a b)) → ∀ (a : A) (g : groupCohomology.cocycles₁ B), groupCohomology.IsLevelConstant₁ r (⇑g) → groupCohomology.cupCochain φ (fun s : G => A.ρ s a - a) (⇑g) ∈ groupCohomology.levelCoboundaries₂ r N := by
  intro k G _ _ r A B N φ hφ a g hg
  apply (groupCohomology.mem_levelCoboundaries₂_iff r N _).2
  refine ⟨fun t => φ a (g t), hg.comp (φ a), ?_⟩
  funext p
  obtain ⟨s, t⟩ := p
  rw [groupCohomology.d₁₂_hom_apply]
  change N.ρ s (φ a (g t)) - φ a (g (s * t)) + φ a (g s) =
    φ (A.ρ s a - a) (B.ρ s (g t))
  rw [(groupCohomology.mem_cocycles₁_iff (⇑g)).1 g.2 s t, ← hφ s a (g t)]
  simp only [map_add, map_sub, LinearMap.sub_apply]
  abel
theorem Submission.p08_7d1ff633a4_cp11_right_level_boundary :
    ∀ {k G : Type} [Field k] [Group G] (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (A B N : Rep.{0} k G) (E₀ : IntermediateField ℚ (AlgebraicClosure ℚ)), FiniteDimensional ℚ E₀ → (∀ s : G, r s ∈ E₀.fixingSubgroup → ∀ b : B, B.ρ s b = b) → ∀ φ : A →ₗ[k] B →ₗ[k] N, (∀ (s : G) (a : A) (b : B), φ (A.ρ s a) (B.ρ s b) = N.ρ s (φ a b)) → ∀ (f : groupCohomology.cocycles₁ A) (b : B), groupCohomology.IsLevelConstant₁ r (⇑f) → groupCohomology.cupCochain φ (⇑f) (fun t : G => B.ρ t b - b) ∈ groupCohomology.levelCoboundaries₂ r N := by
  intro k G _ _ r A B N E₀ hE₀ hB φ hφ f b hf
  obtain ⟨Ff, hFf, hf⟩ := hf
  let := hE₀
  let := hFf
  apply (groupCohomology.mem_levelCoboundaries₂_iff r N _).2
  refine ⟨fun s => -(φ (f s) (B.ρ s b)), ?_, ?_⟩
  · refine ⟨E₀ ⊔ Ff, inferInstance, ?_⟩
    intro s t ht
    dsimp only
    rw [hf s t (IntermediateField.fixingSubgroup_antitone le_sup_right ht),
      Rep.ρ_mul, LinearMap.comp_apply,
      hB t (IntermediateField.fixingSubgroup_antitone le_sup_left ht) b]
  · funext p
    obtain ⟨s, t⟩ := p
    rw [groupCohomology.d₁₂_hom_apply]
    change N.ρ s (-(φ (f t) (B.ρ t b))) -
        (-(φ (f (s * t)) (B.ρ (s * t) b))) + (-(φ (f s) (B.ρ s b))) =
      φ (f s) (B.ρ s (B.ρ t b - b))
    rw [map_neg, (groupCohomology.mem_cocycles₁_iff (⇑f)).1 f.2 s t,
      ← hφ s (f t) (B.ρ t b), Rep.ρ_mul, LinearMap.comp_apply]
    simp only [map_add, map_sub, LinearMap.add_apply]
    abel


/-- The cup product of level one-cocycles descends to the frozen continuous H¹ images. -/
theorem Submission.p08_7d1ff633a4_tt26_cp_one_one :
    ∀ {k G : Type} [Field k] [Group G]
      (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
      (A B N : Rep.{0} k G) (E₀ : IntermediateField ℚ (AlgebraicClosure ℚ)),
      FiniteDimensional ℚ E₀ →
      (∀ s : G, r s ∈ E₀.fixingSubgroup → ∀ b : B, B.ρ s b = b) →
      ∀ φ : A →ₗ[k] B →ₗ[k] N,
      (∀ (s : G) (a : A) (b : B), φ (A.ρ s a) (B.ρ s b) = N.ρ s (φ a b)) →
      ∃ P : continuousH1 r A →ₗ[k] continuousH1 r B →ₗ[k] continuousH2 r N,
        ∀ (f : cocycles₁ A) (hf : IsLevelConstant₁ r (⇑f))
          (g : cocycles₁ B) (hg : IsLevelConstant₁ r (⇑g)),
        ∃ e : levelCocycles₂ r N,
          (∀ st : G × G, (e : G × G → N) st = cupCochain φ (⇑f) (⇑g) st) ∧
          P ⟨(H1π A).hom f, H1π_mem_continuousH1 r A hf⟩
            ⟨(H1π B).hom g, H1π_mem_continuousH1 r B hg⟩ = continuousH2π r N e := by
  classical
  intro k G _ _ r A B N E₀ hE₀ hB φ hφ
  -- The child supplies an actual level two-cocycle for each pair of representatives.
  let C : levelCocycles₁ r A →ₗ[k] levelCocycles₁ r B →ₗ[k] levelCocycles₂ r N :=
    LinearMap.mk₂ k
      (fun f g => ⟨cupCochain φ (⇑f.val) (⇑g.val),
        Submission.p08_7d1ff633a4_cp11_level_cocycle r A B N E₀ hE₀ hB φ hφ
          f.val g.val f.property g.property⟩)
      (fun f f' g => by
        apply Subtype.ext
        funext st
        change φ (f.val st.1 + f'.val st.1) (B.ρ st.1 (g.val st.2)) =
          φ (f.val st.1) (B.ρ st.1 (g.val st.2)) +
            φ (f'.val st.1) (B.ρ st.1 (g.val st.2))
        rw [map_add, LinearMap.add_apply])
      (fun c f g => by
        apply Subtype.ext
        funext st
        change φ (c • f.val st.1) (B.ρ st.1 (g.val st.2)) =
          c • φ (f.val st.1) (B.ρ st.1 (g.val st.2))
        rw [map_smul, LinearMap.smul_apply])
      (fun f g g' => by
        apply Subtype.ext
        funext st
        change φ (f.val st.1) (B.ρ st.1 (g.val st.2 + g'.val st.2)) =
          φ (f.val st.1) (B.ρ st.1 (g.val st.2)) +
            φ (f.val st.1) (B.ρ st.1 (g'.val st.2))
        rw [map_add, map_add])
      (fun c f g => by
        apply Subtype.ext
        funext st
        change φ (f.val st.1) (B.ρ st.1 (c • g.val st.2)) =
          c • φ (f.val st.1) (B.ρ st.1 (g.val st.2))
        rw [map_smul, map_smul])
  let Q : levelCocycles₁ r A →ₗ[k] levelCocycles₁ r B →ₗ[k] continuousH2 r N :=
    C.compr₂ (continuousH2π r N)
  -- The image definition gives a surjective projection from level cocycles.
  let π (M : Rep.{0} k G) : levelCocycles₁ r M →ₗ[k] continuousH1 r M :=
    ((H1π M).hom.comp (levelCocycles₁ r M).subtype).codRestrict
      (continuousH1 r M) (fun f => H1π_mem_continuousH1 r M f.property)
  have hπ (M : Rep.{0} k G) : Function.Surjective (π M) := by
    intro x
    obtain ⟨f, hf, hfx⟩ := (mem_continuousH1_iff r M x.val).mp x.property
    exact ⟨⟨f, hf⟩, Subtype.ext hfx⟩
  -- The two boundary children kill the kernels in the respective variables.
  have hleft : LinearMap.ker (π A) ≤ LinearMap.ker Q := by
    intro f hf
    apply LinearMap.mem_ker.mpr
    ext g
    change continuousH2π r N (C f g) = 0
    apply (continuousH2π_eq_zero_iff r N (C f g)).mpr
    have hf0 : (H1π A).hom f.val = 0 :=
      congrArg Subtype.val (LinearMap.mem_ker.mp hf)
    obtain ⟨a, ha⟩ := (H1π_eq_zero_iff f.val).mp hf0
    have hfa : (⇑f.val) = fun s : G => A.ρ s a - a := by
      funext s
      rw [← ha, d₀₁_hom_apply]
    change cupCochain φ (⇑f.val) (⇑g.val) ∈ levelCoboundaries₂ r N
    rw [hfa]
    exact Submission.p08_7d1ff633a4_cp11_left_level_boundary r A B N φ hφ
      a g.val g.property
  have hright : LinearMap.ker (π B) ≤ LinearMap.ker Q.flip := by
    intro g hg
    apply LinearMap.mem_ker.mpr
    ext f
    change continuousH2π r N (C f g) = 0
    apply (continuousH2π_eq_zero_iff r N (C f g)).mpr
    have hg0 : (H1π B).hom g.val = 0 :=
      congrArg Subtype.val (LinearMap.mem_ker.mp hg)
    obtain ⟨b, hb⟩ := (H1π_eq_zero_iff g.val).mp hg0
    have hgb : (⇑g.val) = fun t : G => B.ρ t b - b := by
      funext t
      rw [← hb, d₀₁_hom_apply]
    change cupCochain φ (⇑f.val) (⇑g.val) ∈ levelCoboundaries₂ r N
    rw [hgb]
    exact Submission.p08_7d1ff633a4_cp11_right_level_boundary r A B N E₀ hE₀ hB
      φ hφ f.val b f.property
  -- Kernel vanishing makes Q independent of either level representative.
  have hQl (f f' : levelCocycles₁ r A) (g : levelCocycles₁ r B)
      (h : π A f = π A f') : Q f g = Q f' g := by
    have hz : Q (f + (-1 : k) • f') = 0 := hleft (by
      rw [LinearMap.mem_ker, map_add, map_smul, h, neg_one_smul, add_neg_cancel])
    have he := LinearMap.congr_fun hz g
    simpa only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      neg_one_smul, LinearMap.zero_apply, ← sub_eq_add_neg, sub_eq_zero] using he
  have hQr (f : levelCocycles₁ r A) (g g' : levelCocycles₁ r B)
      (h : π B g = π B g') : Q f g = Q f g' := by
    have hz : Q.flip (g + (-1 : k) • g') = 0 := hright (by
      rw [LinearMap.mem_ker, map_add, map_smul, h, neg_one_smul, add_neg_cancel])
    have he := LinearMap.congr_fun hz f
    simpa only [LinearMap.flip_apply, map_add, map_smul, LinearMap.add_apply,
      LinearMap.smul_apply, neg_one_smul, LinearMap.zero_apply,
      ← sub_eq_add_neg, sub_eq_zero] using he
  let R (M : Rep.{0} k G) (x : continuousH1 r M) : levelCocycles₁ r M :=
    (hπ M x).choose
  have hR (M : Rep.{0} k G) (x : continuousH1 r M) : π M (R M x) = x :=
    (hπ M x).choose_spec
  let P : continuousH1 r A →ₗ[k] continuousH1 r B →ₗ[k] continuousH2 r N :=
    LinearMap.mk₂ k (fun x y => Q (R A x) (R B y))
      (fun x x' y => by
        calc
          Q (R A (x + x')) (R B y) = Q (R A x + R A x') (R B y) :=
            hQl _ _ _ (by rw [hR, map_add, hR, hR])
          _ = Q (R A x) (R B y) + Q (R A x') (R B y) := by
            rw [map_add, LinearMap.add_apply])
      (fun c x y => by
        calc
          Q (R A (c • x)) (R B y) = Q (c • R A x) (R B y) :=
            hQl _ _ _ (by rw [hR, map_smul, hR])
          _ = c • Q (R A x) (R B y) := by rw [map_smul, LinearMap.smul_apply])
      (fun x y y' => by
        calc
          Q (R A x) (R B (y + y')) = Q (R A x) (R B y + R B y') :=
            hQr _ _ _ (by rw [hR, map_add, hR, hR])
          _ = Q (R A x) (R B y) + Q (R A x) (R B y') := by rw [map_add])
      (fun c x y => by
        calc
          Q (R A x) (R B (c • y)) = Q (R A x) (c • R B y) :=
            hQr _ _ _ (by rw [hR, map_smul, hR])
          _ = c • Q (R A x) (R B y) := by rw [map_smul])
  refine ⟨P, ?_⟩
  intro f hf g hg
  refine ⟨C ⟨f, hf⟩ ⟨g, hg⟩, fun _ => rfl, ?_⟩
  change Q (R A (π A ⟨f, hf⟩)) (R B (π B ⟨g, hg⟩)) = Q ⟨f, hf⟩ ⟨g, hg⟩
  exact (hQl _ _ _ (hR A (π A ⟨f, hf⟩))).trans
    (hQr _ _ _ (hR B (π B ⟨g, hg⟩)))


theorem Submission.p08_7d1ff633a4_tt26_cup_pairings :
    ∀ {k G : Type} [Field k] [Group G]
      (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
      (A B N : Rep.{0} k G) (E₀ : IntermediateField ℚ (AlgebraicClosure ℚ)),
      FiniteDimensional ℚ E₀ →
      (∀ g : G, r g ∈ E₀.fixingSubgroup → ∀ b : B, B.ρ g b = b) →
      ∀ φ : A →ₗ[k] B →ₗ[k] N,
      (∀ (g : G) (a : A) (b : B), φ (A.ρ g a) (B.ρ g b) = N.ρ g (φ a b)) →
      let X : Fin 3 → ModuleCat k :=
        ![ModuleCat.of k A.ρ.invariants, ModuleCat.of k (continuousH1 r A),
          ModuleCat.of k (continuousH2 r A)];
      let Y : Fin 3 → ModuleCat k :=
        ![ModuleCat.of k (continuousH2 r B), ModuleCat.of k (continuousH1 r B),
          ModuleCat.of k B.ρ.invariants];
      ∃ (P : ∀ i : Fin 3, X i →ₗ[k] Y i →ₗ[k] continuousH2 r N),
        ((∀ (m : A.ρ.invariants) (z : levelCocycles₂ r B),
          ∃ e : levelCocycles₂ r N,
            (∀ st : G × G, (e : G × G → N) st = φ (m : A) ((z : G × G → B) st)) ∧
              P 0 m (continuousH2π r B z) = continuousH2π r N e) ∧
        (∀ (f : cocycles₁ A) (hf : IsLevelConstant₁ r (⇑f))
          (g : cocycles₁ B) (hg : IsLevelConstant₁ r (⇑g)),
          ∃ e : levelCocycles₂ r N,
            (∀ st : G × G, (e : G × G → N) st = cupCochain φ (⇑f) (⇑g) st) ∧
              P 1 ⟨(H1π A).hom f, H1π_mem_continuousH1 r A hf⟩
                ⟨(H1π B).hom g, H1π_mem_continuousH1 r B hg⟩ = continuousH2π r N e) ∧
        (∀ (z : levelCocycles₂ r A) (d : B.ρ.invariants),
          ∃ e : levelCocycles₂ r N,
            (∀ st : G × G, (e : G × G → N) st = φ ((z : G × G → A) st) (d : B)) ∧
              P 2 (continuousH2π r A z) d = continuousH2π r N e)) := by
  intro k G _ _ r A B N E₀ hE₀ hB φ hφ
  obtain ⟨P₀, hP₀⟩ := Submission.p08_7d1ff633a4_tt26_cp_zero_two r A B N φ hφ
  obtain ⟨P₁, hP₁⟩ :=
    Submission.p08_7d1ff633a4_tt26_cp_one_one r A B N E₀ hE₀ hB φ hφ
  -- Reverse both inputs to the endpoint child to obtain the (2,0) pairing.
  obtain ⟨P₂, hP₂⟩ :=
    Submission.p08_7d1ff633a4_tt26_cp_zero_two r B A N φ.flip (fun s b a => hφ s a b)
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Fin.cases P₀ (Fin.cases P₁ (Fin.cases P₂.flip (fun i => Fin.elim0 i)))
  · exact hP₀
  · exact hP₁
  · intro z d
    exact hP₂ d z
theorem Submission.p08_7d1ff633a4_tp26_normal_level_retraction :
    ∀ {G : Type} [Group G] (H : Subgroup G), ∃ a : G → H,
      (∀ h : H, a (h : G) = h) ∧
      (∀ (h : H) (g : G), a ((h : G) * g) = h * a g) ∧
      (∀ K : Subgroup G, K.Normal → K ≤ H → ∀ g u : G, u ∈ K →
        (a g : G)⁻¹ * (a (g * u) : G) ∈ K) := by
  classical
  intro G _ H
  let q : G → Quotient (QuotientGroup.rightRel H) := Quotient.mk _
  let t : Quotient (QuotientGroup.rightRel H) → G :=
    fun c => if c = q 1 then 1 else c.out
  have ht (c : Quotient (QuotientGroup.rightRel H)) : q (t c) = c := by
    by_cases hc : c = q 1
    · change q (if c = q 1 then 1 else c.out) = c
      rw [if_pos hc]
      exact hc.symm
    · simpa only [t, if_neg hc] using c.out_eq
  let a : G → H := fun g =>
    ⟨g * (t (q g))⁻¹, QuotientGroup.rightRel_apply.mp (Quotient.exact (ht (q g)))⟩
  have hq (h : H) (g : G) : q ((h : G) * g) = q g := by
    symm
    apply Quotient.sound
    apply QuotientGroup.rightRel_apply.mpr
    simpa only [mul_inv_cancel_right] using h.property
  have ha (h : H) (g : G) : a ((h : G) * g) = h * a g := by
    apply Subtype.ext
    change ((h : G) * g) * (t (q ((h : G) * g)))⁻¹ =
      (h : G) * (g * (t (q g))⁻¹)
    rw [hq, mul_assoc]
  have ha1 : a 1 = 1 := by
    apply Subtype.ext
    simp [a, t]
  refine ⟨a, ?_, ha, ?_⟩
  · intro h
    simpa only [mul_one, ha1] using ha h 1
  · intro K hK hKH g u hu
    have hqu : q (g * u) = q g := by
      symm
      apply Quotient.sound
      apply QuotientGroup.rightRel_apply.mpr
      exact hKH (hK.conj_mem u hu g)
    have heq : (a g : G)⁻¹ * (a (g * u) : G) =
        t (q g) * u * (t (q g))⁻¹ := by
      change (g * (t (q g))⁻¹)⁻¹ * ((g * u) * (t (q (g * u)))⁻¹) = _
      rw [hqu]
      group
    rw [heq]
    exact hK.conj_mem u hu (t (q g))
theorem Submission.p08_7d1ff633a4_tp26_low_degree_prism :
    ∀ {X V : Type} [AddCommGroup V] (α β : X → X),
      (∀ F : X → X → V,
        (∀ x y z : X, F y z - F x z + F x y = 0) →
        ∀ x y : X, F (β x) (β y) - F (α x) (α y) =
          F (α y) (β y) - F (α x) (β x)) ∧
      (∀ F : X → X → X → V,
        (∀ w x y z : X, F x y z - F w y z + F w x z - F w x y = 0) →
        let h : X → X → V := fun x y =>
          F (α x) (β x) (β y) - F (α x) (α y) (β y)
        ∀ x y z : X, F (β x) (β y) (β z) - F (α x) (α y) (α z) =
          h y z - h x z + h x y) := by
  intro X V _ α β
  constructor
  · intro F hF x y
    apply sub_eq_zero.mp
    calc
      _ = (F (β x) (β y) - F (α x) (β y) + F (α x) (β x)) -
          (F (α y) (β y) - F (α x) (β y) + F (α x) (α y)) := by abel
      _ = 0 := by simp only [hF, sub_self]
  · intro F hF
    dsimp only
    intro x y z
    apply sub_eq_zero.mp
    calc
      _ = (F (β x) (β y) (β z) - F (α x) (β y) (β z) +
            F (α x) (β x) (β z) - F (α x) (β x) (β y)) -
          (F (α y) (β y) (β z) - F (α x) (β y) (β z) +
            F (α x) (α y) (β z) - F (α x) (α y) (β y)) +
          (F (α y) (α z) (β z) - F (α x) (α z) (β z) +
            F (α x) (α y) (β z) - F (α x) (α y) (α z)) := by abel
      _ = 0 := by simp only [hF, sub_self, add_zero]

theorem Submission.p08_7d1ff633a4_tp26_coset_averaging :
    ∀ {k G X : Type} [Field k] [Group G] [MulAction G X]
      (H : Subgroup G) [Fintype (G ⧸ H)] (V : Rep.{0} k G) (t : (G ⧸ H) → G),
      (∀ c : G ⧸ H, (t c : G ⧸ H) = c) →
      ∃ T : (X → V) →ₗ[k] (X → V),
        (∀ (F : X → V) (x : X),
          T F x = ∑ c : G ⧸ H, V.ρ (t c) (F ((t c)⁻¹ • x))) ∧
        (∀ F : X → V,
          (∀ (h : H) (x : X), F ((h : G) • x) = V.ρ (h : G) (F x)) →
          ∀ (s : G) (x : X), T F (s • x) = V.ρ s (T F x)) ∧
        (∀ F : X → V,
          (∀ (s : G) (x : X), F (s • x) = V.ρ s (F x)) →
          ∀ x : X, T F x = (H.index : k) • F x) ∧
        (∀ u : (G ⧸ H) → G, (∀ c : G ⧸ H, (u c : G ⧸ H) = c) →
          ∀ F : X → V,
          (∀ (h : H) (x : X), F ((h : G) • x) = V.ρ (h : G) (F x)) →
          ∀ x : X, T F x = ∑ c : G ⧸ H, V.ρ (u c) (F ((u c)⁻¹ • x))) := by
  classical
  intro k G X _ _ _ H _ V t ht
  let T : (X → V) →ₗ[k] (X → V) :=
    { toFun := fun F x => ∑ c : G ⧸ H, V.ρ (t c) (F ((t c)⁻¹ • x))
      map_add' := by
        intro F F'
        funext x
        simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]
      map_smul' := by
        intro b F
        funext x
        simp only [Pi.smul_apply, map_smul, Finset.smul_sum, RingHom.id_apply] }
  have hrep (F : X → V)
      (hF : ∀ (h : H) (x : X), F ((h : G) • x) = V.ρ (h : G) (F x))
      (a b : G) (hab : (a : G ⧸ H) = (b : G ⧸ H)) (x : X) :
      V.ρ a (F (a⁻¹ • x)) = V.ρ b (F (b⁻¹ • x)) := by
    let h : H := ⟨a⁻¹ * b, QuotientGroup.eq.mp hab⟩
    have hb : b = a * (h : G) := by simp [h]
    rw [hb, mul_inv_rev, mul_smul]
    rw [← Subgroup.coe_inv, hF h⁻¹]
    simp only [Subgroup.coe_inv, map_mul, Module.End.mul_apply,
      Representation.self_inv_apply]
  refine ⟨T, fun _ _ => rfl, ?_, ?_, ?_⟩
  · intro F hF s x
    change (∑ c : G ⧸ H, V.ρ (t c) (F ((t c)⁻¹ • (s • x)))) =
      V.ρ s (∑ c : G ⧸ H, V.ρ (t c) (F ((t c)⁻¹ • x)))
    calc
      _ = ∑ c : G ⧸ H, V.ρ (t (s • c)) (F ((t (s • c))⁻¹ • (s • x))) :=
        (Equiv.sum_comp (MulAction.toPerm s) _).symm
      _ = ∑ c : G ⧸ H, V.ρ s (V.ρ (t c) (F ((t c)⁻¹ • x))) := by
        apply Finset.sum_congr rfl
        intro c _
        have hc : (t (s • c) : G ⧸ H) = ((s * t c : G) : G ⧸ H) := by
          exact (ht (s • c)).trans
            (congrArg (fun d : G ⧸ H => s • d) (ht c).symm)
        rw [hrep F hF _ _ hc]
        simp only [mul_inv_rev, mul_smul, inv_smul_smul, map_mul, Module.End.mul_apply]
      _ = _ := (map_sum (V.ρ s) _ _).symm
  · intro F hF x
    change (∑ c : G ⧸ H, V.ρ (t c) (F ((t c)⁻¹ • x))) = _
    have hc (c : G ⧸ H) : V.ρ (t c) (F ((t c)⁻¹ • x)) = F x := by
      rw [← hF, smul_inv_smul]
    simp only [hc, Finset.sum_const, Finset.card_univ]
    rw [Subgroup.index_eq_card, Nat.card_eq_fintype_card, Nat.cast_smul_eq_nsmul]
  · intro u hu F hF x
    change (∑ c : G ⧸ H, V.ρ (t c) (F ((t c)⁻¹ • x))) = _
    apply Finset.sum_congr rfl
    intro c _
    exact hrep F hF (t c) (u c) ((ht c).trans (hu c).symm) x
