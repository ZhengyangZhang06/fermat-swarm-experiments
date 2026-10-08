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
