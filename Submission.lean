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
