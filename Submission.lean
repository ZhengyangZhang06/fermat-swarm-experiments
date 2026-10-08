/-
Copyright 2026 Anthropic, PBC. Licensed under Apache-2.0; see LICENSE.
Source: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_HopfAlgebra_hopfKer_eq_of_surjective_of_ker_eq_span.lean
Modified: replaced the proof with sorry and removed P2M proof imports.
Requires the upstream Definitions modules and their dependencies.
-/

import Mathlib
import Definitions.Def_HopfAlgebra_HopfKer
attribute [-instance] HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra
attribute [-simp] HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul

universe u v w

open scoped TensorProduct

theorem HopfAlgebra.hopfKer_eq_of_surjective_of_ker_eq_span
    {k : Type u} [Field k] {H : Type v} [CommRing H] [HopfAlgebra k H] [Algebra.FiniteType k H]
    (K : Subalgebra k H)
    (hΔ : ∀ x ∈ K, Coalgebra.comul (R := k) x ∈
      Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K, ∃ b ∈ K, t = a ⊗ₜ[k] b})
    (hS : ∀ x ∈ K, HopfAlgebra.antipode k x ∈ K)
    {B : Type w} [CommRing B] [Bialgebra k B] (q : H →ₐc[k] B) (hq : Function.Surjective q)
    (hker : RingHom.ker (q : H →+* B) =
      Ideal.span {x : H | x ∈ K ∧ Coalgebra.counit (R := k) x = 0}) :
    HopfAlgebra.hopfKer q = K := by
  sorry


theorem Submission.p05_canonical_balanced_lift_a5b449214a
    {k : Type*} [Field k] {H : Type*} [CommRing H] [HopfAlgebra k H]
    (K : Subalgebra k H) {B : Type*} [CommRing B] [Bialgebra k B]
    (q : BialgHom k H B)
    (hcoinv : ∀ t ∈ K, HopfAlgebra.coaction q t = TensorProduct.tmul k t (1 : B)) :
    ∃ β : (TensorProduct K H H) →ₐ[k] (TensorProduct k H B),
      ∀ a b : H, β (TensorProduct.tmul K a b) =
        (TensorProduct.tmul k a (1 : B)) * HopfAlgebra.coaction q b := by
  let ρ : H →ₐ[K] (TensorProduct k H B) :=
    { (HopfAlgebra.coaction q).toRingHom with
      commutes' := fun t => by
        change HopfAlgebra.coaction q (t : H) = TensorProduct.tmul k (t : H) (1 : B)
        exact hcoinv t t.property }
  refine ⟨(Algebra.TensorProduct.lift
    (Algebra.TensorProduct.includeLeft : H →ₐ[H] (TensorProduct k H B))
    ρ (fun _ _ => Commute.all _ _)).restrictScalars k, ?_⟩
  intro a b
  rfl
theorem Submission.p05_di_determinant_grouplike_a5b449214a
    {k : Type*} [Field k] {H : Type*} [CommRing H] [Bialgebra k H]
    (n : ℕ) (c : Matrix (Fin n) (Fin n) H)
    (hΔ : ∀ i j : Fin n, Coalgebra.comul (R := k) (c i j) =
      ∑ l : Fin n, TensorProduct.tmul k (c i l) (c l j))
    (hε : ∀ i j : Fin n, Coalgebra.counit (R := k) (c i j) =
      if i = j then (1 : k) else 0) :
    Coalgebra.comul (R := k) (Matrix.det c) =
      TensorProduct.tmul k (Matrix.det c) (Matrix.det c) ∧
    Coalgebra.counit (R := k) (Matrix.det c) = 1 := by
  classical
  let L : H →ₐ[k] H ⊗[k] H := Algebra.TensorProduct.includeLeft
  let R : H →ₐ[k] H ⊗[k] H := Algebra.TensorProduct.includeRight
  have hcomul : (Bialgebra.comulAlgHom k H).mapMatrix c =
      L.mapMatrix c * R.mapMatrix c := by
    ext i j
    change Coalgebra.comul (R := k) (c i j) =
      ∑ l : Fin n, L (c i l) * R (c l j)
    rw [hΔ]
    apply Finset.sum_congr rfl
    intro l _
    simp [L, R, Algebra.TensorProduct.tmul_mul_tmul]
  constructor
  · change (Bialgebra.comulAlgHom k H) (Matrix.det c) = _
    rw [AlgHom.map_det, hcomul, Matrix.det_mul, ← L.map_det, ← R.map_det]
    simp [L, R, Algebra.TensorProduct.tmul_mul_tmul]
  · have hcounit : (Bialgebra.counitAlgHom k H).mapMatrix c =
        (1 : Matrix (Fin n) (Fin n) k) := by
      ext i j
      change Coalgebra.counit (R := k) (c i j) = if i = j then 1 else 0
      exact hε i j
    change (Bialgebra.counitAlgHom k H) (Matrix.det c) = 1
    rw [AlgHom.map_det, hcounit, Matrix.det_one]
theorem Submission.p05_cm_coalgebra_laws_a5b449214a
    {k : Type*} [Field k] {H : Type*} [CommRing H] [HopfAlgebra k H]
    (V : Submodule k H) (n : ℕ) (b : Module.Basis (Fin n) k V)
    (c : Matrix (Fin n) (Fin n) H)
    (hexp : ∀ j : Fin n, Coalgebra.comul (R := k) (b j : H) =
      ∑ i : Fin n, TensorProduct.tmul k (b i : H) (c i j)) :
    (∀ i j : Fin n, Coalgebra.comul (R := k) (c i j) =
      ∑ l : Fin n, TensorProduct.tmul k (c i l) (c l j)) ∧
    (∀ i j : Fin n, Coalgebra.counit (R := k) (c i j) =
      if i = j then (1 : k) else 0) := by
  classical
  have hcoord : ∀ i : Fin n, ∃ φ : H →ₗ[k] k,
      ∀ r : Fin n, φ (b r : H) = if i = r then 1 else 0 := by
    intro i
    obtain ⟨φ, hφ⟩ := (b.coord i).exists_extend
    refine ⟨φ, fun r => ?_⟩
    have h := LinearMap.congr_fun hφ (b r)
    simpa [Module.Basis.coord_apply, Finsupp.single_apply, eq_comm] using h
  choose φ hφ using hcoord
  constructor
  · intro i j
    let U : H ⊗[k] (H ⊗[k] H) →ₗ[k] H ⊗[k] H :=
      (TensorProduct.lid k (H ⊗[k] H)).toLinearMap ∘ₗ
        (φ i).rTensor (H ⊗[k] H)
    have h := Coalgebra.coassoc_apply (R := k) (b j : H)
    rw [hexp j] at h
    simp only [map_sum, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul,
      hexp, TensorProduct.sum_tmul, TensorProduct.assoc_tmul] at h
    have hu := congrArg U h
    simpa [U, map_sum, hφ, TensorProduct.assoc_tmul, ite_smul] using hu.symm
  · intro i j
    let U : H ⊗[k] k →ₗ[k] k :=
      (TensorProduct.lid k k).toLinearMap ∘ₗ (φ i).rTensor k
    have h := Coalgebra.lTensor_counit_comul (R := k) (b j : H)
    rw [hexp j] at h
    have hu := congrArg U h
    simpa [U, map_sum, hφ, ite_smul] using hu
theorem Submission.p05_cm_basis_expansion_a5b449214a
    {k : Type*} [Field k] {H : Type*} [CommRing H] [HopfAlgebra k H]
    (V : Submodule k H) (n : ℕ) (b : Module.Basis (Fin n) k V)
    (hV : ∀ x ∈ V, Coalgebra.comul (R := k) x ∈
      Submodule.span k {t : TensorProduct k H H |
        ∃ a ∈ V, ∃ y : H, t = TensorProduct.tmul k a y}) :
    ∃ c : Matrix (Fin n) (Fin n) H, ∀ j : Fin n,
      Coalgebra.comul (R := k) (b j : H) =
        ∑ i : Fin n, TensorProduct.tmul k (b i : H) (c i j) := by
  classical
  let W : Submodule k (H ⊗[k] H) :=
    { carrier := {z | ∃ d : Fin n → H, z = ∑ i, (b i : H) ⊗ₜ[k] d i}
      zero_mem' := ⟨fun _ => 0, by simp⟩
      add_mem' := by
        rintro x y ⟨d, rfl⟩ ⟨e, rfl⟩
        exact ⟨fun i => d i + e i, by
          simp only [TensorProduct.tmul_add, Finset.sum_add_distrib]⟩
      smul_mem' := by
        rintro r x ⟨d, rfl⟩
        exact ⟨fun i => r • d i, by
          simp only [TensorProduct.tmul_smul, Finset.smul_sum]⟩ }
  have hspan : Submodule.span k {t : TensorProduct k H H |
      ∃ a ∈ V, ∃ y : H, t = TensorProduct.tmul k a y} ≤ W := by
    apply Submodule.span_le.mpr
    rintro t ⟨a, ha, y, rfl⟩
    refine ⟨fun i => b.repr ⟨a, ha⟩ i • y, ?_⟩
    have hexp : ∑ i, b.repr ⟨a, ha⟩ i • (b i : H) = a := by
      simpa only [map_sum, map_smul, Submodule.subtype_apply] using
        congrArg V.subtype (b.sum_repr ⟨a, ha⟩)
    conv_lhs => rw [← hexp]
    rw [TensorProduct.sum_tmul]
    simp only [TensorProduct.smul_tmul]
  have hcol (j : Fin n) : ∃ d : Fin n → H,
      Coalgebra.comul (R := k) (b j : H) = ∑ i, (b i : H) ⊗ₜ[k] d i :=
    hspan (hV (b j : H) (b j).property)
  choose d hd using hcol
  exact ⟨Matrix.of (fun i j => d j i), hd⟩
theorem Submission.p05_fr_coideal_ideal_dichotomy_a5b449214a
    {k : Type*} [Field k] {A : Type*} [CommRing A] [HopfAlgebra k A]
    (J : Ideal A)
    (_hJ : ∀ x ∈ J, Coalgebra.comul (R := k) x ∈
      Submodule.span k {t : TensorProduct k A A |
        ∃ a ∈ J, ∃ b : A, t = TensorProduct.tmul k a b}) :
    J = ⊥ ∨ J = ⊤ := by
  classical
  by_cases htop : J = ⊤
  · exact Or.inr htop
  left
  let L : TensorProduct k A A →ₗ[k] A :=
    LinearMap.mul' k A ∘ₗ (HopfAlgebra.antipode k).lTensor A
  have hL (t : TensorProduct k A A)
      (ht : t ∈ Submodule.span k {t : TensorProduct k A A |
        ∃ a ∈ J, ∃ b : A, t = TensorProduct.tmul k a b}) : L t ∈ J := by
    induction ht using Submodule.span_induction with
    | mem t ht =>
      obtain ⟨a, ha, b, rfl⟩ := ht
      simpa [L] using J.mul_mem_right (HopfAlgebra.antipode k b) ha
    | zero => simp
    | add t u _ _ ht hu => simpa using J.add_mem ht hu
    | smul r t _ ht =>
      simpa using (J.restrictScalars k).smul_mem r ht
  have heps (x : A) (hx : x ∈ J) : Coalgebra.counit (R := k) x = 0 := by
    have hmem : algebraMap k A (Coalgebra.counit (R := k) x) ∈ J := by
      simpa [L] using hL _ (_hJ x hx)
    by_contra hne
    apply htop
    apply J.eq_top_iff_one.mpr
    have hmul := J.mul_mem_left
      (algebraMap k A (Coalgebra.counit (R := k) x)⁻¹) hmem
    simpa only [← map_mul, inv_mul_cancel₀ hne, map_one] using hmul
  let C : TensorProduct k A A →ₗ[k] A :=
    TensorProduct.lift (LinearMap.lsmul k A ∘ₗ Coalgebra.counit (R := k))
  have hC (t : TensorProduct k A A)
      (ht : t ∈ Submodule.span k {t : TensorProduct k A A |
        ∃ a ∈ J, ∃ b : A, t = TensorProduct.tmul k a b}) : C t = 0 := by
    induction ht using Submodule.span_induction with
    | mem t ht =>
      obtain ⟨a, ha, b, rfl⟩ := ht
      simp [C, heps a ha]
    | zero => exact map_zero C
    | add t u _ _ ht hu => simp only [map_add, ht, hu, add_zero]
    | smul r t _ ht => simp only [map_smul, ht, smul_zero]
  apply (Submodule.eq_bot_iff J).mpr
  intro x hx
  have hidx : C (Coalgebra.comul (R := k) x) = x :=
    LinearMap.congr_fun (Coalgebra.lift_lsmul_comp_counit_comp_comul
      (R := k) (A := A)) x
  exact hidx.symm.trans (hC _ (_hJ x hx))

theorem Submission.p05_pcs_clear_away_section_a5b449214a
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    (n p : ℕ) (P : Matrix (Fin n) (Fin p) R) (π : (Fin n → R) →ₗ[R] M)
    (_hπ : Function.Surjective π)
    (_hker : LinearMap.ker π = LinearMap.range P.mulVecLin) (f : R)
    (_hlocal : ∃ σ : LocalizedModule (Submonoid.powers f) M →ₗ[Localization.Away f]
      LocalizedModule (Submonoid.powers f) (Fin n → R),
      (LocalizedModule.map (Submonoid.powers f) π).comp σ = LinearMap.id) :
    ∃ N : ℕ, 0 < N ∧ ∃ t : M →ₗ[R] (Fin n → R),
      π.comp t = f ^ N • (LinearMap.id : M →ₗ[R] M) := by
  have : Module.FinitePresentation R M :=
    Module.finitePresentation_of_free_of_surjective π _hπ
      (_hker.symm ▸ Submodule.fg_range P.mulVecLin)
  obtain ⟨σ, hσ⟩ := _hlocal
  let S := Submonoid.powers f
  let iM := LocalizedModule.mkLinearMap S M
  let iF := LocalizedModule.mkLinearMap S (Fin n → R)
  obtain ⟨u, s, hu⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule
    S iF ((σ.restrictScalars R).comp iM)
  have hcomp : iM.comp (π.comp u) = iM.comp ((s : R) • LinearMap.id) := by
    ext x
    have hx := LinearMap.congr_fun hu x
    have hσx := LinearMap.congr_fun hσ (iM x)
    change iF (u x) = (s : R) • σ (iM x) at hx
    change (LocalizedModule.map S π) (σ (iM x)) = iM x at hσx
    change iM (π (u x)) = iM ((s : R) • x)
    calc
      iM (π (u x)) = (LocalizedModule.map S π) (iF (u x)) := by
        simp [iM, iF]
      _ = (s : R) • iM x := by
        rw [hx, LinearMap.map_smul_of_tower, hσx]
      _ = iM ((s : R) • x) := (map_smul iM _ _).symm
  obtain ⟨c, hc⟩ := Module.Finite.exists_smul_of_comp_eq_of_isLocalizedModule
    S iM _ _ hcomp
  obtain ⟨a, ha⟩ := s.property
  obtain ⟨b, hb⟩ := c.property
  have heq : f ^ b • π.comp u = f ^ b • (f ^ a • (LinearMap.id : M →ₗ[R] M)) := by
    simpa only [Submonoid.smul_def, ← ha, ← hb] using hc
  refine ⟨b + a + 1, by omega, f • (f ^ b • u), ?_⟩
  rw [LinearMap.comp_smul, LinearMap.comp_smul, heq]
  simp only [smul_smul, ← pow_add]
  congr 1
  rw [pow_succ, mul_comm]

theorem Submission.p05_pcs_patch_power_sections_a5b449214a
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    {F : Type*} [AddCommGroup F] [Module R F]
    (π : F →ₗ[R] M) (q : ℕ) (f : Fin q → R)
    (_hcover : Ideal.span (Set.range f) = ⊤) (N : Fin q → ℕ)
    (_hN : ∀ i, 0 < N i) (t : Fin q → M →ₗ[R] F)
    (_ht : ∀ i, π.comp (t i) = (f i) ^ (N i) • (LinearMap.id : M →ₗ[R] M)) :
    ∃ s : M →ₗ[R] F, π.comp s = LinearMap.id := by
  classical
  let j : Set.range f → Fin q := fun x => Classical.choose x.property
  have hj (x : Set.range f) : f (j x) = x := Classical.choose_spec x.property
  have hpow : Ideal.span (Set.range fun i => f i ^ N i) = ⊤ := by
    have htop := Ideal.span_range_pow_eq_top (Set.range f) _hcover (fun x => N (j x))
    apply top_unique
    rw [← htop]
    apply Ideal.span_mono
    rintro _ ⟨x, rfl⟩
    exact ⟨j x, congrArg (fun r : R => r ^ N (j x)) (hj x)⟩
  obtain ⟨b, hb⟩ := Ideal.mem_span_range_iff_exists_fun.mp
    ((Ideal.eq_top_iff_one _).mp hpow)
  refine ⟨∑ i, b i • t i, ?_⟩
  ext m
  simp only [LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    map_sum, map_smul]
  have ht (i : Fin q) : π (t i m) = f i ^ N i • m :=
    LinearMap.congr_fun (_ht i) m
  simp only [ht, smul_smul, ← Finset.sum_smul, hb, one_smul, LinearMap.id_apply]


namespace Submission

theorem p05_ptm_split_of_away_splits_a5b449214a
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    (n p q : ℕ) (P : Matrix (Fin n) (Fin p) R) (π : (Fin n → R) →ₗ[R] M)
    (_hπ : Function.Surjective π) (_hker : LinearMap.ker π = LinearMap.range P.mulVecLin)
    (f : Fin q → R) (_hcover : Ideal.span (Set.range f) = ⊤)
    (_hlocal : ∀ i : Fin q,
      ∃ s : LocalizedModule (Submonoid.powers (f i)) M →ₗ[Localization.Away (f i)]
        LocalizedModule (Submonoid.powers (f i)) (Fin n → R),
        (LocalizedModule.map (Submonoid.powers (f i)) π).comp s = LinearMap.id) :
    ∃ s : M →ₗ[R] (Fin n → R), π.comp s = LinearMap.id := by
  classical
  have hpower : ∀ i : Fin q, ∃ N : ℕ, 0 < N ∧
      ∃ t : M →ₗ[R] (Fin n → R),
        π.comp t = (f i) ^ N • (LinearMap.id : M →ₗ[R] M) := by
    intro i
    exact Submission.p05_pcs_clear_away_section_a5b449214a
      n p P π _hπ _hker (f i) (_hlocal i)
  choose N hN t ht using hpower
  exact Submission.p05_pcs_patch_power_sections_a5b449214a π q f _hcover N hN t ht

end Submission
