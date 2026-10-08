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

theorem Submission.p05_fr_rhm_bcsi_base_changed_presentation_a5b449214a
    {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S]
    {M : Type*} [AddCommGroup M] [Module R M]
    (n p : ℕ) (P : Matrix (Fin n) (Fin p) R)
    (π : (Fin n → R) →ₗ[R] M) (_hπ : Function.Surjective π)
    (_hker : LinearMap.ker π = LinearMap.range P.mulVecLin) :
    ∃ q : (Fin n → S) →ₗ[S] TensorProduct R S M,
      (∀ b : Fin n → S, q b =
        ∑ i, b i • TensorProduct.tmul R (1 : S) (π (Pi.single i (1 : R)))) ∧
      Function.Surjective q ∧
      LinearMap.ker q = LinearMap.range (P.map (algebraMap R S)).mulVecLin := by
  classical
  let e (k : ℕ) : TensorProduct R S (Fin k → R) ≃ₗ[S] (Fin k → S) :=
    TensorProduct.piScalarRight R S S (Fin k)
  let q : (Fin n → S) →ₗ[S] TensorProduct R S M :=
    (π.baseChange S).comp (e n).symm.toLinearMap
  have hP (x : TensorProduct R S (Fin p → R)) :
      e n (P.mulVecLin.baseChange S x) =
        (P.map (algebraMap R S)).mulVecLin (e p x) := by
    induction x with
    | zero => simp
    | tmul s a =>
      ext i
      simp [e, Matrix.mulVec, dotProduct,
        Algebra.smul_def, Finset.sum_mul, mul_assoc]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hex : Function.Exact (P.mulVecLin.baseChange S) (π.baseChange S) :=
    lTensor_exact S (LinearMap.exact_iff.mpr _hker) _hπ
  refine ⟨q, ?_, ?_, ?_⟩
  · intro b
    calc
      q b = q (∑ i, Pi.single i (b i)) := by rw [Finset.univ_sum_single]
      _ = ∑ i, TensorProduct.tmul R (b i) (π (Pi.single i (1 : R))) := by
        simp [q, e]
      _ = _ := by
        simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  · exact (LinearMap.baseChange_surjective S _hπ).comp (e n).symm.surjective
  · ext b
    change q b = 0 ↔ ∃ c, (P.map (algebraMap R S)).mulVecLin c = b
    constructor
    · intro hb
      obtain ⟨x, hx⟩ := (hex ((e n).symm b)).mp hb
      refine ⟨e p x, ?_⟩
      rw [← hP, hx, (e n).apply_symm_apply]
    · rintro ⟨c, rfl⟩
      apply (hex _).mpr
      refine ⟨(e p).symm c, ?_⟩
      apply (e n).injective
      rw [hP, (e p).apply_symm_apply]
      exact ((e n).apply_symm_apply _).symm
