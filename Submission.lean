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
