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


theorem Submission.p05_di_antipode_adjugate_a5b449214a
    {k : Type*} [Field k] {H : Type*} [CommRing H] [HopfAlgebra k H]
    (n : ℕ) (c : Matrix (Fin n) (Fin n) H)
    (hΔ : ∀ i j : Fin n, Coalgebra.comul (R := k) (c i j) =
      ∑ l : Fin n, TensorProduct.tmul k (c i l) (c l j))
    (hε : ∀ i j : Fin n, Coalgebra.counit (R := k) (c i j) =
      if i = j then (1 : k) else 0) :
    ∃ u : H, Matrix.det c * u = 1 ∧ ∀ i j : Fin n,
      HopfAlgebra.antipode k (c i j) = u * Matrix.adjugate c i j := by
  classical
  let Q : Matrix (Fin n) (Fin n) H :=
    Matrix.of fun i j => HopfAlgebra.antipode k (c i j)
  have hQc : Q * c = 1 := by
    ext i j
    simpa [Q, Matrix.mul_apply, Matrix.one_apply, hΔ, hε, map_sum] using
      (HopfAlgebra.mul_antipode_rTensor_comul_apply (R := k) (c i j))
  have hcQ : c * Q = 1 := by
    ext i j
    simpa [Q, Matrix.mul_apply, Matrix.one_apply, hΔ, hε, map_sum] using
      (HopfAlgebra.mul_antipode_lTensor_comul_apply (R := k) (c i j))
  have hdet : Matrix.det c * Matrix.det Q = 1 := by
    rw [← Matrix.det_mul, hcQ, Matrix.det_one]
  have hdet' : Matrix.det Q * Matrix.det c = 1 := by
    rw [mul_comm, hdet]
  have hcT : c * (Matrix.det Q • Matrix.adjugate c) = 1 := by
    rw [Matrix.mul_smul, Matrix.mul_adjugate, smul_smul, hdet', one_smul]
  have hQT : Q = Matrix.det Q • Matrix.adjugate c := by
    calc
      Q = Q * 1 := (Matrix.mul_one Q).symm
      _ = Q * (c * (Matrix.det Q • Matrix.adjugate c)) := by rw [hcT]
      _ = (Q * c) * (Matrix.det Q • Matrix.adjugate c) :=
        (Matrix.mul_assoc _ _ _).symm
      _ = Matrix.det Q • Matrix.adjugate c := by rw [hQc, Matrix.one_mul]
  refine ⟨Matrix.det Q, hdet, ?_⟩
  intro i j
  exact congrArg (fun M : Matrix (Fin n) (Fin n) H => M i j) hQT
