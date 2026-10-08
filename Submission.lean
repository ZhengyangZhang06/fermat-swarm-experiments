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

theorem Submission.p05_hte_fss_tensor_dual_expansion_a5b449214a :
    ∀ {k : Type*} [Field k] {C : Type*} [AddCommGroup C] [Module k C]
      (z : TensorProduct k C C),
      ∃ (n : ℕ) (v w : Fin n → C) (ell : Fin n → C →ₗ[k] k),
        z = ∑ i : Fin n, TensorProduct.tmul k (v i) (w i) ∧
          ∀ i j : Fin n, ell i (w j) = if i = j then (1 : k) else 0 := by
  intro k _ C _ _ z
  classical
  obtain ⟨m, x, y, hz⟩ := TensorProduct.exists_sum_tmul_eq z
  let W : Submodule k C := Submodule.span k (Set.range y)
  have : FiniteDimensional k W := FiniteDimensional.span_of_finite k (Set.finite_range y)
  let b := Module.finBasis k W
  let yW : Fin m → W := fun r => ⟨y r, Submodule.subset_span (Set.mem_range_self r)⟩
  choose ell hell using fun i : Fin (Module.finrank k W) => (b.coord i).exists_extend
  refine ⟨Module.finrank k W, (fun i => ∑ r, b.repr (yW r) i • x r),
    (fun i => (b i : C)), ell, ?_, ?_⟩
  · have hy (r : Fin m) : y r = ∑ i, b.repr (yW r) i • (b i : C) := by
      simpa only [map_sum, map_smul, Submodule.subtype_apply, yW] using
        (congrArg W.subtype (b.sum_repr (yW r))).symm
    calc
      z = ∑ r, TensorProduct.tmul k (x r) (y r) := hz
      _ = ∑ r, ∑ i, TensorProduct.tmul k (b.repr (yW r) i • x r) (b i : C) := by
        apply Finset.sum_congr rfl
        intro r _
        rw [hy r, TensorProduct.tmul_sum]
        apply Finset.sum_congr rfl
        intro i _
        exact (TensorProduct.smul_tmul _ _ _).symm
      _ = ∑ i, TensorProduct.tmul k (∑ r, b.repr (yW r) i • x r) (b i : C) := by
        rw [Finset.sum_comm]
        simp only [TensorProduct.sum_tmul]
  · intro i j
    have h := LinearMap.congr_fun (hell i) (b j)
    simpa [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply, eq_comm] using h

theorem Submission.p05_hte_fss_coefficient_span_a5b449214a
    {k : Type*} [Field k] {C : Type*} [AddCommGroup C] [Module k C] [Coalgebra k C]
    (f : C) (n : ℕ) (v w : Fin n → C) (ell : Fin n → C →ₗ[k] k)
    (hΔ : Coalgebra.comul (R := k) f =
      ∑ i : Fin n, TensorProduct.tmul k (v i) (w i))
    (hdual : ∀ i j : Fin n, ell i (w j) = if i = j then (1 : k) else 0) :
    let V : Submodule k C := Submodule.span k (Set.range v)
    FiniteDimensional k V ∧ f ∈ V ∧ ∀ x ∈ V, Coalgebra.comul (R := k) x ∈
      Submodule.span k {t : TensorProduct k C C |
        ∃ a ∈ V, ∃ b : C, t = TensorProduct.tmul k a b} := by
  classical
  let V : Submodule k C := Submodule.span k (Set.range v)
  let S : Submodule k (C ⊗[k] C) :=
    Submodule.span k {t : C ⊗[k] C | ∃ a ∈ V, ∃ b : C, t = a ⊗ₜ[k] b}
  change FiniteDimensional k V ∧ f ∈ V ∧
    ∀ x ∈ V, Coalgebra.comul (R := k) x ∈ S
  have hv (i : Fin n) : v i ∈ V := Submodule.subset_span ⟨i, rfl⟩
  refine ⟨FiniteDimensional.span_of_finite k (Set.finite_range v), ?_, ?_⟩
  · have hε := congrArg (TensorProduct.rid k C)
      (Coalgebra.lTensor_counit_comul (R := k) f)
    rw [hΔ] at hε
    have hf : (∑ i : Fin n, Coalgebra.counit (R := k) (w i) • v i) = f := by
      simpa only [map_sum, LinearMap.lTensor_tmul, TensorProduct.rid_tmul, one_smul]
        using hε
    rw [← hf]
    exact Submodule.sum_mem V fun i _ => V.smul_mem _ (hv i)
  · have hstable : V ≤ S.comap (Coalgebra.comul (R := k)) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      change Coalgebra.comul (R := k) (v i) ∈ S
      let R : C ⊗[k] C →ₗ[k] C :=
        (TensorProduct.rid k C).toLinearMap ∘ₗ (ell i).lTensor C
      let T : (C ⊗[k] C) ⊗[k] C →ₗ[k] C ⊗[k] C :=
        (TensorProduct.rid k (C ⊗[k] C)).toLinearMap ∘ₗ
          (ell i).lTensor (C ⊗[k] C)
      have hT (a : C) (t : C ⊗[k] C) :
          T ((TensorProduct.assoc k C C C).symm (a ⊗ₜ[k] t)) = a ⊗ₜ[k] R t := by
        induction t using TensorProduct.induction_on with
        | zero => simp [R, T]
        | tmul b c => simp [R, T, TensorProduct.tmul_smul]
        | add t u ht hu =>
          simp only [TensorProduct.tmul_add, map_add, ht, hu]
      have hc := Coalgebra.coassoc_symm_apply (R := k) f
      rw [hΔ] at hc
      have hcontract := congrArg T hc
      have hformula : (∑ j : Fin n, v j ⊗ₜ[k] R (Coalgebra.comul (R := k) (w j))) =
          Coalgebra.comul (R := k) (v i) := by
        simpa only [map_sum, LinearMap.lTensor_tmul, LinearMap.rTensor_tmul, hT,
          T, LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.rid_tmul,
          hdual, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ,
          if_true] using hcontract
      rw [← hformula]
      apply Submodule.sum_mem
      intro j _
      exact Submodule.subset_span ⟨v j, hv j, R (Coalgebra.comul (R := k) (w j)), rfl⟩
    intro x hx
    exact hstable hx


namespace Submission

theorem p05_hte_finite_stable_subspace_a5b449214a
    {k : Type*} [Field k] {C : Type*} [AddCommGroup C] [Module k C] [Coalgebra k C]
    (E : Finset C) :
    ∃ V : Submodule k C, FiniteDimensional k V ∧ (∀ x ∈ E, x ∈ V) ∧
      ∀ x ∈ V, Coalgebra.comul (R := k) x ∈
        Submodule.span k {t : TensorProduct k C C |
          ∃ a ∈ V, ∃ b : C, t = TensorProduct.tmul k a b} := by
  classical
  induction E using Finset.induction_on with
  | empty =>
      refine ⟨⊥, inferInstance, ?_, ?_⟩
      · simp
      · intro x hx
        have hx0 : x = 0 := (Submodule.mem_bot k).mp hx
        subst x
        rw [map_zero]
        exact Submodule.zero_mem _
  | @insert f E _ ih =>
      obtain ⟨V, hVfin, hEV, hVstable⟩ := ih
      obtain ⟨n, v, w, ell, hΔ, hdual⟩ :=
        p05_hte_fss_tensor_dual_expansion_a5b449214a (Coalgebra.comul (R := k) f)
      obtain ⟨hWfin, hfW, hWstable⟩ :=
        p05_hte_fss_coefficient_span_a5b449214a f n v w ell hΔ hdual
      let W : Submodule k C := Submodule.span k (Set.range v)
      let : FiniteDimensional k V := hVfin
      let : FiniteDimensional k W := hWfin
      refine ⟨W ⊔ V, inferInstance, ?_, ?_⟩
      · intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact Submodule.mem_sup_left hfW
        · exact Submodule.mem_sup_right (hEV x hx)
      · intro x hx
        obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
        rw [map_add]
        apply Submodule.add_mem
        · apply (Submodule.span_mono ?_) (hWstable y hy)
          rintro t ⟨a, ha, b, rfl⟩
          exact ⟨a, Submodule.mem_sup_left ha, b, rfl⟩
        · apply (Submodule.span_mono ?_) (hVstable z hz)
          rintro t ⟨a, ha, b, rfl⟩
          exact ⟨a, Submodule.mem_sup_right ha, b, rfl⟩

end Submission
