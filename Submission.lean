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

theorem Submission.p05_fhess_tensor_independent_right_a5b449214a
    {k : Type*} [Field k] {M : Type*} [AddCommGroup M] [Module k M]
    {N : Type*} [AddCommGroup N] [Module k N] (z : TensorProduct k M N) :
    ∃ (n : ℕ) (v : Fin n → M) (w : Fin n → N),
      LinearIndependent k w ∧ z = ∑ i : Fin n, TensorProduct.tmul k (v i) (w i) := by
  classical
  obtain ⟨r, a, b, hz⟩ := TensorProduct.exists_sum_tmul_eq z
  let S := Submodule.span k (Set.range b)
  let : Module.Finite k S := Module.Finite.span_of_finite k (Set.finite_range b)
  let c := Module.finBasis k S
  let b' : Fin r → S := fun j => ⟨b j, Submodule.subset_span (Set.mem_range_self j)⟩
  refine ⟨Module.finrank k S, (fun i => ∑ j, c.repr (b' j) i • a j),
    (fun i => (c i : N)), ?_, ?_⟩
  · exact c.linearIndependent.map' S.subtype (Submodule.ker_subtype S)
  · calc
      z = ∑ j, TensorProduct.tmul k (a j) (b j) := hz
      _ = ∑ j, ∑ i, TensorProduct.tmul k (c.repr (b' j) i • a j) (c i : N) := by
        apply Finset.sum_congr rfl
        intro j _
        have hj : b j = ∑ i, c.repr (b' j) i • (c i : N) := by
          simpa only [map_sum, map_smul, Submodule.subtype_apply] using
            (congrArg S.subtype (c.sum_repr (b' j))).symm
        rw [hj, TensorProduct.tmul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
      _ = ∑ i, ∑ j, TensorProduct.tmul k (c.repr (b' j) i • a j) (c i : N) :=
        Finset.sum_comm
      _ = ∑ i, TensorProduct.tmul k (∑ j, c.repr (b' j) i • a j) (c i : N) := by
        simp only [TensorProduct.sum_tmul]
theorem Submission.p05_fhess_coefficient_span_stable_a5b449214a
    {k : Type*} [Field k] {C : Type*} [AddCommGroup C] [Module k C] [Coalgebra k C]
    (x : C) (n : ℕ) (v w : Fin n → C) (hw : LinearIndependent k w)
    (hΔ : Coalgebra.comul (R := k) x =
      ∑ i : Fin n, TensorProduct.tmul k (v i) (w i)) :
    FiniteDimensional k (Submodule.span k (Set.range v)) ∧
    x ∈ Submodule.span k (Set.range v) ∧
    ∀ y ∈ Submodule.span k (Set.range v), Coalgebra.comul (R := k) y ∈
      Submodule.span k {t : TensorProduct k C C |
        ∃ a ∈ Submodule.span k (Set.range v), ∃ b : C,
          t = TensorProduct.tmul k a b} := by
  classical
  let V := Submodule.span k (Set.range v)
  let W := Submodule.span k {t : C ⊗[k] C | ∃ a ∈ V, ∃ b : C, t = a ⊗ₜ[k] b}
  have hv (i : Fin n) : v i ∈ V := Submodule.subset_span (Set.mem_range_self i)
  refine ⟨FiniteDimensional.span_of_finite k (Set.finite_range v), ?_, ?_⟩
  · have hx : x = ∑ i : Fin n, Coalgebra.counit (R := k) (w i) • v i := by
      have h := congrArg
        (fun z => TensorProduct.rid k C ((Coalgebra.counit (R := k)).lTensor C z)) hΔ
      simpa [map_sum] using h
    rw [hx]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem V _ (hv i)
  · suffices hs : V ≤ W.comap (Coalgebra.comul (R := k)) from fun y hy => hs hy
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    change Coalgebra.comul (R := k) (v j) ∈ W
    obtain ⟨φ, hφ⟩ := ((Finsupp.lapply j).comp hw.repr).exists_extend
    have hφw (i : Fin n) : φ (w i) = if i = j then 1 else 0 := by
      have h := LinearMap.congr_fun hφ
        ⟨w i, Submodule.subset_span (Set.mem_range_self i)⟩
      simpa [hw.repr_eq_single i
        ⟨w i, Submodule.subset_span (Set.mem_range_self i)⟩ rfl, Finsupp.single_apply] using h
    let D : C ⊗[k] C →ₗ[k] C := (TensorProduct.rid k C).toLinearMap.comp (φ.lTensor C)
    let T : (C ⊗[k] C) ⊗[k] C →ₗ[k] C ⊗[k] C :=
      (TensorProduct.rid k (C ⊗[k] C)).toLinearMap.comp (φ.lTensor (C ⊗[k] C))
    have hT (a : C) (z : C ⊗[k] C) :
        T ((TensorProduct.assoc k C C C).symm (a ⊗ₜ[k] z)) = a ⊗ₜ[k] D z := by
      induction z using TensorProduct.induction_on with
      | zero => simp [D, T]
      | tmul b c => simp [D, T, TensorProduct.tmul_smul]
      | add z z' hz hz' => simp [TensorProduct.tmul_add, hz, hz']
    have hco := congrArg T (Coalgebra.coassoc_symm_apply (R := k) x)
    have heq : Coalgebra.comul (R := k) (v j) =
        ∑ i : Fin n, v i ⊗ₜ[k] D (Coalgebra.comul (R := k) (w i)) := by
      simpa [hΔ, map_sum, hT, T, hφw] using hco.symm
    rw [heq]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.subset_span ⟨v i, hv i, D (Coalgebra.comul (R := k) (w i)), rfl⟩


namespace Submission

theorem p05_fhe_stable_subspace_a5b449214a :
    ∀ {k : Type*} [Field k] {H : Type*} [CommRing H] [HopfAlgebra k H]
      (F : Finset H), ∃ V : Submodule k H, FiniteDimensional k V ∧ (1 : H) ∈ V ∧
      (∀ x ∈ F, x ∈ V) ∧ (∀ x ∈ V, Coalgebra.comul (R := k) x ∈
        Submodule.span k {t : TensorProduct k H H |
          ∃ a ∈ V, ∃ b : H, t = TensorProduct.tmul k a b}) := by
  intro k _ H _ _ F
  classical
  -- The two children supply the stable coefficient span for each element.
  have hsingle (x : H) : ∃ V : Submodule k H,
      FiniteDimensional k V ∧ x ∈ V ∧ (∀ y ∈ V, Coalgebra.comul (R := k) y ∈
        Submodule.span k {t : TensorProduct k H H |
          ∃ a ∈ V, ∃ b : H, t = TensorProduct.tmul k a b}) := by
    obtain ⟨n, v, w, hw, hΔ⟩ :=
      p05_fhess_tensor_independent_right_a5b449214a (Coalgebra.comul (R := k) x)
    exact ⟨Submodule.span k (Set.range v),
      p05_fhess_coefficient_span_stable_a5b449214a x n v w hw hΔ⟩
  have hmono {U V : Submodule k H} (hUV : U ≤ V) :
      Submodule.span k {t : TensorProduct k H H |
        ∃ a ∈ U, ∃ b : H, t = TensorProduct.tmul k a b} ≤
      Submodule.span k {t : TensorProduct k H H |
        ∃ a ∈ V, ∃ b : H, t = TensorProduct.tmul k a b} := by
    apply Submodule.span_mono
    rintro t ⟨a, ha, b, rfl⟩
    exact ⟨a, hUV ha, b, rfl⟩
  -- Start with the span for 1 and add the spans for the elements of F.
  induction F using Finset.induction_on with
  | empty =>
      obtain ⟨V, hV, h1, hΔ⟩ := hsingle 1
      exact ⟨V, hV, h1, by simp, hΔ⟩
  | @insert x F _ ih =>
      obtain ⟨V, hV, h1, hF, hVΔ⟩ := ih
      obtain ⟨U, hU, hx, hUΔ⟩ := hsingle x
      let : FiniteDimensional k U := hU
      let : FiniteDimensional k V := hV
      refine ⟨U ⊔ V, inferInstance, Submodule.mem_sup_right h1, ?_, ?_⟩
      · intro y hy
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact Submodule.mem_sup_left hx
        · exact Submodule.mem_sup_right (hF y hy)
      · intro y hy
        obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hy
        rw [map_add]
        exact Submodule.add_mem _ (hmono le_sup_left (hUΔ a ha))
          (hmono le_sup_right (hVΔ b hb))

end Submission
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

theorem Submission.p05_fhe_coefficient_matrix_a5b449214a
    {k : Type*} [Field k] {H : Type*} [CommRing H] [HopfAlgebra k H]
    (V : Submodule k H) [FiniteDimensional k V]
    (hV : ∀ x ∈ V, Coalgebra.comul (R := k) x ∈
      Submodule.span k {t : TensorProduct k H H |
        ∃ a ∈ V, ∃ b : H, t = TensorProduct.tmul k a b}) :
    ∃ (n : ℕ) (c : Matrix (Fin n) (Fin n) H),
      (∀ x ∈ V, x ∈ Submodule.span k
        (Set.range (fun p : Fin n × Fin n => c p.1 p.2))) ∧
      (∀ i j : Fin n, Coalgebra.comul (R := k) (c i j) =
        ∑ l : Fin n, TensorProduct.tmul k (c i l) (c l j)) ∧
      (∀ i j : Fin n, Coalgebra.counit (R := k) (c i j) =
        if i = j then (1 : k) else 0) := by
  classical
  let n := Module.finrank k V
  let b : Module.Basis (Fin n) k V := Module.finBasis k V
  obtain ⟨c, hexp⟩ := Submission.p05_cm_basis_expansion_a5b449214a V n b hV
  refine ⟨n, c, ?_, Submission.p05_cm_coalgebra_laws_a5b449214a V n b c hexp⟩
  let W := Submodule.span k (Set.range (fun p : Fin n × Fin n => c p.1 p.2))
  have hb (j : Fin n) : (b j : H) ∈ W := by
    have h := Coalgebra.rTensor_counit_comul (R := k) (b j : H)
    rw [hexp j] at h
    have hsum : ∑ i, Coalgebra.counit (R := k) (b i : H) • c i j = (b j : H) := by
      simpa [map_sum] using congrArg (TensorProduct.lid k H) h
    rw [← hsum]
    exact Submodule.sum_mem W fun i _ =>
      Submodule.smul_mem W _ (Submodule.subset_span ⟨(i, j), rfl⟩)
  intro x hx
  have hsum : ∑ i, b.repr ⟨x, hx⟩ i • (b i : H) = x := by
    simpa only [map_sum, map_smul, Submodule.subtype_apply] using
      congrArg V.subtype (b.sum_repr ⟨x, hx⟩)
  rw [← hsum]
  exact Submodule.sum_mem W fun i _ => Submodule.smul_mem W _ (hb i)

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

theorem Submission.p05_fhe_determinant_inverse_a5b449214a
    {k : Type*} [Field k] {H : Type*} [CommRing H] [HopfAlgebra k H]
    (n : ℕ) (c : Matrix (Fin n) (Fin n) H)
    (hΔ : ∀ i j : Fin n, Coalgebra.comul (R := k) (c i j) =
      ∑ l : Fin n, TensorProduct.tmul k (c i l) (c l j))
    (hε : ∀ i j : Fin n, Coalgebra.counit (R := k) (c i j) =
      if i = j then (1 : k) else 0) :
    ∃ u : H, Matrix.det c * u = 1 ∧
      Coalgebra.comul (R := k) u = TensorProduct.tmul k u u ∧
      HopfAlgebra.antipode k u = Matrix.det c ∧
      (∀ i j : Fin n, HopfAlgebra.antipode k (c i j) = u * Matrix.adjugate c i j) := by
  obtain ⟨u, hdu, hadj⟩ := Submission.p05_di_antipode_adjugate_a5b449214a n c hΔ hε
  obtain ⟨hdΔ, hdε⟩ := Submission.p05_di_determinant_grouplike_a5b449214a n c hΔ hε
  have hd : IsGroupLikeElem k (Matrix.det c) := ⟨hdε, hdΔ⟩
  have hSu : HopfAlgebra.antipode k (Matrix.det c) = u :=
    left_inv_eq_right_inv hd.antipode_mul_cancel hdu
  refine ⟨u, hdu, ?_, ?_, hadj⟩
  · rw [← hSu]
    exact hd.antipode.comul_eq_tmul_self
  · rw [← hSu]
    exact hd.antipode_antipode

theorem Submission.p05_finite_hopf_envelope_a5b449214a :
    ∀ {k : Type*} [Field k] {H : Type*} [CommRing H] [HopfAlgebra k H]
      (F : Finset H), ∃ A : Subalgebra k H, (∀ x ∈ F, x ∈ A) ∧
      Algebra.FiniteType k A ∧
      (∀ x ∈ A, Coalgebra.comul (R := k) x ∈
        Submodule.span k {t : TensorProduct k H H |
          ∃ a ∈ A, ∃ b ∈ A, t = TensorProduct.tmul k a b}) ∧
      (∀ x ∈ A, HopfAlgebra.antipode k x ∈ A) := by
  intro k _ H _ _ F
  classical
  obtain ⟨V, hV, _, hF, hVΔ⟩ := Submission.p05_fhe_stable_subspace_a5b449214a (k := k) F
  let : FiniteDimensional k V := hV
  obtain ⟨n, c, hcV, hcΔ, hcε⟩ :=
    Submission.p05_fhe_coefficient_matrix_a5b449214a V hVΔ
  obtain ⟨u, _, huΔ, huS, hcS⟩ :=
    Submission.p05_fhe_determinant_inverse_a5b449214a n c hcΔ hcε
  let s : Set H := insert u (Set.range (fun p : Fin n × Fin n => c p.1 p.2))
  let A := Algebra.adjoin k s
  have hu : u ∈ A := Algebra.subset_adjoin (Set.mem_insert u _)
  have hc (i j : Fin n) : c i j ∈ A :=
    Algebra.subset_adjoin (Set.mem_insert_of_mem u ⟨(i, j), rfl⟩)
  have hspan : Submodule.span k (Set.range (fun p : Fin n × Fin n => c p.1 p.2)) ≤
      A.toSubmodule := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨i, j⟩, rfl⟩
    exact hc i j
  refine ⟨A, (fun x hx => hspan (hcV x (hF x hx))),
    Algebra.FiniteType.adjoin_of_finite ((Set.finite_range _).insert u), ?_, ?_⟩
  · -- The tensor-map range is a subalgebra with exactly the required underlying span.
    let T : Subalgebra k (H ⊗[k] H) := (Algebra.TensorProduct.map A.val A.val).range
    have hT : T.toSubmodule = Submodule.span k {t : H ⊗[k] H |
        ∃ a ∈ A, ∃ b ∈ A, t = a ⊗ₜ[k] b} := by
      change LinearMap.range (TensorProduct.map A.val.toLinearMap A.val.toLinearMap) = _
      rw [TensorProduct.range_map_eq_span_tmul]
      congr 1
      ext t
      constructor
      · rintro ⟨a, b, rfl⟩
        exact ⟨a, a.property, b, b.property, rfl⟩
      · rintro ⟨a, ha, b, hb, rfl⟩
        exact ⟨⟨a, ha⟩, ⟨b, hb⟩, rfl⟩
    have htmul (a b : H) (ha : a ∈ A) (hb : b ∈ A) : a ⊗ₜ[k] b ∈ T := by
      change a ⊗ₜ[k] b ∈ T.toSubmodule
      rw [hT]
      exact Submodule.subset_span ⟨a, ha, b, hb, rfl⟩
    have hΔA : A ≤ T.comap (Bialgebra.comulAlgHom k H) := by
      apply Algebra.adjoin_le
      intro x hx
      change Coalgebra.comul (R := k) x ∈ T
      rcases hx with hxu | ⟨⟨i, j⟩, rfl⟩
      · rw [hxu, huΔ]
        exact htmul u u hu hu
      · rw [hcΔ]
        exact T.sum_mem fun l _ => htmul (c i l) (c l j) (hc i l) (hc l j)
    intro x hx
    rw [← hT]
    exact hΔA hx
  · -- Determinants and adjugates of the coefficient matrix can be formed inside A.
    let cA : Matrix (Fin n) (Fin n) A := fun i j => ⟨c i j, hc i j⟩
    have hcA : A.val.mapMatrix cA = c := rfl
    have hdet : Matrix.det c ∈ A := by
      have hd := A.val.map_det cA
      rw [hcA] at hd
      exact hd ▸ (Matrix.det cA).property
    have hadj (i j : Fin n) : Matrix.adjugate c i j ∈ A := by
      have hm := congrArg (fun m : Matrix (Fin n) (Fin n) H => m i j)
        (A.val.map_adjugate cA)
      change ((Matrix.adjugate cA i j : A) : H) = Matrix.adjugate c i j at hm
      rw [← hm]
      exact (Matrix.adjugate cA i j).property
    have hSA : A ≤ A.comap (HopfAlgebra.antipodeAlgHom k H) := by
      apply Algebra.adjoin_le
      intro x hx
      change HopfAlgebra.antipode k x ∈ A
      rcases hx with hxu | ⟨⟨i, j⟩, rfl⟩
      · rw [hxu, huS]
        exact hdet
      · rw [hcS]
        exact A.mul_mem hu (hadj i j)
    exact fun x hx => hSA hx
