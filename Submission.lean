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
theorem Submission.p05_subalgebra_coinvariant_a5b449214a
    {k : Type*} [Field k] {H : Type*} [CommRing H] [HopfAlgebra k H]
    (K : Subalgebra k H)
    (hΔ : ∀ x ∈ K, Coalgebra.comul (R := k) x ∈
      Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K, ∃ b ∈ K, t = a ⊗ₜ[k] b})
    {B : Type*} [CommRing B] [Bialgebra k B] (q : BialgHom k H B)
    (hker : RingHom.ker (q : H →+* B) =
      Ideal.span {x : H | x ∈ K ∧ Coalgebra.counit (R := k) x = 0}) :
    K ≤ HopfAlgebra.hopfKer q := by
  have hqK (t : H) (ht : t ∈ K) :
      q t = algebraMap k B (Coalgebra.counit (R := k) t) := by
    have hmem : t - algebraMap k H (Coalgebra.counit (R := k) t) ∈
        RingHom.ker (q : H →+* B) := by
      rw [hker]
      exact Ideal.subset_span ⟨K.sub_mem ht (K.algebraMap_mem _), by simp⟩
    have hz : q (t - algebraMap k H (Coalgebra.counit (R := k) t)) = 0 := hmem
    have hscalar : q (algebraMap k H (Coalgebra.counit (R := k) t)) =
        algebraMap k B (Coalgebra.counit (R := k) t) :=
      (q : H →ₐ[k] B).commutes _
    rw [map_sub, hscalar] at hz
    exact sub_eq_zero.mp hz
  have hspan (z : H ⊗[k] H)
      (hz : z ∈ Submodule.span k
        {t : H ⊗[k] H | ∃ a ∈ K, ∃ b ∈ K, t = a ⊗ₜ[k] b}) :
      Algebra.TensorProduct.map (AlgHom.id k H) (q : H →ₐ[k] B) z =
        (Algebra.linearMap k B).lTensor H
          ((Coalgebra.counit (R := k)).lTensor H z) := by
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨a, _, b, hb, rfl⟩ := hz
      simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
        LinearMap.lTensor_tmul, Algebra.linearMap_apply, BialgHom.coe_toAlgHom]
      rw [hqK b hb]
    | zero => simp only [map_zero]
    | add z w _ _ hz hw => simp only [map_add, hz, hw]
    | smul c z _ hz => simp only [map_smul, hz]
  intro x hx
  rw [HopfAlgebra.mem_hopfKer_iff, HopfAlgebra.coaction_apply, hspan _ (hΔ x hx)]
  simp only [Coalgebra.lTensor_counit_comul, LinearMap.lTensor_tmul,
    Algebra.linearMap_apply, map_one]
theorem Submission.p05_translation_left_inverse_a5b449214a
    {k : Type*} [Field k] {H : Type*} [CommRing H] [HopfAlgebra k H]
    (K : Subalgebra k H) {B : Type*} [CommRing B] [Bialgebra k B]
    (q : BialgHom k H B)
    (β : (TensorProduct K H H) →ₐ[k] (TensorProduct k H B))
    (hβ : ∀ a b : H, β (TensorProduct.tmul K a b) =
      (TensorProduct.tmul k a (1 : B)) * HopfAlgebra.coaction q b)
    (σ : B →ₐ[k] (TensorProduct K H H))
    (hσ : ∀ b : H, σ (q b) =
      Algebra.TensorProduct.mapOfCompatibleSMul K k k H H
        (TensorProduct.map (HopfAlgebra.antipode k) (LinearMap.id : H →ₗ[k] H)
          (Coalgebra.comul (R := k) b))) :
    ∃ γ : (TensorProduct k H B) →ₐ[k] (TensorProduct K H H),
      (∀ (a : H) (c : B), γ (TensorProduct.tmul k a c) =
        (TensorProduct.tmul K a (1 : H)) * σ c) ∧ Function.LeftInverse γ β := by
  let C := Algebra.TensorProduct.mapOfCompatibleSMul K k k H H
  let γ : H ⊗[k] B →ₐ[k] H ⊗[K] H :=
    Algebra.TensorProduct.lift
      (Algebra.TensorProduct.includeLeft : H →ₐ[k] H ⊗[K] H) σ
      (fun _ _ => Commute.all _ _)
  have hγ (a : H) (c : B) : γ (a ⊗ₜ[k] c) = (a ⊗ₜ[K] (1 : H)) * σ c := rfl
  let mS : H ⊗[k] H →ₗ[k] H :=
    (LinearMap.mul' k H).comp ((HopfAlgebra.antipode k).lTensor H)
  let F : H ⊗[k] (H ⊗[k] H) →ₗ[k] H ⊗[k] H :=
    (mS.rTensor H).comp (TensorProduct.assoc k H H H).symm.toLinearMap
  have hF (a b c : H) :
      F (a ⊗ₜ[k] (b ⊗ₜ[k] c)) = (a * HopfAlgebra.antipode k b) ⊗ₜ[k] c := rfl
  have hmS : mS.comp (Coalgebra.comul (R := k)) =
      (Algebra.linearMap k H).comp (Coalgebra.counit (R := k)) :=
    HopfAlgebra.mul_antipode_lTensor_comul
  have hcancel (b : H) :
      F ((Coalgebra.comul (R := k)).lTensor H (Coalgebra.comul b)) =
        (1 : H) ⊗ₜ[k] b := by
    change mS.rTensor H ((TensorProduct.assoc k H H H).symm
      ((Coalgebra.comul (R := k)).lTensor H (Coalgebra.comul b))) = _
    rw [Coalgebra.coassoc_symm_apply, ← LinearMap.rTensor_comp_apply, hmS,
      LinearMap.rTensor_comp_apply, Coalgebra.rTensor_counit_comul]
    simp
  have htranslate (a : H) (t : H ⊗[k] H) :
      (a ⊗ₜ[K] (1 : H)) * C
          (TensorProduct.map (HopfAlgebra.antipode k) (LinearMap.id : H →ₗ[k] H) t) =
        C (F (a ⊗ₜ[k] t)) := by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul b c => simp [C, hF, Algebra.TensorProduct.tmul_mul_tmul]
    | add x y hx hy => simp [TensorProduct.tmul_add, mul_add, hx, hy]
  have hcomp (t : H ⊗[k] H) :
      γ (Algebra.TensorProduct.map (AlgHom.id k H) (q : H →ₐ[k] B) t) =
        C (F ((Coalgebra.comul (R := k)).lTensor H t)) := by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
        BialgHom.coe_toAlgHom, LinearMap.lTensor_tmul, hγ, hσ]
      exact htranslate a (Coalgebra.comul b)
    | add x y hx hy => simp [hx, hy]
  have hcoaction (b : H) : γ (HopfAlgebra.coaction q b) = (1 : H) ⊗ₜ[K] b := by
    rw [HopfAlgebra.coaction_apply, hcomp, hcancel]
    rfl
  refine ⟨γ, hγ, ?_⟩
  intro t
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    rw [hβ, map_mul, hγ, map_one, mul_one, hcoaction]
    simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  | add x y hx hy => simp [hx, hy]
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
theorem Submission.p05_translation_descends_a5b449214a
    {k : Type*} [Field k] {H : Type*} [CommRing H] [HopfAlgebra k H]
    (K : Subalgebra k H)
    (hΔ : ∀ x ∈ K, Coalgebra.comul (R := k) x ∈
      Submodule.span k {t : TensorProduct k H H |
        ∃ a ∈ K, ∃ b ∈ K, t = TensorProduct.tmul k a b})
    (hS : ∀ x ∈ K, HopfAlgebra.antipode k x ∈ K)
    {B : Type*} [CommRing B] [Bialgebra k B] (q : BialgHom k H B)
    (hq : Function.Surjective q)
    (hker : RingHom.ker (q : H →+* B) =
      Ideal.span {x : H | x ∈ K ∧ Coalgebra.counit (R := k) x = 0}) :
    ∃ σ : B →ₐ[k] (TensorProduct K H H), ∀ b : H,
      σ (q b) = Algebra.TensorProduct.mapOfCompatibleSMul K k k H H
        (TensorProduct.map (HopfAlgebra.antipode k) (LinearMap.id : H →ₗ[k] H)
          (Coalgebra.comul (R := k) b)) := by
  let C := Algebra.TensorProduct.mapOfCompatibleSMul K k k H H
  let s : TensorProduct k H H →ₗ[k] TensorProduct k H H := TensorProduct.map (HopfAlgebra.antipode k) (LinearMap.id : H →ₗ[k] H)
  let i : H →ₗ[k] TensorProduct K H H :=
    ((Algebra.TensorProduct.includeRight : H →ₐ[K] TensorProduct K H H).restrictScalars k).toLinearMap
  let τ : H →ₐ[k] TensorProduct K H H :=
    C.comp ((Algebra.TensorProduct.map (HopfAlgebra.antipodeAlgHom k H)
      (AlgHom.id k H)).comp (Bialgebra.comulAlgHom k H))
  have hbalance : ∀ z ∈ Submodule.span k {t : TensorProduct k H H |
      ∃ a ∈ K, ∃ b ∈ K, t = TensorProduct.tmul k a b},
      (C.toLinearMap.comp s) z = (i.comp ((LinearMap.mul' k H).comp s)) z := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨a, ha, b, _, rfl⟩ := hz
      change HopfAlgebra.antipode k a ⊗ₜ[K] b =
        (1 : H) ⊗ₜ[K] (HopfAlgebra.antipode k a * b)
      simpa [Algebra.smul_def] using
        (TensorProduct.smul_tmul (⟨HopfAlgebra.antipode k a, hS a ha⟩ : K) (1 : H) b)
    | zero => simp only [map_zero]
    | add x y _ _ hx hy => simp only [map_add, hx, hy]
    | smul r x _ hx => simp only [map_smul, hx]
  have hτker : RingHom.ker (q : H →+* B) ≤ RingHom.ker τ.toRingHom := by
    rw [hker]
    apply Ideal.span_le.mpr
    intro x hx
    change τ x = 0
    change (C.toLinearMap.comp s) (Coalgebra.comul (R := k) x) = 0
    rw [hbalance _ (hΔ x hx.1)]
    change i (LinearMap.mul' k H
      ((HopfAlgebra.antipode k).rTensor H (Coalgebra.comul (R := k) x))) = 0
    rw [HopfAlgebra.mul_antipode_rTensor_comul_apply, hx.2, map_zero, map_zero]
  refine ⟨AlgHom.liftOfSurjective q.toAlgHom hq τ hτker, ?_⟩
  intro b
  exact AlgHom.liftOfSurjective_apply q.toAlgHom hq τ hτker b
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

theorem Submission.p05_hte_sshs_br_comul_alg_lift_a5b449214a
    {k : Type*} [Field k] {H : Type*} [CommRing H] [Bialgebra k H]
    (D : Subalgebra k H)
    (_hΔ : ∀ x ∈ D, Coalgebra.comul (R := k) x ∈
      Submodule.span k {t : TensorProduct k H H |
        ∃ a ∈ D, ∃ b ∈ D, t = TensorProduct.tmul k a b}) :
    ∃ δ : D →ₐ[k] TensorProduct k D D, ∀ d : D,
      (Algebra.TensorProduct.map D.val D.val) (δ d) =
        Coalgebra.comul (R := k) (d : H) := by
  classical
  let i : D →ₗ[k] H := D.val.toLinearMap
  obtain ⟨r, hr⟩ := i.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  have hri (d : D) : r (d : H) = d := LinearMap.congr_fun hr d
  let J : TensorProduct k D D →ₐ[k] TensorProduct k H H :=
    Algebra.TensorProduct.map D.val D.val
  let R : TensorProduct k H H →ₗ[k] TensorProduct k D D := TensorProduct.map r r
  have hRJ : Function.LeftInverse R J := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul d e =>
      change r (d : H) ⊗ₜ[k] r (e : H) = d ⊗ₜ[k] e
      rw [hri, hri]
    | add z w hz hw => simp only [map_add, hz, hw]
  have hspan : Submodule.span k {t : TensorProduct k H H |
      ∃ a ∈ D, ∃ b ∈ D, t = TensorProduct.tmul k a b} ≤
        LinearMap.range J.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro t ⟨a, ha, b, hb, rfl⟩
    exact ⟨(⟨a, ha⟩ : D) ⊗ₜ[k] (⟨b, hb⟩ : D), rfl⟩
  let δ : D →ₗ[k] TensorProduct k D D :=
    R.comp ((Coalgebra.comul (R := k)).comp i)
  have hδ (d : D) : J (δ d) = Coalgebra.comul (R := k) (d : H) := by
    obtain ⟨z, hz⟩ := hspan (_hΔ (d : H) d.property)
    change J (R (Coalgebra.comul (R := k) (d : H))) = _
    change J z = Coalgebra.comul (R := k) (d : H) at hz
    rw [← hz, hRJ z]
  refine ⟨AlgHom.ofLinearMap δ ?_ ?_, hδ⟩
  · apply hRJ.injective
    rw [hδ, map_one]
    exact Bialgebra.comul_one
  · intro d e
    apply hRJ.injective
    rw [hδ, map_mul, hδ, hδ]
    exact Bialgebra.comul_mul (R := k) (d : H) (e : H)
