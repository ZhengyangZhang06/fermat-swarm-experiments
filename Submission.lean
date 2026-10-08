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


theorem Submission.p05_hte_sshs_antipode_lift_a5b449214a
    {k : Type*} [Field k] {A : Type*} [CommRing A] [bA : Bialgebra k A]
    {H : Type*} [CommRing H] [HopfAlgebra k H]
    (ι : BialgHom k A H) (hι : Function.Injective ι)
    (hS : ∀ a : A, ∃ b : A, ι b = HopfAlgebra.antipode k (ι a)) :
    ∃ hA : HopfAlgebra k A, hA.toHopfAlgebraStruct.toBialgebra = bA ∧
      (letI : Algebra k A := hA.toHopfAlgebraStruct.toBialgebra.toAlgebra
       letI : Module k A := Algebra.toModule
       letI : Bialgebra k A := hA.toHopfAlgebraStruct.toBialgebra
       letI : HopfAlgebra k A := hA
       ∀ a : A, ι (HopfAlgebra.antipode k a) = HopfAlgebra.antipode k (ι a)) := by
  classical
  let S : A → A := fun a => Classical.choose (hS a)
  have hSι (a : A) : ι (S a) = HopfAlgebra.antipode k (ι a) :=
    Classical.choose_spec (hS a)
  let s : A →ₗ[k] A :=
    { toFun := S
      map_add' := fun a b => hι (by simp only [hSι, map_add])
      map_smul' := fun c a => hι (by simp only [hSι, map_smul, RingHom.id_apply]) }
  have hs (a : A) : ι (s a) = HopfAlgebra.antipode k (ι a) := hSι a
  have hr :
      (ι : A →ₗ[k] H) ∘ₗ (LinearMap.mul' k A ∘ₗ s.rTensor A) =
        (LinearMap.mul' k H ∘ₗ (HopfAlgebra.antipode k).rTensor H) ∘ₗ
          TensorProduct.map (ι : A →ₗ[k] H) (ι : A →ₗ[k] H) := by
    apply TensorProduct.ext'
    intro a b
    simp [hs]
  have hl :
      (ι : A →ₗ[k] H) ∘ₗ (LinearMap.mul' k A ∘ₗ s.lTensor A) =
        (LinearMap.mul' k H ∘ₗ (HopfAlgebra.antipode k).lTensor H) ∘ₗ
          TensorProduct.map (ι : A →ₗ[k] H) (ι : A →ₗ[k] H) := by
    apply TensorProduct.ext'
    intro a b
    simp [hs]
  have hleft :
      LinearMap.mul' k A ∘ₗ s.rTensor A ∘ₗ Coalgebra.comul =
        Algebra.linearMap k A ∘ₗ Coalgebra.counit := by
    ext a
    apply hι
    change ι (LinearMap.mul' k A (s.rTensor A (Coalgebra.comul a))) =
      ι (algebraMap k A (Coalgebra.counit a))
    calc
      _ = LinearMap.mul' k H ((HopfAlgebra.antipode k).rTensor H
          (TensorProduct.map (ι : A →ₗ[k] H) (ι : A →ₗ[k] H)
            (Coalgebra.comul a))) := LinearMap.congr_fun hr _
      _ = algebraMap k H (Coalgebra.counit (ι a)) := by
        rw [CoalgHomClass.map_comp_comul_apply]
        exact HopfAlgebra.mul_antipode_rTensor_comul_apply (ι a)
      _ = _ := by simp only [CoalgHomClass.counit_comp_apply, AlgHomClass.commutes]
  have hright :
      LinearMap.mul' k A ∘ₗ s.lTensor A ∘ₗ Coalgebra.comul =
        Algebra.linearMap k A ∘ₗ Coalgebra.counit := by
    ext a
    apply hι
    change ι (LinearMap.mul' k A (s.lTensor A (Coalgebra.comul a))) =
      ι (algebraMap k A (Coalgebra.counit a))
    calc
      _ = LinearMap.mul' k H ((HopfAlgebra.antipode k).lTensor H
          (TensorProduct.map (ι : A →ₗ[k] H) (ι : A →ₗ[k] H)
            (Coalgebra.comul a))) := LinearMap.congr_fun hl _
      _ = algebraMap k H (Coalgebra.counit (ι a)) := by
        rw [CoalgHomClass.map_comp_comul_apply]
        exact HopfAlgebra.mul_antipode_lTensor_comul_apply (ι a)
      _ = _ := by simp only [CoalgHomClass.counit_comp_apply, AlgHomClass.commutes]
  let hA : HopfAlgebra k A :=
    { toBialgebra := bA
      antipode := s
      mul_antipode_rTensor_comul := hleft
      mul_antipode_lTensor_comul := hright }
  exact ⟨hA, rfl, hs⟩
theorem Submission.p05_ftzw_supported_relations_vanish_a5b449214a :
    ∀ {k : Type*} [CommRing k] {D : Type*} [CommRing D] [Algebra k D] {M : Type*} [AddCommGroup M] [Module D M] {P : Type*} [AddCommGroup P] [Module D P] (A : Subalgebra k D) (N : Submodule A M) (m : N) (p : P), let b : M → P → FreeAbelianGroup (M × P) := fun u z => FreeAbelianGroup.of (u, z); b (m : M) p ∈ AddSubgroup.closure {r : FreeAbelianGroup (M × P) | (∃ z : P, r = b 0 z) ∨ (∃ u : M, u ∈ N ∧ r = b u 0) ∨ (∃ (u v : M) (z : P), u ∈ N ∧ v ∈ N ∧ r = b (u + v) z - b u z - b v z) ∨ (∃ (u : M) (z w : P), u ∈ N ∧ r = b u (z + w) - b u z - b u w) ∨ (∃ (d : D) (u : M) (z : P), d ∈ A ∧ u ∈ N ∧ r = b (d • u) z - b u (d • z))} → (TensorProduct.tmul A m p : TensorProduct A N P) = 0 := by
  classical
  intro k _ D _ _ M _ _ P _ _ A N m p
  dsimp only
  intro h
  let bN : N → P → FreeAbelianGroup (N × P) :=
    fun n z => FreeAbelianGroup.of (n, z)
  let J : FreeAbelianGroup (N × P) →+ FreeAbelianGroup (M × P) :=
    FreeAbelianGroup.lift fun t : N × P => FreeAbelianGroup.of ((t.1 : M), t.2)
  let E : FreeAbelianGroup (N × P) →+ TensorProduct A N P :=
    FreeAbelianGroup.lift fun t : N × P => TensorProduct.tmul A t.1 t.2
  have hcoeff (t : N × P) :
      (FreeAbelianGroup.coeff ((t.1 : M), t.2)).comp J = FreeAbelianGroup.coeff t := by
    rcases t with ⟨n', z'⟩
    apply FreeAbelianGroup.lift_ext
    rintro ⟨n, z⟩
    change (J (FreeAbelianGroup.of (n, z))).toFinsupp ((n' : M), z') =
      (FreeAbelianGroup.of (n, z)).toFinsupp (n', z')
    rw [show J (FreeAbelianGroup.of (n, z)) =
      FreeAbelianGroup.of ((n : M), z) from FreeAbelianGroup.lift_apply_of _ _,
      FreeAbelianGroup.toFinsupp_of, FreeAbelianGroup.toFinsupp_of]
    simp only [Finsupp.single_apply, Prod.mk.injEq, Subtype.ext_iff]
  have hJ : Function.Injective J := by
    intro x y hxy
    apply (FreeAbelianGroup.equivFinsupp (N × P)).injective
    ext t
    change FreeAbelianGroup.coeff t x = FreeAbelianGroup.coeff t y
    rw [← hcoeff t]
    exact congrArg (FreeAbelianGroup.coeff ((t.1 : M), t.2)) hxy
  have hmem : FreeAbelianGroup.of ((m : M), p) ∈ E.ker.map J := by
    apply ((AddSubgroup.closure_le _).mpr ?_) h
    intro r hr
    rcases hr with ⟨z, rfl⟩ | ⟨u, hu, rfl⟩ | ⟨u, v, z, hu, hv, rfl⟩ |
      ⟨u, z, w, hu, rfl⟩ | ⟨d, u, z, hd, hu, rfl⟩
    · refine ⟨bN 0 z, ?_, ?_⟩
      · change E (bN 0 z) = 0
        simp [E, bN]
      · simp [J, bN]
    · refine ⟨bN ⟨u, hu⟩ 0, ?_, ?_⟩
      · change E (bN ⟨u, hu⟩ 0) = 0
        simp [E, bN]
      · simp [J, bN]
    · refine ⟨bN (⟨u, hu⟩ + ⟨v, hv⟩) z - bN ⟨u, hu⟩ z - bN ⟨v, hv⟩ z,
        ?_, ?_⟩
      · change E _ = 0
        simp only [map_sub, E, bN, FreeAbelianGroup.lift_apply_of, TensorProduct.add_tmul]
        abel
      · simp [J, bN]
    · refine ⟨bN ⟨u, hu⟩ (z + w) - bN ⟨u, hu⟩ z - bN ⟨u, hu⟩ w, ?_, ?_⟩
      · change E _ = 0
        simp only [map_sub, E, bN, FreeAbelianGroup.lift_apply_of, TensorProduct.tmul_add]
        abel
      · simp [J, bN]
    · refine ⟨bN ((⟨d, hd⟩ : A) • (⟨u, hu⟩ : N)) z -
        bN ⟨u, hu⟩ ((⟨d, hd⟩ : A) • z), ?_, ?_⟩
      · change E _ = 0
        simp only [map_sub, E, bN, FreeAbelianGroup.lift_apply_of,
          TensorProduct.smul_tmul, sub_self]
      · simp only [map_sub, J, bN, FreeAbelianGroup.lift_apply_of]
        rfl
  have hNm : bN m p ∈ E.ker :=
    (AddSubgroup.mem_map_iff_mem hJ).mp hmem
  change E (bN m p) = 0 at hNm
  simpa only [E, bN, FreeAbelianGroup.lift_apply_of] using hNm
theorem Submission.p05_fr_rhm_tensor_ideal_descent_a5b449214a
    {k : Type*} [Field k] {A : Type*} [CommRing A] [Algebra k A]
    {H : Type*} [CommRing H] [Algebra k H]
    (f : A →ₗ[k] H) (_hf : Function.Injective f) (J : Ideal A)
    (t : TensorProduct k A A)
    (_ht : TensorProduct.map (LinearMap.id : A →ₗ[k] A) f t ∈
      Ideal.map (Algebra.TensorProduct.includeLeft :
        A →ₐ[k] TensorProduct k A H).toRingHom J) :
    t ∈ Submodule.span k {z : TensorProduct k A A |
      ∃ a ∈ J, ∃ b : A, z = TensorProduct.tmul k a b} := by
  classical
  let E : Submodule k (A ⊗[k] H) :=
    Submodule.span k {z : A ⊗[k] H | ∃ a ∈ J, ∃ b : H, z = a ⊗ₜ[k] b}
  have hmul (r z : A ⊗[k] H) (hz : z ∈ E) : r * z ∈ E := by
    induction hz using Submodule.span_induction with
    | mem z hz =>
      rcases hz with ⟨a, ha, b, rfl⟩
      induction r using TensorProduct.induction_on with
      | zero => simpa only [zero_mul] using E.zero_mem
      | tmul c d =>
        rw [Algebra.TensorProduct.tmul_mul_tmul]
        exact Submodule.subset_span ⟨c * a, J.mul_mem_left c ha, d * b, rfl⟩
      | add x y hx hy =>
        simpa only [add_mul] using E.add_mem hx hy
    | zero => simpa only [mul_zero] using E.zero_mem
    | add x y hx hy ihx ihy =>
      simpa only [mul_add] using E.add_mem ihx ihy
    | smul c x hx ih =>
      simpa only [mul_smul_comm] using E.smul_mem c ih
  have hE : TensorProduct.map (LinearMap.id : A →ₗ[k] A) f t ∈ E := by
    change TensorProduct.map (LinearMap.id : A →ₗ[k] A) f t ∈
      Submodule.span (A ⊗[k] H)
        ((Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] H).toRingHom ''
          (J : Set A)) at _ht
    refine Submodule.span_induction (p := fun z _ => z ∈ E) ?_ ?_ ?_ ?_ _ht
    · rintro z ⟨a, ha, rfl⟩
      exact Submodule.subset_span ⟨a, ha, 1, rfl⟩
    · exact E.zero_mem
    · intro x y _ _ hx hy
      exact E.add_mem hx hy
    · intro r z _ hz
      exact hmul r z hz
  obtain ⟨g, hg⟩ := f.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr _hf)
  let F : Submodule k (A ⊗[k] A) :=
    Submodule.span k {z : A ⊗[k] A | ∃ a ∈ J, ∃ b : A, z = a ⊗ₜ[k] b}
  have hdesc (z : A ⊗[k] H) (hz : z ∈ E) :
      TensorProduct.map (LinearMap.id : A →ₗ[k] A) g z ∈ F := by
    induction hz using Submodule.span_induction with
    | mem z hz =>
      rcases hz with ⟨a, ha, b, rfl⟩
      exact Submodule.subset_span ⟨a, ha, g b, by simp⟩
    | zero => simpa only [map_zero] using F.zero_mem
    | add x y hx hy ihx ihy =>
      simpa only [map_add] using F.add_mem ihx ihy
    | smul c x hx ih =>
      simpa only [map_smul] using F.smul_mem c ih
  have hcomp (z : A ⊗[k] A) :
      TensorProduct.map (LinearMap.id : A →ₗ[k] A) g
        (TensorProduct.map (LinearMap.id : A →ₗ[k] A) f z) = z := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      have hgf : g (f b) = b := LinearMap.congr_fun hg b
      simp [hgf]
    | add x y hx hy => simp only [map_add, hx, hy]
  simpa only [hcomp] using hdesc _ hE
theorem Submission.p05_ftzw_tensor_relation_kernel_a5b449214a :
    ∀ {D : Type*} [CommRing D] {M : Type*} [AddCommGroup M] [Module D M]
      {P : Type*} [AddCommGroup P] [Module D P],
      let b : M → P → FreeAbelianGroup (M × P) := fun u z => FreeAbelianGroup.of (u, z)
      (FreeAbelianGroup.lift (fun x : M × P => TensorProduct.tmul D x.1 x.2)).ker =
        AddSubgroup.closure {r : FreeAbelianGroup (M × P) |
          (∃ z : P, r = b 0 z) ∨ (∃ u : M, r = b u 0) ∨
          (∃ (u v : M) (z : P), r = b (u + v) z - b u z - b v z) ∨
          (∃ (u : M) (z w : P), r = b u (z + w) - b u z - b u w) ∨
          (∃ (d : D) (u : M) (z : P), r = b (d • u) z - b u (d • z))} := by
  intro D _ M _ _ P _ _
  let b : M → P → FreeAbelianGroup (M × P) := fun u z => FreeAbelianGroup.of (u, z)
  let T : Set (FreeAbelianGroup (M × P)) := {r |
    (∃ z : P, r = b 0 z) ∨ (∃ u : M, r = b u 0) ∨
    (∃ (u v : M) (z : P), r = b (u + v) z - b u z - b v z) ∨
    (∃ (u : M) (z w : P), r = b u (z + w) - b u z - b u w) ∨
    (∃ (d : D) (u : M) (z : P), r = b (d • u) z - b u (d • z))}
  let R := AddSubgroup.closure T
  let E := FreeAbelianGroup.lift (fun x : M × P => TensorProduct.tmul D x.1 x.2)
  change E.ker = R
  have hRE : R ≤ E.ker := by
    apply (AddSubgroup.closure_le _).mpr
    intro r hr
    change E r = 0
    rcases hr with ⟨z, rfl⟩ | ⟨u, rfl⟩ | ⟨u, v, z, rfl⟩ |
      ⟨u, z, w, rfl⟩ | ⟨d, u, z, rfl⟩
    · simp [E, b]
    · simp [E, b]
    · simp [E, b, TensorProduct.add_tmul]
    · simp [E, b, TensorProduct.tmul_add]
    · simp [E, b, TensorProduct.smul_tmul]
  let π := QuotientAddGroup.mk' R
  have hrel {r : FreeAbelianGroup (M × P)} (hr : r ∈ T) : π r = 0 :=
    (QuotientAddGroup.eq_zero_iff r).mpr (AddSubgroup.subset_closure hr)
  have hzero_left (z : P) : π (b 0 z) = 0 :=
    hrel (Or.inl ⟨z, rfl⟩)
  have hzero_right (u : M) : π (b u 0) = 0 :=
    hrel (Or.inr (Or.inl ⟨u, rfl⟩))
  have hadd_left (u v : M) (z : P) :
      π (b (u + v) z) = π (b u z) + π (b v z) := by
    have h := hrel (Or.inr (Or.inr (Or.inl ⟨u, v, z, rfl⟩)))
    simpa only [map_sub, map_add, sub_sub, sub_eq_zero] using h
  have hadd_right (u : M) (z w : P) :
      π (b u (z + w)) = π (b u z) + π (b u w) := by
    have h := hrel (Or.inr (Or.inr (Or.inr (Or.inl ⟨u, z, w, rfl⟩))))
    simpa only [map_sub, map_add, sub_sub, sub_eq_zero] using h
  have hbalance (d : D) (u : M) (z : P) :
      π (b (d • u) z) = π (b u (d • z)) := by
    have h := hrel (Or.inr (Or.inr (Or.inr (Or.inr ⟨d, u, z, rfl⟩))))
    simpa only [map_sub, sub_eq_zero] using h
  let β : M →+ P →+ FreeAbelianGroup (M × P) ⧸ R :=
    { toFun := fun u =>
        { toFun := fun z => π (b u z)
          map_zero' := hzero_right u
          map_add' := hadd_right u }
      map_zero' := by
        ext z
        exact hzero_left z
      map_add' := by
        intro u v
        ext z
        exact hadd_left u v z }
  let L : M ⊗[D] P →+ FreeAbelianGroup (M × P) ⧸ R :=
    TensorProduct.liftAddHom β hbalance
  have hcomp : L.comp E = π := by
    apply FreeAbelianGroup.lift_ext
    intro x
    rcases x with ⟨u, z⟩
    simp [E, L, β, b]
  apply le_antisymm _ hRE
  intro g hg
  apply (QuotientAddGroup.eq_zero_iff g).mp
  change π g = 0
  rw [← hcomp]
  change L (E g) = 0
  rw [show E g = 0 from hg, map_zero]
theorem Submission.p05_fr_rhm_bcsi_twisted_presentation_a5b449214a
    {S : Type*} [CommRing S] {L : Type*} [AddCommGroup L] [Module S L]
    (n p : ℕ) (P : Matrix (Fin n) (Fin p) S) (q : (Fin n → S) →ₗ[S] L)
    (_hq : Function.Surjective q)
    (_hker : LinearMap.ker q = LinearMap.range P.mulVecLin)
    (θ : S ≃+* S) (T : L ≃+ L)
    (_hT : ∀ (s : S) (x : L), T (s • x) = θ s • T x) :
    ∃ qθ : (Fin n → S) →ₗ[S] L,
      (∀ b : Fin n → S, qθ b = T (q (fun i => θ.symm (b i)))) ∧
      Function.Surjective qθ ∧
      LinearMap.ker qθ = LinearMap.range (P.map θ.toRingHom).mulVecLin := by
  let qθ : (Fin n → S) →ₗ[S] L :=
    { toFun := fun b => T (q (fun i => θ.symm (b i)))
      map_add' := by
        intro b c
        have h : (fun i => θ.symm ((b + c) i)) =
            (fun i => θ.symm (b i)) + (fun i => θ.symm (c i)) := by
          ext i
          exact map_add θ.symm (b i) (c i)
        rw [h, map_add, map_add]
      map_smul' := by
        intro s b
        have h : (fun i => θ.symm ((s • b) i)) =
            θ.symm s • (fun i => θ.symm (b i)) := by
          ext i
          exact map_mul θ.symm s (b i)
        change T (q (fun i => θ.symm ((s • b) i))) =
          s • T (q (fun i => θ.symm (b i)))
        rw [h, map_smul, _hT, θ.apply_symm_apply] }
  refine ⟨qθ, fun _ => rfl, ?_, ?_⟩
  · intro y
    obtain ⟨a, ha⟩ := _hq (T.symm y)
    refine ⟨fun i => θ (a i), ?_⟩
    change T (q (fun i => θ.symm (θ (a i)))) = y
    simpa only [θ.symm_apply_apply, ha] using T.apply_symm_apply y
  · ext b
    rw [LinearMap.mem_ker, LinearMap.mem_range]
    constructor
    · intro hb
      change T (q (fun i => θ.symm (b i))) = 0 at hb
      have hb0 : q (fun i => θ.symm (b i)) = 0 :=
        T.injective (by simpa only [map_zero] using hb)
      have hbker := LinearMap.mem_ker.mpr hb0
      rw [_hker] at hbker
      obtain ⟨c, hc⟩ := LinearMap.mem_range.mp hbker
      refine ⟨fun j => θ (c j), ?_⟩
      funext i
      calc
        (P.map θ.toRingHom).mulVecLin (fun j => θ (c j)) i =
            θ (P.mulVecLin c i) := (θ.toRingHom.map_mulVec P c i).symm
        _ = b i := by rw [congrFun hc i, θ.apply_symm_apply]
    · rintro ⟨d, rfl⟩
      have hA : (fun i => θ.symm ((P.map θ.toRingHom).mulVecLin d i)) =
          P.mulVecLin (fun j => θ.symm (d j)) := by
        ext i
        simp [Matrix.mulVec, dotProduct, map_sum]
      have hzero : q (P.mulVecLin (fun j => θ.symm (d j))) = 0 := by
        apply LinearMap.mem_ker.mp
        rw [_hker]
        exact LinearMap.mem_range.mpr ⟨_, rfl⟩
      change T (q (fun i => θ.symm ((P.map θ.toRingHom).mulVecLin d i))) = 0
      rw [hA, hzero, map_zero]
theorem Submission.p05_ct_comodule_a5b449214a
    {k : Type*} [Field k] {H : Type*} [CommRing H] [HopfAlgebra k H]
    {M : Type*} [AddCommGroup M] [Module k M]
    (μ : M →ₗ[k] TensorProduct k M H)
    (_hcoassoc : ∀ m : M, TensorProduct.assoc k M H H
      ((TensorProduct.map μ (LinearMap.id : H →ₗ[k] H)) (μ m)) =
      (TensorProduct.map (LinearMap.id : M →ₗ[k] M)
        (Coalgebra.comul (R := k))) (μ m))
    (_hcounit : ∀ m : M, TensorProduct.rid k M
      ((TensorProduct.map (LinearMap.id : M →ₗ[k] M)
        (Coalgebra.counit (R := k))) (μ m)) = m) :
    ∃ T : TensorProduct k M H ≃ₗ[k] TensorProduct k M H,
      ∀ (m : M) (h : H), T (TensorProduct.tmul k m h) =
        TensorProduct.map (LinearMap.id : M →ₗ[k] M) (LinearMap.mulLeft k h) (μ m) := by
  let P (f g : H →ₗ[k] H) : H ⊗[k] H →ₗ[k] H :=
    LinearMap.mul' k H ∘ₗ TensorProduct.map f g
  let F (f : H →ₗ[k] H) : M ⊗[k] H →ₗ[k] M ⊗[k] H :=
    TensorProduct.map LinearMap.id (P f LinearMap.id) ∘ₗ
      (TensorProduct.assoc k M H H).toLinearMap ∘ₗ
        TensorProduct.map μ LinearMap.id
  have hF (f : H →ₗ[k] H) (m : M) (h : H) :
      F f (m ⊗ₜ[k] h) =
        TensorProduct.map LinearMap.id (LinearMap.mulRight k h ∘ₗ f) (μ m) := by
    change TensorProduct.map LinearMap.id (P f LinearMap.id)
      (TensorProduct.assoc k M H H ((μ m) ⊗ₜ[k] h)) = _
    induction μ m using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [P]
    | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]
  have hcomp (f g : H →ₗ[k] H) (h : H) (z : M ⊗[k] H) :
      F f (TensorProduct.map LinearMap.id (LinearMap.mulRight k h ∘ₗ g) z) =
        TensorProduct.map LinearMap.id (LinearMap.mulRight k h ∘ₗ P f g)
          (TensorProduct.assoc k M H H (TensorProduct.map μ LinearMap.id z)) := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul m b =>
      simp only [TensorProduct.map_tmul, LinearMap.id_apply, LinearMap.comp_apply,
        LinearMap.mulRight_apply, hF]
      induction μ m using TensorProduct.induction_on with
      | zero => simp
      | tmul x y => simp [P, mul_assoc]
      | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hcancel (f g : H →ₗ[k] H)
      (hfg : P f g ∘ₗ Coalgebra.comul (R := k) =
        Algebra.linearMap k H ∘ₗ Coalgebra.counit (R := k)) :
      F f ∘ₗ F g = LinearMap.id := by
    apply TensorProduct.ext'
    intro m h
    simp only [LinearMap.comp_apply, LinearMap.id_apply, hF, hcomp, _hcoassoc]
    rw [TensorProduct.map_map, LinearMap.id_comp, LinearMap.comp_assoc, hfg]
    have hc (z : M ⊗[k] H) :
        TensorProduct.map (LinearMap.id : M →ₗ[k] M)
          (LinearMap.mulRight k h ∘ₗ Algebra.linearMap k H ∘ₗ
            Coalgebra.counit (R := k)) z =
          TensorProduct.rid k M
            (TensorProduct.map LinearMap.id (Coalgebra.counit (R := k)) z) ⊗ₜ[k] h := by
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul x y => simp [Algebra.smul_def, TensorProduct.smul_tmul]
      | add x y hx hy => simp only [map_add, TensorProduct.add_tmul, hx, hy]
    rw [hc, _hcounit]
  have hleft : F (HopfAlgebra.antipode k) ∘ₗ F LinearMap.id = LinearMap.id :=
    hcancel _ _ (HopfAlgebra.mul_antipode_rTensor_comul (R := k) (A := H))
  have hright : F LinearMap.id ∘ₗ F (HopfAlgebra.antipode k) = LinearMap.id :=
    hcancel _ _ (HopfAlgebra.mul_antipode_lTensor_comul (R := k) (A := H))
  refine ⟨{ F LinearMap.id with
    invFun := F (HopfAlgebra.antipode k)
    left_inv := fun z => LinearMap.congr_fun hleft z
    right_inv := fun z => LinearMap.congr_fun hright z }, ?_⟩
  intro m h
  change F LinearMap.id (m ⊗ₜ[k] h) = _
  rw [hF, LinearMap.comp_id]
  have hmul : LinearMap.mulRight k h = LinearMap.mulLeft k h := by
    ext b
    exact mul_comm b h
  rw [hmul]

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
theorem Submission.p05_ums_section_of_inner_inverse_a5b449214a
    {R : Type*} [CommRing R]
    {F : Type*} [AddCommGroup F] [Module R F]
    {G : Type*} [AddCommGroup G] [Module R G]
    {M : Type*} [AddCommGroup M] [Module R M]
    (f : G →ₗ[R] F) (g : F →ₗ[R] G) (π : F →ₗ[R] M)
    (_hinner : (f.comp g).comp f = f) (_hπ : Function.Surjective π)
    (_hker : LinearMap.ker π = LinearMap.range f) :
    ∃ s : M →ₗ[R] F, π.comp s = LinearMap.id := by
  classical
  let r : F →ₗ[R] F := LinearMap.id - f.comp g
  have hπf (y : G) : π (f y) = 0 := by
    apply LinearMap.mem_ker.mp
    rw [_hker]
    exact LinearMap.mem_range_self f y
  have hfiber (x y : F) (h : π x = π y) : r x = r y := by
    apply sub_eq_zero.mp
    rw [← map_sub]
    have hmem : x - y ∈ LinearMap.ker π := by
      rw [LinearMap.mem_ker, map_sub, h, sub_self]
    rw [_hker] at hmem
    obtain ⟨z, hz⟩ := hmem
    rw [← hz]
    change f z - f (g (f z)) = 0
    rw [show f (g (f z)) = f z from LinearMap.congr_fun _hinner z, sub_self]
  choose t ht using _hπ
  let s : M →ₗ[R] F :=
    { toFun := fun m => r (t m)
      map_add' := by
        intro m n
        rw [← map_add]
        apply hfiber
        rw [ht, map_add, ht, ht]
      map_smul' := by
        intro a m
        change r (t (a • m)) = a • r (t m)
        rw [← map_smul]
        apply hfiber
        rw [ht, map_smul, ht] }
  refine ⟨s, ?_⟩
  ext m
  change π (t m - f (g (t m))) = m
  rw [map_sub, hπf, sub_zero, ht]
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
theorem Submission.p05_canonical_map_injective_a5b449214a
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
    ∃ β : (TensorProduct K H H) →ₐ[k] (TensorProduct k H B),
      Function.Injective β ∧ ∀ a b : H, β (TensorProduct.tmul K a b) =
        (TensorProduct.tmul k a (1 : B)) * HopfAlgebra.coaction q b := by
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
  have hcoinv (t : H) (ht : t ∈ K) :
      HopfAlgebra.coaction q t = TensorProduct.tmul k t (1 : B) := by
    rw [HopfAlgebra.coaction_apply, hspan _ (hΔ t ht)]
    simp only [Coalgebra.lTensor_counit_comul, LinearMap.lTensor_tmul,
      Algebra.linearMap_apply, map_one]
  obtain ⟨β, hβ⟩ := Submission.p05_canonical_balanced_lift_a5b449214a K q hcoinv
  obtain ⟨σ, hσ⟩ := Submission.p05_translation_descends_a5b449214a K hΔ hS q hq hker
  obtain ⟨γ, _, hγβ⟩ := Submission.p05_translation_left_inverse_a5b449214a K q β hβ σ hσ
  exact ⟨β, hγβ.injective, hβ⟩
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
theorem Submission.p05_ct_algebra_a5b449214a
    {k : Type*} [Field k] {A : Type*} [CommRing A] [HopfAlgebra k A]
    {H : Type*} [CommRing H] [HopfAlgebra k H] (ι : BialgHom k A H) :
    ∃ θ : TensorProduct k A H ≃ₐ[k] TensorProduct k A H,
      ∀ (a : A) (h : H), θ (TensorProduct.tmul k a h) =
        (TensorProduct.map (LinearMap.id : A →ₗ[k] A) ι.toLinearMap)
          (Coalgebra.comul (R := k) a) * TensorProduct.tmul k (1 : A) h := by
  classical
  let T (f : A →ₗ[k] H) : A ⊗[k] H →ₗ[k] A ⊗[k] H :=
    TensorProduct.lift ((LinearMap.mul k (A ⊗[k] H)).compl₁₂
      (TensorProduct.map LinearMap.id f ∘ₗ Coalgebra.comul)
      (Algebra.TensorProduct.includeRight : H →ₐ[k] A ⊗[k] H).toLinearMap)
  have hT (f : A →ₗ[k] H) (a : A) (h : H) :
      T f (a ⊗ₜ[k] h) = TensorProduct.map LinearMap.id f (Coalgebra.comul a) *
        (1 ⊗ₜ[k] h) := rfl
  let r := Coalgebra.Repr.arbitrary k (A := A)
  have hexp (f : A →ₗ[k] H) (a : A) (h : H) :
      T f (a ⊗ₜ[k] h) = ∑ i ∈ (r a).index,
        (r a).left i ⊗ₜ[k] (f ((r a).right i) * h) := by
    rw [hT, ← (r a).eq]
    simp [map_sum, Finset.sum_mul, Algebra.TensorProduct.tmul_mul_tmul]
  have hinv (f g : A →ₗ[k] H)
      (hfg : TensorProduct.lift ((LinearMap.mul k H).compl₁₂ f g) ∘ₗ
        Coalgebra.comul = Algebra.linearMap k H ∘ₗ Coalgebra.counit) :
      T f ∘ₗ T g = LinearMap.id := by
    ext a h
    have hc := congrArg
      (TensorProduct.map (LinearMap.id : A →ₗ[k] A)
        (TensorProduct.lift ((LinearMap.mul k H).compl₁₂ f g)))
      (Coalgebra.sum_tmul_tmul_eq (r a) (fun i => r ((r a).left i))
        (fun i => r ((r a).right i)))
    simp only [map_sum, TensorProduct.map_tmul, LinearMap.id_apply,
      TensorProduct.lift.tmul, LinearMap.compl₁₂_apply, LinearMap.mul_apply'] at hc
    have hc' := congrArg ((LinearMap.mulRight k h).lTensor A) hc
    simp only [map_sum, LinearMap.lTensor_tmul, LinearMap.mulRight_apply] at hc'
    have he (b : A) : ∑ j ∈ (r b).index,
        f ((r b).left j) * g ((r b).right j) =
          algebraMap k H (Coalgebra.counit b) := by
      have he := LinearMap.congr_fun hfg b
      simpa only [LinearMap.comp_apply, ← (r b).eq, map_sum,
        TensorProduct.lift.tmul, LinearMap.compl₁₂_apply, LinearMap.mul_apply',
        Algebra.linearMap_apply] using he
    change T f (T g (a ⊗ₜ[k] h)) = a ⊗ₜ[k] h
    rw [hexp]
    simp only [map_sum, hexp, ← mul_assoc]
    rw [hc']
    simp only [← TensorProduct.tmul_sum, ← Finset.sum_mul, he,
      ← Algebra.smul_def, TensorProduct.tmul_smul]
    have heps := congrArg (TensorProduct.rid k A)
      (Coalgebra.sum_tmul_counit_eq (r a))
    simp only [map_sum, TensorProduct.rid_tmul, one_smul] at heps
    simp only [TensorProduct.smul_tmul', ← TensorProduct.sum_tmul, heps]
  let f : A →ₗ[k] H := ι.toLinearMap
  let g : A →ₗ[k] H := ι.toLinearMap ∘ₗ HopfAlgebra.antipode k
  have hfg : TensorProduct.lift ((LinearMap.mul k H).compl₁₂ f g) =
      ι.toLinearMap ∘ₗ LinearMap.mul' k A ∘ₗ (HopfAlgebra.antipode k).lTensor A := by
    ext a b
    exact (map_mul ι a (HopfAlgebra.antipode k b)).symm
  have hgf : TensorProduct.lift ((LinearMap.mul k H).compl₁₂ g f) =
      ι.toLinearMap ∘ₗ LinearMap.mul' k A ∘ₗ (HopfAlgebra.antipode k).rTensor A := by
    ext a b
    exact (map_mul ι (HopfAlgebra.antipode k a) b).symm
  have hright : T f ∘ₗ T g = LinearMap.id := by
    apply hinv
    rw [hfg, LinearMap.comp_assoc, LinearMap.comp_assoc,
      HopfAlgebra.mul_antipode_lTensor_comul]
    ext a
    exact ι.toAlgHom.commutes (Coalgebra.counit a)
  have hleft : T g ∘ₗ T f = LinearMap.id := by
    apply hinv
    rw [hgf, LinearMap.comp_assoc, LinearMap.comp_assoc,
      HopfAlgebra.mul_antipode_rTensor_comul]
    ext a
    exact ι.toAlgHom.commutes (Coalgebra.counit a)
  let F : A ⊗[k] H →ₐ[k] A ⊗[k] H :=
    Algebra.TensorProduct.lift (HopfAlgebra.coaction ι)
      Algebra.TensorProduct.includeRight (fun _ _ => Commute.all _ _)
  have hF : F.toLinearMap = T f := by
    ext a h
    rfl
  have hbij : Function.Bijective F := by
    constructor
    · intro x y hxy
      have hx := LinearMap.congr_fun hleft x
      have hy := LinearMap.congr_fun hleft y
      change T g (T f x) = x at hx
      change T g (T f y) = y at hy
      rw [← hx, ← hy]
      apply congrArg (T g)
      simpa only [← hF, AlgHom.toLinearMap_apply] using hxy
    · intro x
      refine ⟨T g x, ?_⟩
      change F.toLinearMap (T g x) = x
      rw [hF]
      exact LinearMap.congr_fun hright x
  refine ⟨AlgEquiv.ofBijective F hbij, ?_⟩
  intro a h
  rfl

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

theorem p05_hte_finite_tensor_zero_witness_a5b449214a
    {k : Type*} [CommRing k] {D : Type*} [CommRing D] [Algebra k D]
    {M : Type*} [AddCommGroup M] [Module D M]
    {P : Type*} [AddCommGroup P] [Module D P] (m : M) (p : P)
    (hmp : (TensorProduct.tmul D m p : TensorProduct D M P) = 0) :
    ∃ S : Finset D, ∃ F : Finset M, m ∈ F ∧
      ∀ (A : Subalgebra k D), (∀ d ∈ S, d ∈ A) →
      ∀ (N : Submodule A M), (∀ y ∈ F, y ∈ N) →
      ∀ hm : m ∈ N,
        (TensorProduct.tmul A (⟨m, hm⟩ : N) p : TensorProduct A N P) = 0 := by
  classical
  let b : M → P → FreeAbelianGroup (M × P) := fun u z => FreeAbelianGroup.of (u, z)
  let R : Set (FreeAbelianGroup (M × P)) :=
    {r | (∃ z : P, r = b 0 z) ∨
      (∃ u : M, r = b u 0) ∨
      (∃ (u v : M) (z : P), r = b (u + v) z - b u z - b v z) ∨
      (∃ (u : M) (z w : P), r = b u (z + w) - b u z - b u w) ∨
      (∃ (d : D) (u : M) (z : P), r = b (d • u) z - b u (d • z))}
  let supported (A : Subalgebra k D) (N : Submodule A M) :
      Set (FreeAbelianGroup (M × P)) :=
    {r | (∃ z : P, r = b 0 z) ∨
      (∃ u : M, u ∈ N ∧ r = b u 0) ∨
      (∃ (u v : M) (z : P), u ∈ N ∧ v ∈ N ∧
        r = b (u + v) z - b u z - b v z) ∨
      (∃ (u : M) (z w : P), u ∈ N ∧
        r = b u (z + w) - b u z - b u w) ∨
      (∃ (d : D) (u : M) (z : P), d ∈ A ∧ u ∈ N ∧
        r = b (d • u) z - b u (d • z))}
  have hrel : b m p ∈ AddSubgroup.closure R := by
    rw [← p05_ftzw_tensor_relation_kernel_a5b449214a (D := D) (M := M) (P := P)]
    change FreeAbelianGroup.lift (fun x : M × P => TensorProduct.tmul D x.1 x.2)
      (FreeAbelianGroup.of (m, p)) = 0
    simpa only [FreeAbelianGroup.lift_apply_of] using hmp
  -- Closure induction collects finite supports for the formal relation identity.
  have finite_support : ∀ r ∈ AddSubgroup.closure R,
      ∃ S : Finset D, ∃ F : Finset M,
        ∀ (A : Subalgebra k D), (∀ d ∈ S, d ∈ A) →
        ∀ (N : Submodule A M), (∀ y ∈ F, y ∈ N) →
          r ∈ AddSubgroup.closure (supported A N) := by
    intro r hr
    induction hr using AddSubgroup.closure_induction with
    | mem r hr =>
      rcases hr with ⟨z, rfl⟩ | ⟨u, rfl⟩ | ⟨u, v, z, rfl⟩ |
        ⟨u, z, w, rfl⟩ | ⟨d, u, z, rfl⟩
      · refine ⟨∅, {0}, ?_⟩
        intro A _ N _
        exact AddSubgroup.subset_closure (Or.inl ⟨z, rfl⟩)
      · refine ⟨∅, {u}, ?_⟩
        intro A _ N hN
        exact AddSubgroup.subset_closure (Or.inr (Or.inl ⟨u, hN u (by simp), rfl⟩))
      · refine ⟨∅, {u, v, u + v}, ?_⟩
        intro A _ N hN
        exact AddSubgroup.subset_closure
          (Or.inr (Or.inr (Or.inl ⟨u, v, z, hN u (by simp), hN v (by simp), rfl⟩)))
      · refine ⟨∅, {u}, ?_⟩
        intro A _ N hN
        exact AddSubgroup.subset_closure
          (Or.inr (Or.inr (Or.inr (Or.inl ⟨u, z, w, hN u (by simp), rfl⟩))))
      · refine ⟨{d}, {u, d • u}, ?_⟩
        intro A hA N hN
        exact AddSubgroup.subset_closure
          (Or.inr (Or.inr (Or.inr (Or.inr
            ⟨d, u, z, hA d (by simp), hN u (by simp), rfl⟩))))
    | zero =>
      exact ⟨∅, ∅, fun A _ N _ => (AddSubgroup.closure (supported A N)).zero_mem⟩
    | add r s _ _ ihr ihs =>
      obtain ⟨Sr, Fr, hr⟩ := ihr
      obtain ⟨Ss, Fs, hs⟩ := ihs
      refine ⟨Sr ∪ Ss, Fr ∪ Fs, ?_⟩
      intro A hA N hN
      exact (AddSubgroup.closure (supported A N)).add_mem
        (hr A (fun d hd => hA d (Finset.mem_union_left Ss hd))
          N (fun y hy => hN y (Finset.mem_union_left Fs hy)))
        (hs A (fun d hd => hA d (Finset.mem_union_right Sr hd))
          N (fun y hy => hN y (Finset.mem_union_right Fr hy)))
    | neg r _ ihr =>
      obtain ⟨S, F, h⟩ := ihr
      exact ⟨S, F, fun A hA N hN =>
        (AddSubgroup.closure (supported A N)).neg_mem (h A hA N hN)⟩
  obtain ⟨S, F, hSF⟩ := finite_support (b m p) hrel
  refine ⟨S, insert m F, Finset.mem_insert_self m F, ?_⟩
  intro A hA N hN hm
  apply p05_ftzw_supported_relations_vanish_a5b449214a A N ⟨m, hm⟩ p
  exact hSF A hA N (fun y hy => hN y (Finset.mem_insert_of_mem hy))
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


namespace Submission

/-- The two coaction twists intertwine the prescribed tensor action. -/
theorem p05_fr_rhm_coaction_twist_a5b449214a :
    ∀ {k : Type*} [Field k]
      {A : Type*} [CommRing A] [HopfAlgebra k A]
      {H : Type*} [CommRing H] [HopfAlgebra k H]
      (ι : BialgHom k A H)
      {M : Type*} [AddCommGroup M] [Module k M] [Module A M]
      [IsScalarTower k A M]
      [Module (TensorProduct k A H) (TensorProduct k M H)]
      (_hact : ∀ (a : A) (h : H) (m : M) (g : H), (TensorProduct.tmul k a h) • (TensorProduct.tmul k m g) = TensorProduct.tmul k (a • m) (h * g))
      (μ : M →ₗ[k] TensorProduct k M H)
      (_hcoassoc : ∀ m : M, TensorProduct.assoc k M H H ((TensorProduct.map μ (LinearMap.id : H →ₗ[k] H)) (μ m)) = (TensorProduct.map (LinearMap.id : M →ₗ[k] M) (Coalgebra.comul (R := k))) (μ m))
      (_hcounit : ∀ m : M, TensorProduct.rid k M ((TensorProduct.map (LinearMap.id : M →ₗ[k] M) (Coalgebra.counit (R := k))) (μ m)) = m)
      (_hcompat : ∀ (a : A) (m : M), let d := Coalgebra.Repr.arbitrary k a; μ (a • m) = ∑ i ∈ d.index, TensorProduct.map ((Algebra.lsmul k k M) (d.left i)) (LinearMap.mulLeft k (ι (d.right i))) (μ m)),
      ∃ (θ : TensorProduct k A H ≃ₐ[k] TensorProduct k A H)
        (T : TensorProduct k M H ≃ₗ[k] TensorProduct k M H),
        (∀ (a : A) (h : H), θ (TensorProduct.tmul k a h) = (TensorProduct.map (LinearMap.id : A →ₗ[k] A) ι.toLinearMap) (Coalgebra.comul (R := k) a) * TensorProduct.tmul k (1 : A) h) ∧
        (∀ (m : M) (h : H), T (TensorProduct.tmul k m h) = TensorProduct.map (LinearMap.id : M →ₗ[k] M) (LinearMap.mulLeft k h) (μ m)) ∧
        (∀ (s : TensorProduct k A H) (x : TensorProduct k M H), T (s • x) = θ s • T x) := by
  classical
  intro k _ A _ _ H _ _ ι M _ _ _ _ _ hact μ hcoassoc hcounit hcompat
  obtain ⟨θ, hθ⟩ := Submission.p05_ct_algebra_a5b449214a ι
  obtain ⟨T, hT⟩ := Submission.p05_ct_comodule_a5b449214a μ hcoassoc hcounit
  refine ⟨θ, T, hθ, hT, ?_⟩
  intro s x
  induction s using TensorProduct.induction_on with
  | zero => simp
  | tmul a h =>
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul m g =>
      rw [hact, hT, hθ, hT, hcompat]
      -- Expand the algebra twist using the representation fixed by compatibility.
      let d := Coalgebra.Repr.arbitrary k a
      rw [← d.eq]
      simp only [map_sum, Finset.sum_mul, Finset.sum_smul]
      apply Finset.sum_congr rfl
      intro i hi
      -- The summand identity is additive in the coaction tensor.
      generalize μ m = z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul n t =>
        simp [d, hact, Algebra.TensorProduct.tmul_mul_tmul, BialgHom.toCoalgHom_apply,
          mul_assoc,
          mul_left_comm, mul_comm]
      | add z₁ z₂ hz₁ hz₂ =>
        simp only [map_add, smul_add, hz₁, hz₂]
    | add x₁ x₂ hx₁ hx₂ =>
      simp only [smul_add, map_add, hx₁, hx₂]
  | add s₁ s₂ hs₁ hs₂ =>
    simp only [add_smul, map_add, hs₁, hs₂]

end Submission
theorem Submission.p05_pie_successive_minor_containment_a5b449214a
    {R : Type*} [CommRing R] {ι κ : Type*} [Fintype ι] [Fintype κ]
    (P : Matrix ι κ R) (d : ℕ) :
    (Ideal.span {x : R | ∃ (rows : Fin (d + 1) ↪ ι) (cols : Fin (d + 1) ↪ κ),
      x = Matrix.det (P.submatrix rows cols)}) ≤
    Ideal.span {x : R | ∃ (rows : Fin d ↪ ι) (cols : Fin d ↪ κ),
      x = Matrix.det (P.submatrix rows cols)} := by
  classical
  apply Ideal.span_le.mpr
  rintro x ⟨rows, cols, rfl⟩
  rw [Matrix.det_succ_row_zero]
  apply Ideal.sum_mem
  intro j _
  apply Ideal.mul_mem_left
  exact Ideal.subset_span
    ⟨(Fin.succEmb d).trans rows, j.succAboveEmb.trans cols, rfl⟩
theorem Submission.p05_pie_redundant_generator_relations_a5b449214a
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    (n p t : ℕ) (P : Matrix (Fin n) (Fin p) R) (A : Matrix (Fin n) (Fin t) R)
    (π : (Fin n → R) →ₗ[R] M) (ψ : (Fin t → R) →ₗ[R] M)
    (_hker : LinearMap.ker π = LinearMap.range P.mulVecLin)
    (_hA : ∀ y : Fin t → R, π (A.mulVecLin y) = ψ y) :
    let T : Matrix (Fin n ⊕ Fin t) (Fin p ⊕ Fin t) R :=
      Matrix.fromBlocks P (-A) 0 (1 : Matrix (Fin t) (Fin t) R)
    ∀ z : (Fin n ⊕ Fin t) → R,
      (π (fun i => z (Sum.inl i)) + ψ (fun j => z (Sum.inr j)) = 0) ↔
        ∃ w : (Fin p ⊕ Fin t) → R, T.mulVecLin w = z := by
  intro T z
  have hT (w : (Fin p ⊕ Fin t) → R) :
      T.mulVecLin w = Sum.elim
        (P.mulVecLin (fun i => w (Sum.inl i)) - A.mulVecLin (fun j => w (Sum.inr j)))
        (fun j => w (Sum.inr j)) := by
    simp only [T, Matrix.mulVecLin_apply, Matrix.fromBlocks_mulVec,
      Matrix.neg_mulVec, Matrix.zero_mulVec, Matrix.one_mulVec, zero_add,
      sub_eq_add_neg, Function.comp_def]
  constructor
  · intro hz
    have hx : (fun i => z (Sum.inl i)) + A.mulVecLin (fun j => z (Sum.inr j)) ∈
        LinearMap.range P.mulVecLin := by
      rw [← _hker, LinearMap.mem_ker, map_add, _hA]
      exact hz
    obtain ⟨u, hu⟩ := hx
    refine ⟨Sum.elim u (fun j => z (Sum.inr j)), ?_⟩
    rw [hT]
    simp only [Sum.elim_inl, Sum.elim_inr, hu, add_sub_cancel_right]
    funext i
    cases i <;> rfl
  · rintro ⟨w, rfl⟩
    have hP : π (P.mulVecLin (fun i => w (Sum.inl i))) = 0 := by
      apply LinearMap.mem_ker.mp
      rw [_hker]
      exact ⟨fun i => w (Sum.inl i), rfl⟩
    rw [hT]
    simp only [Sum.elim_inl, Sum.elim_inr, map_sub, hP, _hA, zero_sub, neg_add_cancel]
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
theorem Submission.p05_hte_sshs_br_coalgebra_laws_a5b449214a
    {k : Type*} [Field k] {C : Type*} [AddCommGroup C] [Module k C] [Coalgebra k C]
    {V : Type*} [AddCommGroup V] [Module k V]
    (i : V →ₗ[k] C) (_hi : Function.Injective i)
    (δ : V →ₗ[k] TensorProduct k V V) (ε : V →ₗ[k] k)
    (_hδ : ∀ v : V, TensorProduct.map i i (δ v) = Coalgebra.comul (R := k) (i v))
    (_hε : ∀ v : V, ε v = Coalgebra.counit (R := k) (i v)) :
    (∀ v : V, TensorProduct.assoc k V V V
      (TensorProduct.map δ (LinearMap.id : V →ₗ[k] V) (δ v)) =
      TensorProduct.map (LinearMap.id : V →ₗ[k] V) δ (δ v)) ∧
    (∀ v : V, TensorProduct.map ε (LinearMap.id : V →ₗ[k] V) (δ v) =
      TensorProduct.tmul k (1 : k) v) ∧
    (∀ v : V, TensorProduct.map (LinearMap.id : V →ₗ[k] V) ε (δ v) =
      TensorProduct.tmul k v (1 : k)) := by
  obtain ⟨r, hr⟩ := i.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr _hi)
  have hJ : Function.Injective (TensorProduct.map i (TensorProduct.map i i)) := by
    apply Function.LeftInverse.injective
      (g := TensorProduct.map r (TensorProduct.map r r))
    intro t
    simp only [TensorProduct.map_map, ← TensorProduct.map_comp, hr,
      TensorProduct.map_id, LinearMap.id_apply]
  have hL : Function.Injective (TensorProduct.map (LinearMap.id : k →ₗ[k] k) i) := by
    apply Function.LeftInverse.injective
      (g := TensorProduct.map (LinearMap.id : k →ₗ[k] k) r)
    intro t
    simp only [TensorProduct.map_map, hr, LinearMap.id_comp,
      TensorProduct.map_id, LinearMap.id_apply]
  have hR : Function.Injective (TensorProduct.map i (LinearMap.id : k →ₗ[k] k)) := by
    apply Function.LeftInverse.injective
      (g := TensorProduct.map r (LinearMap.id : k →ₗ[k] k))
    intro t
    simp only [TensorProduct.map_map, hr, LinearMap.id_comp,
      TensorProduct.map_id, LinearMap.id_apply]
  have hδcomp : (TensorProduct.map i i).comp δ =
      (Coalgebra.comul (R := k)).comp i := LinearMap.ext _hδ
  have hεcomp : ε = (Coalgebra.counit (R := k)).comp i := LinearMap.ext _hε
  refine ⟨?_, ?_, ?_⟩
  · intro v
    apply hJ
    calc
      TensorProduct.map i (TensorProduct.map i i)
          (TensorProduct.assoc k V V V
            (TensorProduct.map δ (LinearMap.id : V →ₗ[k] V) (δ v))) =
          TensorProduct.assoc k C C C
            (TensorProduct.map (Coalgebra.comul (R := k)) (LinearMap.id : C →ₗ[k] C)
              (TensorProduct.map i i (δ v))) := by
        rw [TensorProduct.map_map_assoc]
        simp only [TensorProduct.map_map, hδcomp, LinearMap.comp_id, LinearMap.id_comp]
      _ = TensorProduct.map (LinearMap.id : C →ₗ[k] C) (Coalgebra.comul (R := k))
          (TensorProduct.map i i (δ v)) := by
        rw [_hδ]
        exact Coalgebra.coassoc_apply (R := k) (i v)
      _ = TensorProduct.map i (TensorProduct.map i i)
          (TensorProduct.map (LinearMap.id : V →ₗ[k] V) δ (δ v)) := by
        simp only [TensorProduct.map_map, hδcomp, LinearMap.comp_id, LinearMap.id_comp]
  · intro v
    apply hL
    calc
      TensorProduct.map (LinearMap.id : k →ₗ[k] k) i
          (TensorProduct.map ε (LinearMap.id : V →ₗ[k] V) (δ v)) =
          TensorProduct.map (Coalgebra.counit (R := k)) (LinearMap.id : C →ₗ[k] C)
            (TensorProduct.map i i (δ v)) := by
        simp only [TensorProduct.map_map, hεcomp, LinearMap.comp_id, LinearMap.id_comp]
      _ = TensorProduct.map (LinearMap.id : k →ₗ[k] k) i
          (TensorProduct.tmul k (1 : k) v) := by
        rw [_hδ]
        simpa only [LinearMap.rTensor, TensorProduct.map_tmul, LinearMap.id_apply] using
        simpa only [TensorProduct.map_tmul, LinearMap.id_apply] using
          Coalgebra.rTensor_counit_comul (R := k) (i v)
  · intro v
    apply hR
    calc
      TensorProduct.map i (LinearMap.id : k →ₗ[k] k)
          (TensorProduct.map (LinearMap.id : V →ₗ[k] V) ε (δ v)) =
          TensorProduct.map (LinearMap.id : C →ₗ[k] C) (Coalgebra.counit (R := k))
            (TensorProduct.map i i (δ v)) := by
        simp only [TensorProduct.map_map, hεcomp, LinearMap.comp_id, LinearMap.id_comp]
      _ = TensorProduct.map i (LinearMap.id : k →ₗ[k] k)
          (TensorProduct.tmul k v (1 : k)) := by
        rw [_hδ]
        simpa only [LinearMap.lTensor, TensorProduct.map_tmul, LinearMap.id_apply] using
          Coalgebra.lTensor_counit_comul (R := k) (i v)
theorem Submission.p05_pie_minor_product_containment_a5b449214a
    {R : Type*} [CommRing R] {ι κ ν : Type*}
    [Fintype ι] [Fintype κ] [Fintype ν]
    (A : Matrix ι κ R) (B : Matrix κ ν R) (d : ℕ) :
    (Ideal.span {x : R | ∃ (rows : Fin d ↪ ι) (cols : Fin d ↪ ν),
      x = Matrix.det ((A * B).submatrix rows cols)}) ≤
    (Ideal.span {x : R | ∃ (rows : Fin d ↪ ι) (cols : Fin d ↪ κ),
      x = Matrix.det (A.submatrix rows cols)}) ⊓
    (Ideal.span {x : R | ∃ (rows : Fin d ↪ κ) (cols : Fin d ↪ ν),
      x = Matrix.det (B.submatrix rows cols)}) := by
  classical
  have hrows (C : Matrix (Fin d) κ R) (D : Matrix κ (Fin d) R)
      (J : Ideal R)
      (hgen : ∀ r : Fin d ↪ κ, Matrix.det (D.submatrix r id) ∈ J) :
      Matrix.det (C * D) ∈ J := by
    have hexp : Matrix.det (C * D) =
        ∑ f : Fin d → κ, (∏ i, C i (f i)) * Matrix.det (D.submatrix f id) := by
      have hmat : C * D = fun i => ∑ k, C i k • D k := by
        ext i j
        simp [Matrix.mul_apply]
      have hsum : Matrix.det (fun i => ∑ k, C i k • D k) =
          ∑ f : Fin d → κ, Matrix.det (fun i => C i (f i) • D (f i)) :=
        (Matrix.detRowAlternating : (Fin d → R) [⋀^Fin d]→ₗ[R] R).toMultilinearMap.map_sum
          (fun i k => C i k • D k)
      rw [hmat, hsum]
      apply Finset.sum_congr rfl
      intro f _
      exact Matrix.det_mul_column (fun i => C i (f i)) (D.submatrix f id)
    rw [hexp]
    apply J.sum_mem
    intro f _
    by_cases hf : Function.Injective f
    · exact J.mul_mem_left _ (hgen ⟨f, hf⟩)
    · have hz : Matrix.det (D.submatrix f id) = 0 := by
        rw [Function.Injective] at hf
        push Not at hf
        obtain ⟨i, j, hij, hne⟩ := hf
        apply Matrix.det_zero_of_row_eq hne
        funext k
        change D (f i) k = D (f j) k
        rw [hij]
      rw [hz, mul_zero]
      exact J.zero_mem
  apply Ideal.span_le.mpr
  rintro x ⟨rows, cols, rfl⟩
  constructor
  · have h := hrows (B.transpose.submatrix cols id) (A.transpose.submatrix id rows)
      (Ideal.span {x : R | ∃ (r : Fin d ↪ ι) (c : Fin d ↪ κ),
        x = Matrix.det (A.submatrix r c)}) (fun r => by
          apply Ideal.subset_span
          refine ⟨rows, r, ?_⟩
          exact Matrix.det_transpose (A.submatrix rows r))
    have hmat : B.transpose.submatrix cols id * A.transpose.submatrix id rows =
        ((A * B).submatrix rows cols).transpose := by
      ext i j
      simp only [Matrix.mul_apply, Matrix.submatrix_apply, Matrix.transpose_apply, id_eq]
      apply Finset.sum_congr rfl
      intro k _
      exact mul_comm _ _
    rw [hmat, Matrix.det_transpose] at h
    exact h
  · exact hrows (A.submatrix rows id) (B.submatrix id cols) _
      (fun r => Ideal.subset_span ⟨r, cols, rfl⟩)


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

theorem Submission.p05_umgi_inner_inverse_of_reconstruction_a5b449214a :
    ∀ {R : Type*} [CommRing R] (n p d : ℕ) (P : Matrix (Fin n) (Fin p) R)
      (rows : Fin d ↪ Fin n) (cols : Fin d ↪ Fin p)
      (T : Matrix (Fin d) (Fin d) R)
      (_hfactor : P = (P.submatrix id cols) * T * (P.submatrix rows id)),
      ∃ Q : Matrix (Fin p) (Fin n) R, P * Q * P = P := by
  intro R _ n p d P rows cols T hfactor
  let U : Matrix (Fin p) (Fin d) R := (1 : Matrix (Fin p) (Fin p) R).submatrix id cols
  let V : Matrix (Fin d) (Fin n) R := (1 : Matrix (Fin n) (Fin n) R).submatrix rows id
  have hU : P * U = P.submatrix id cols :=
    Matrix.mul_submatrix_one (Equiv.refl (Fin p)) cols P
  have hV : V * P = P.submatrix rows id :=
    Matrix.one_submatrix_mul rows (Equiv.refl (Fin n)) P
  refine ⟨U * T * V, ?_⟩
  calc
    P * (U * T * V) * P = (P * U) * T * (V * P) := by
      simp only [Matrix.mul_assoc]
    _ = (P.submatrix id cols) * T * (P.submatrix rows id) := by rw [hU, hV]
    _ = P := hfactor.symm


theorem Submission.p05_hte_sshs_bialgebra_restriction_a5b449214a
    {k : Type*} [Field k] {H : Type*} [CommRing H] [Bialgebra k H]
    (D : Subalgebra k H)
    (hΔ : ∀ x ∈ D, Coalgebra.comul (R := k) x ∈
      Submodule.span k {t : TensorProduct k H H |
        ∃ a ∈ D, ∃ b ∈ D, t = TensorProduct.tmul k a b}) :
    ∃ bD : Bialgebra k D, bD.toAlgebra = (inferInstance : Algebra k D) ∧
      (letI : Algebra k D := bD.toAlgebra
       letI : Module k D := Algebra.toModule
       letI : Bialgebra k D := bD
       ∃ ι : BialgHom k D H, ∀ d : D, ι d = (d : H)) := by
  obtain ⟨δ, hδ⟩ := Submission.p05_hte_sshs_br_comul_alg_lift_a5b449214a D hΔ
  let ε : D →ₐ[k] k := (Bialgebra.counitAlgHom k H).comp D.val
  obtain ⟨hcoassoc, hleft, hright⟩ :=
    Submission.p05_hte_sshs_br_coalgebra_laws_a5b449214a
      D.val.toLinearMap Subtype.val_injective δ.toLinearMap ε.toLinearMap
      (fun d => hδ d) (fun _ => rfl)
  let : Coalgebra k D :=
    { comul := δ.toLinearMap
      counit := ε.toLinearMap
      coassoc := LinearMap.ext hcoassoc
      rTensor_counit_comp_comul := LinearMap.ext hleft
      lTensor_counit_comp_comul := LinearMap.ext hright }
  let bD : Bialgebra k D :=
    Bialgebra.mk' k D (map_one ε) (map_mul ε _ _) (map_one δ) (map_mul δ _ _)
  refine ⟨bD, rfl, ?_⟩
  let : Bialgebra k D := bD
  refine ⟨BialgHom.ofAlgHom D.val ?_ ?_, fun _ => rfl⟩
  · ext d
    rfl
  · ext d
    exact hδ d


theorem Submission.p05_ibs_extend_minor_a5b449214a
    {R : Type*} [CommRing R] (n p t s : ℕ) (P : Matrix (Fin n) (Fin p) R)
    (rows : Fin s ↪ Fin n) (cols : Fin s ↪ Fin p) :
    ∃ (rows' : Fin (s + t) ↪ (Fin n ⊕ Fin t))
      (cols' : Fin (s + t) ↪ (Fin p ⊕ Fin t)),
      Matrix.det ((Matrix.fromBlocks P 0 0 (1 : Matrix (Fin t) (Fin t) R)).submatrix
        rows' cols') = Matrix.det (P.submatrix rows cols) := by
  classical
  let e : Fin (s + t) ≃ (Fin s ⊕ Fin t) := finSumFinEquiv.symm
  let r : (Fin s ⊕ Fin t) ↪ (Fin n ⊕ Fin t) :=
    rows.sumMap (Function.Embedding.refl (Fin t))
  let c : (Fin s ⊕ Fin t) ↪ (Fin p ⊕ Fin t) :=
    cols.sumMap (Function.Embedding.refl (Fin t))
  refine ⟨e.toEmbedding.trans r, e.toEmbedding.trans c, ?_⟩
  have h : (Matrix.fromBlocks P 0 0 (1 : Matrix (Fin t) (Fin t) R)).submatrix r c =
      Matrix.fromBlocks (P.submatrix rows cols) 0 0 (1 : Matrix (Fin t) (Fin t) R) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> rfl
  change Matrix.det (((Matrix.fromBlocks P 0 0 (1 : Matrix (Fin t) (Fin t) R)).submatrix
    r c).submatrix e e) = _
  rw [Matrix.det_submatrix_equiv_self, h, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_one, mul_one]
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

theorem Submission.p05_umgi_minor_reconstruction_a5b449214a
    {R : Type*} [CommRing R] (n p d : ℕ) (P : Matrix (Fin n) (Fin p) R)
    (rows : Fin d ↪ Fin n) (cols : Fin d ↪ Fin p)
    (_hunit : IsUnit (Matrix.det (P.submatrix rows cols)))
    (_hnext : ∀ (rows' : Fin (d + 1) ↪ Fin n) (cols' : Fin (d + 1) ↪ Fin p),
      Matrix.det (P.submatrix rows' cols') = 0) :
    P = (P.submatrix id cols) * (P.submatrix rows cols)⁻¹ * (P.submatrix rows id) := by
  classical
  let B := P.submatrix rows cols
  let L := P.submatrix id cols
  let H := P.submatrix rows id
  ext i j
  by_cases hi : i ∈ Set.range rows
  · obtain ⟨a, rfl⟩ := hi
    change P (rows a) j = (B * B⁻¹ * H) a j
    rw [Matrix.mul_nonsing_inv B _hunit, Matrix.one_mul]
    rfl
  by_cases hj : j ∈ Set.range cols
  · obtain ⟨b, rfl⟩ := hj
    change P i (cols b) = (L * B⁻¹ * B) i b
    rw [Matrix.nonsing_inv_mul_cancel_right B L _hunit]
    rfl
  let er : Fin d ⊕ Fin 1 ↪ Fin n :=
    { toFun := Sum.elim rows (fun _ => i)
      inj' := by
        intro a b hab
        rcases a with a | a <;> rcases b with b | b
        · exact congrArg Sum.inl (rows.injective hab)
        · exact (hi ⟨a, hab⟩).elim
        · exact (hi ⟨b, hab.symm⟩).elim
        · exact congrArg Sum.inr (Subsingleton.elim _ _) }
  let ec : Fin d ⊕ Fin 1 ↪ Fin p :=
    { toFun := Sum.elim cols (fun _ => j)
      inj' := by
        intro a b hab
        rcases a with a | a <;> rcases b with b | b
        · exact congrArg Sum.inl (cols.injective hab)
        · exact (hj ⟨a, hab⟩).elim
        · exact (hj ⟨b, hab.symm⟩).elim
        · exact congrArg Sum.inr (Subsingleton.elim _ _) }
  let e : Fin d ⊕ Fin 1 ≃ Fin (d + 1) := finSumFinEquiv
  have hz : Matrix.det (P.submatrix er ec) = 0 := by
    rw [← Matrix.det_submatrix_equiv_self e.symm (P.submatrix er ec)]
    exact _hnext (e.symm.toEmbedding.trans er) (e.symm.toEmbedding.trans ec)
  let c : Matrix (Fin d) (Fin 1) R := fun a _ => P (rows a) j
  let r : Matrix (Fin 1) (Fin d) R := fun _ b => P i (cols b)
  let z : Matrix (Fin 1) (Fin 1) R := fun _ _ => P i j
  have hblock : P.submatrix er ec = Matrix.fromBlocks B c r z := by
    ext a b
    cases a <;> cases b <;> rfl
  let : Invertible B := Matrix.invertibleOfIsUnitDet B _hunit
  rw [hblock, Matrix.det_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv] at hz
  have hcorner := _hunit.mul_right_eq_zero.mp hz
  rw [Matrix.det_fin_one] at hcorner
  exact sub_eq_zero.mp hcorner
theorem Submission.p05_ibsrm_mismatched_support_zero_a5b449214a
    {R : Type*} [CommRing R] (n p t d : ℕ)
    (P : Matrix (Fin n) (Fin p) R)
    (rows : Fin d ↪ (Fin n ⊕ Fin t)) (cols : Fin d ↪ (Fin p ⊕ Fin t))
    (_h : ¬ (∀ a : Fin t, (∃ i : Fin d, rows i = Sum.inr a) ↔
      (∃ j : Fin d, cols j = Sum.inr a))) :
    Matrix.det ((Matrix.fromBlocks P 0 0 (1 : Matrix (Fin t) (Fin t) R)).submatrix
      rows cols) = 0 := by
  classical
  obtain ⟨a, ha⟩ := not_forall.mp _h
  by_cases hr : ∃ i : Fin d, rows i = Sum.inr a
  · have hc : ¬ ∃ j : Fin d, cols j = Sum.inr a :=
      fun hc => ha ⟨fun _ => hc, fun _ => hr⟩
    obtain ⟨i, hi⟩ := hr
    apply Matrix.det_eq_zero_of_row_eq_zero i
    intro j
    rw [Matrix.submatrix_apply, hi]
    cases hj : cols j with
    | inl b => rfl
    | inr b =>
        have hab : a ≠ b := by
          intro hab
          exact hc ⟨j, hj.trans (congrArg Sum.inr hab.symm)⟩
        simp only [Matrix.fromBlocks_apply₂₂, Matrix.one_apply, if_neg hab]
  · have hc : ∃ j : Fin d, cols j = Sum.inr a := by
      by_contra hc
      exact ha ⟨fun h => (hr h).elim, fun h => (hc h).elim⟩
    obtain ⟨j, hj⟩ := hc
    apply Matrix.det_eq_zero_of_column_eq_zero j
    intro i
    rw [Matrix.submatrix_apply, hj]
    cases hi : rows i with
    | inl b => rfl
    | inr b =>
        have hba : b ≠ a := by
          intro hba
          exact hr ⟨i, hi.trans (congrArg Sum.inr hba)⟩
        simp only [Matrix.fromBlocks_apply₂₂, Matrix.one_apply, if_neg hba]

theorem Submission.p05_ibsrm_matching_support_blocks_a5b449214a
    {R : Type*} [CommRing R] (n p t d : ℕ) (P : Matrix (Fin n) (Fin p) R)
    (rows : Fin d ↪ (Fin n ⊕ Fin t)) (cols : Fin d ↪ (Fin p ⊕ Fin t))
    (_h : ∀ a : Fin t, (∃ i : Fin d, rows i = Sum.inr a) ↔
      (∃ j : Fin d, cols j = Sum.inr a)) :
    ∃ l : ℕ, l ≤ t ∧ l ≤ d ∧
      ∃ (rows' : Fin (d - l) ↪ Fin n) (cols' : Fin (d - l) ↪ Fin p)
        (er ec : (Fin (d - l) ⊕ Fin l) ≃ Fin d),
        ((Matrix.fromBlocks P 0 0 (1 : Matrix (Fin t) (Fin t) R)).submatrix rows cols).submatrix er ec =
          Matrix.fromBlocks (P.submatrix rows' cols') 0 0
            (1 : Matrix (Fin l) (Fin l) R) := by
  classical
  let A := {a : Fin n // ∃ i : Fin d, rows i = Sum.inl a}
  let B := {b : Fin p // ∃ j : Fin d, cols j = Sum.inl b}
  let S := {a : Fin t // ∃ i : Fin d, rows i = Sum.inr a}
  let br : Fin d ≃ A ⊕ S :=
    (Equiv.ofInjective rows rows.injective).trans Equiv.subtypeSum
  let bc : Fin d ≃ B ⊕ S :=
    ((Equiv.ofInjective cols cols.injective).trans Equiv.subtypeSum).trans
      (Equiv.sumCongr (Equiv.refl B) (Equiv.subtypeEquivRight (fun a => (_h a).symm)))
  let l := Fintype.card S
  have hlt : l ≤ t := by
    simpa only [Fintype.card_fin] using
      (Fintype.card_le_of_injective (Subtype.val : S → Fin t) Subtype.val_injective)
  have hr : d = Fintype.card A + l := by
    simpa only [Fintype.card_fin, Fintype.card_sum] using Fintype.card_congr br
  have hc : d = Fintype.card B + l := by
    simpa only [Fintype.card_fin, Fintype.card_sum] using Fintype.card_congr bc
  have hld : l ≤ d := by omega
  have hA : Fintype.card A = d - l := by omega
  have hB : Fintype.card B = d - l := by omega
  let α : Fin (d - l) ≃ A := (monoEquivOfFin A hA).toEquiv
  let β : Fin (d - l) ≃ B := (monoEquivOfFin B hB).toEquiv
  let γ : Fin l ≃ S := (monoEquivOfFin S rfl).toEquiv
  let rows' : Fin (d - l) ↪ Fin n :=
    ⟨fun i => (α i).val, Subtype.val_injective.comp α.injective⟩
  let cols' : Fin (d - l) ↪ Fin p :=
    ⟨fun j => (β j).val, Subtype.val_injective.comp β.injective⟩
  let s : Fin l ↪ Fin t :=
    ⟨fun a => (γ a).val, Subtype.val_injective.comp γ.injective⟩
  let er : (Fin (d - l) ⊕ Fin l) ≃ Fin d := (α.sumCongr γ).trans br.symm
  let ec : (Fin (d - l) ⊕ Fin l) ≃ Fin d := (β.sumCongr γ).trans bc.symm
  have hr₁ (i : Fin (d - l)) : rows (er (Sum.inl i)) = Sum.inl (rows' i) := by
    change rows ((Equiv.ofInjective rows rows.injective).symm
      ⟨Sum.inl (α i).val, (α i).property⟩) = _
    exact Equiv.apply_ofInjective_symm rows.injective _
  have hr₂ (a : Fin l) : rows (er (Sum.inr a)) = Sum.inr (s a) := by
    change rows ((Equiv.ofInjective rows rows.injective).symm
      ⟨Sum.inr (γ a).val, (γ a).property⟩) = _
    exact Equiv.apply_ofInjective_symm rows.injective _
  have hc₁ (j : Fin (d - l)) : cols (ec (Sum.inl j)) = Sum.inl (cols' j) := by
    change cols ((Equiv.ofInjective cols cols.injective).symm
      ⟨Sum.inl (β j).val, (β j).property⟩) = _
    exact Equiv.apply_ofInjective_symm cols.injective _
  have hc₂ (b : Fin l) : cols (ec (Sum.inr b)) = Sum.inr (s b) := by
    change cols ((Equiv.ofInjective cols cols.injective).symm
      ⟨Sum.inr (γ b).val, (_h (γ b).val).mp (γ b).property⟩) = _
    exact Equiv.apply_ofInjective_symm cols.injective _
  refine ⟨l, hlt, hld, rows', cols', er, ec, ?_⟩
  ext i j
  rcases i with i | a <;> rcases j with j | b
  · simp only [Matrix.submatrix_apply, hr₁, hc₁, Matrix.fromBlocks_apply₁₁]
  · simp only [Matrix.submatrix_apply, hr₁, hc₂, Matrix.fromBlocks_apply₁₂,
      Matrix.zero_apply]
  · simp only [Matrix.submatrix_apply, hr₂, hc₁, Matrix.fromBlocks_apply₂₁,
      Matrix.zero_apply]
  · simp only [Matrix.submatrix_apply, hr₂, hc₂, Matrix.fromBlocks_apply₂₂,
      Matrix.one_apply, s.injective.eq_iff]


theorem Submission.p05_ums_inner_inverse_of_minors_a5b449214a
    {R : Type*} [CommRing R] (n p d : ℕ)
    (P : Matrix (Fin n) (Fin p) R)
    (rows : Fin d ↪ Fin n) (cols : Fin d ↪ Fin p)
    (_hunit : IsUnit (Matrix.det (P.submatrix rows cols)))
    (_hnext : ∀ (rows' : Fin (d + 1) ↪ Fin n) (cols' : Fin (d + 1) ↪ Fin p),
      Matrix.det (P.submatrix rows' cols') = 0) :
    ∃ Q : Matrix (Fin p) (Fin n) R, P * Q * P = P := by
  exact Submission.p05_umgi_inner_inverse_of_reconstruction_a5b449214a
    n p d P rows cols (P.submatrix rows cols)⁻¹
    (Submission.p05_umgi_minor_reconstruction_a5b449214a
      n p d P rows cols _hunit _hnext)
theorem Submission.p05_ibs_reduce_minor_a5b449214a :
    ∀ {R : Type*} [CommRing R] (n p t d : ℕ) (P : Matrix (Fin n) (Fin p) R)
      (rows : Fin d ↪ (Fin n ⊕ Fin t)) (cols : Fin d ↪ (Fin p ⊕ Fin t)),
      let E : Matrix (Fin n ⊕ Fin t) (Fin p ⊕ Fin t) R :=
        Matrix.fromBlocks P 0 0 (1 : Matrix (Fin t) (Fin t) R)
      Matrix.det (E.submatrix rows cols) = 0 ∨
        ∃ l : ℕ, l ≤ t ∧ l ≤ d ∧
          ∃ (rows' : Fin (d - l) ↪ Fin n) (cols' : Fin (d - l) ↪ Fin p),
            Matrix.det (E.submatrix rows cols) = Matrix.det (P.submatrix rows' cols') ∨
              Matrix.det (E.submatrix rows cols) = -Matrix.det (P.submatrix rows' cols') := by
  intro R _ n p t d P rows cols E
  classical
  by_cases hsupport : ∀ a : Fin t,
      (∃ i : Fin d, rows i = Sum.inr a) ↔ (∃ j : Fin d, cols j = Sum.inr a)
  · obtain ⟨l, hlt, hld, rows', cols', er, ec, hblocks⟩ :=
      Submission.p05_ibsrm_matching_support_blocks_a5b449214a n p t d P rows cols hsupport
    refine Or.inr ⟨l, hlt, hld, rows', cols', ?_⟩
    -- The common identity block has determinant one; reindexing contributes a sign.
    have hdet := Matrix.det_reindex er.symm ec.symm (E.submatrix rows cols)
    simp only [Matrix.reindex_apply, Equiv.symm_symm, E, hblocks,
      Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one] at hdet
    rcases Int.isUnit_eq_one_or (Equiv.Perm.sign (ec.symm.trans er)).isUnit with hs | hs
    · left
      simpa [hs] using hdet.symm
    · right
      simpa [hs] using congrArg (fun x : R => -x) hdet.symm
  · exact Or.inl
      (Submission.p05_ibsrm_mismatched_support_zero_a5b449214a n p t d P rows cols hsupport)


namespace Submission

theorem p05_ptm_split_of_unit_minor_a5b449214a
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    (n p d : ℕ) (P : Matrix (Fin n) (Fin p) R) (π : (Fin n → R) →ₗ[R] M)
    (_hπ : Function.Surjective π) (_hker : LinearMap.ker π = LinearMap.range P.mulVecLin)
    (rows : Fin d ↪ Fin n) (cols : Fin d ↪ Fin p)
    (_hunit : IsUnit (Matrix.det (P.submatrix rows cols)))
    (_hnext : ∀ (rows' : Fin (d + 1) ↪ Fin n) (cols' : Fin (d + 1) ↪ Fin p),
      Matrix.det (P.submatrix rows' cols') = 0) :
    ∃ s : M →ₗ[R] (Fin n → R), π.comp s = LinearMap.id := by
  obtain ⟨Q, hQ⟩ := Submission.p05_ums_inner_inverse_of_minors_a5b449214a
    n p d P rows cols _hunit _hnext
  refine Submission.p05_ums_section_of_inner_inverse_a5b449214a
    P.mulVecLin Q.mulVecLin π ?_ _hπ _hker
  simpa only [Matrix.mulVecLin_mul] using
    congrArg (fun A : Matrix (Fin n) (Fin p) R => A.mulVecLin) hQ

end Submission
theorem Submission.p05_pie_identity_block_stabilization_a5b449214a
    {R : Type*} [CommRing R] (n p t r : ℕ) (P : Matrix (Fin n) (Fin p) R) :
    (Ideal.span {x : R |
      ∃ (rows : Fin (n + t - r) ↪ (Fin n ⊕ Fin t))
        (cols : Fin (n + t - r) ↪ (Fin p ⊕ Fin t)),
        x = Matrix.det
          ((Matrix.fromBlocks P 0 0 (1 : Matrix (Fin t) (Fin t) R)).submatrix rows cols)}) =
    Ideal.span {x : R | ∃ (rows : Fin (n - r) ↪ Fin n) (cols : Fin (n - r) ↪ Fin p),
      x = Matrix.det (P.submatrix rows cols)} := by
  classical
  let D (a : ℕ) : Ideal R := Ideal.span
    {x : R | ∃ (rows : Fin a ↪ Fin n) (cols : Fin a ↪ Fin p),
      x = Matrix.det (P.submatrix rows cols)}
  let E := Matrix.fromBlocks P 0 0 (1 : Matrix (Fin t) (Fin t) R)
  let J : Ideal R := Ideal.span
    {x : R | ∃ (rows : Fin (n + t - r) ↪ (Fin n ⊕ Fin t))
      (cols : Fin (n + t - r) ↪ (Fin p ⊕ Fin t)),
      x = Matrix.det (E.submatrix rows cols)}
  change J = D (n - r)
  by_cases hnr : n ≤ r
  · have hd : n + t - r ≤ t := by omega
    let e := Fin.castLEEmb hd
    let rows : Fin (n + t - r) ↪ (Fin n ⊕ Fin t) := e.trans Function.Embedding.inr
    let cols : Fin (n + t - r) ↪ (Fin p ⊕ Fin t) := e.trans Function.Embedding.inr
    have hmatrix : E.submatrix rows cols = (1 : Matrix (Fin (n + t - r)) _ R) := by
      ext i j
      change (1 : Matrix (Fin t) (Fin t) R) (e i) (e j) =
        (1 : Matrix (Fin (n + t - r)) _ R) i j
      simp only [Matrix.one_apply, e.injective.eq_iff]
    have hJ : J = ⊤ := by
      apply (Ideal.eq_top_iff_one J).mpr
      exact Ideal.subset_span ⟨rows, cols, by rw [hmatrix, Matrix.det_one]⟩
    have hD : D (n - r) = ⊤ := by
      rw [Nat.sub_eq_zero_of_le hnr]
      apply (Ideal.eq_top_iff_one (D 0)).mpr
      exact Ideal.subset_span
        ⟨Function.Embedding.ofIsEmpty, Function.Embedding.ofIsEmpty, Matrix.det_isEmpty.symm⟩
    exact hJ.trans hD.symm
  · have hd : n + t - r = (n - r) + t := by omega
    have hdesc {a b : ℕ} (hab : a ≤ b) : D b ≤ D a := by
      induction hab with
      | refl => exact le_rfl
      | @step b _ ih =>
        exact le_trans (Submission.p05_pie_successive_minor_containment_a5b449214a P b) ih
    apply le_antisymm
    · apply Ideal.span_le.mpr
      rintro x ⟨rows, cols, rfl⟩
      rcases Submission.p05_ibs_reduce_minor_a5b449214a n p t (n + t - r) P rows cols with
        hz | ⟨l, hlt, _, rows', cols', hminor⟩
      · change Matrix.det (E.submatrix rows cols) = 0 at hz
        rw [hz]
        exact Ideal.zero_mem _
      · have hsize : n - r ≤ n + t - r - l := by omega
        have hmem : Matrix.det (P.submatrix rows' cols') ∈ D (n - r) :=
          hdesc hsize (Ideal.subset_span ⟨rows', cols', rfl⟩)
        rcases hminor with hminor | hminor
        · change Matrix.det (E.submatrix rows cols) = _ at hminor
          rw [hminor]
          exact hmem
        · change Matrix.det (E.submatrix rows cols) = _ at hminor
          rw [hminor]
          exact (D (n - r)).neg_mem hmem
    · apply Ideal.span_le.mpr
      rintro x ⟨rows, cols, rfl⟩
      obtain ⟨rows', cols', hminor⟩ :=
        Submission.p05_ibs_extend_minor_a5b449214a n p t (n - r) P rows cols
      change Matrix.det (P.submatrix rows cols) ∈ Ideal.span
        {x : R | ∃ (rows : Fin (n + t - r) ↪ (Fin n ⊕ Fin t))
          (cols : Fin (n + t - r) ↪ (Fin p ⊕ Fin t)),
          x = Matrix.det (E.submatrix rows cols)}
      rw [hd]
      exact Ideal.subset_span ⟨rows', cols', hminor.symm⟩

namespace Submission

theorem p05_fr_projective_of_trivial_minors_a5b449214a
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    (n p : ℕ) (P : Matrix (Fin n) (Fin p) R) (π : (Fin n → R) →ₗ[R] M)
    (_hπ : Function.Surjective π)
    (_hker : LinearMap.ker π = LinearMap.range P.mulVecLin)
    (_hminor : ∀ d : ℕ,
      let J : Ideal R := Ideal.span
        {x : R | ∃ (rows : Fin d ↪ Fin n) (cols : Fin d ↪ Fin p),
          x = Matrix.det (P.submatrix rows cols)}
      J = ⊥ ∨ J = ⊤) :
    Module.Projective R M := by
  classical
  -- Choose a maximal size whose minors generate the unit ideal.
  let J : ℕ → Ideal R := fun d ↦ Ideal.span
    {x : R | ∃ (rows : Fin d ↪ Fin n) (cols : Fin d ↪ Fin p),
      x = Matrix.det (P.submatrix rows cols)}
  have hzero : J 0 = ⊤ := by
    apply (Ideal.eq_top_iff_one _).mpr
    apply Ideal.subset_span
    exact ⟨Function.Embedding.ofIsEmpty, Function.Embedding.ofIsEmpty,
      Matrix.det_isEmpty.symm⟩
  let d := Nat.findGreatest (fun k ↦ J k = ⊤) n
  have hd : J d = ⊤ :=
    Nat.findGreatest_spec (P := fun k ↦ J k = ⊤) (Nat.zero_le n) hzero
  have hnext : ∀ (rows : Fin (d + 1) ↪ Fin n) (cols : Fin (d + 1) ↪ Fin p),
      Matrix.det (P.submatrix rows cols) = 0 := by
    intro rows cols
    have hbound : d + 1 ≤ n := by
      simpa using Fintype.card_le_of_injective rows rows.injective
    have hnot : J (d + 1) ≠ ⊤ :=
      Nat.findGreatest_is_greatest (P := fun k ↦ J k = ⊤) (Nat.lt_succ_self d) hbound
    have hbot : J (d + 1) = ⊥ := (_hminor (d + 1)).resolve_right hnot
    have hmem : Matrix.det (P.submatrix rows cols) ∈ J (d + 1) :=
      Ideal.subset_span ⟨rows, cols, rfl⟩
    simpa only [hbot, Ideal.mem_bot] using hmem
  -- Enumerate all minors of this size, including the unique empty minor.
  let I := (Fin d ↪ Fin n) × (Fin d ↪ Fin p)
  let q := Fintype.card I
  let e : Fin q ≃ I := (Fintype.equivFin I).symm
  let f : Fin q → R := fun i ↦ Matrix.det (P.submatrix (e i).1 (e i).2)
  have hcover : Ideal.span (Set.range f) = ⊤ := by
    convert hd using 1
    congr 1
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨(e i).1, (e i).2, rfl⟩
    · rintro ⟨rows, cols, rfl⟩
      exact ⟨e.symm (rows, cols), by simp [f]⟩
  obtain ⟨s, hs⟩ := p05_ptm_split_of_away_splits_a5b449214a
    n p q P π _hπ _hker f hcover (by
      intro i
      let S := Submonoid.powers (f i)
      let A := Localization.Away (f i)
      let loc (k : ℕ) : (Fin k → R) →ₗ[R] (Fin k → A) :=
        LinearMap.pi fun j ↦ (Algebra.linearMap R A).comp (LinearMap.proj j)
      let mloc := LocalizedModule.mkLinearMap S M
      let PA : Matrix (Fin n) (Fin p) A := P.map (algebraMap R A)
      let πA : (Fin n → A) →ₗ[A] LocalizedModule S M :=
        IsLocalizedModule.mapExtendScalars S (loc n) mloc A π
      have hπA : Function.Surjective πA :=
        IsLocalizedModule.map_surjective S (loc n) mloc π _hπ
      -- Localization of the matrix map is entrywise localization of the matrix.
      have hP : IsLocalizedModule.map S (loc p) (loc n) P.mulVecLin =
          PA.mulVecLin.restrictScalars R := by
        apply IsLocalizedModule.linearMap_ext S (loc p) (loc n)
        rw [IsLocalizedModule.map_comp]
        apply LinearMap.ext
        intro x
        funext j
        simp [loc, PA, Matrix.mulVec, dotProduct]
      have hex := IsLocalizedModule.map_exact S (loc p) (loc n) mloc
        P.mulVecLin π (LinearMap.exact_iff.mpr _hker)
      have hkerA : LinearMap.ker πA = LinearMap.range PA.mulVecLin := by
        apply LinearMap.exact_iff.mp
        rw [hP] at hex
        exact hex
      have hunit : IsUnit (Matrix.det (PA.submatrix (e i).1 (e i).2)) := by
        change IsUnit (Matrix.det ((algebraMap R A).mapMatrix
          (P.submatrix (e i).1 (e i).2)))
        rw [← RingHom.map_det]
        exact IsLocalization.map_units A ⟨f i, Submonoid.mem_powers (f i)⟩
      have hnextA : ∀ (rows : Fin (d + 1) ↪ Fin n) (cols : Fin (d + 1) ↪ Fin p),
          Matrix.det (PA.submatrix rows cols) = 0 := by
        intro rows cols
        change Matrix.det ((algebraMap R A).mapMatrix (P.submatrix rows cols)) = 0
        rw [← RingHom.map_det, hnext, map_zero]
      obtain ⟨sA, hsA⟩ := p05_ptm_split_of_unit_minor_a5b449214a
        n p d PA πA hπA hkerA (e i).1 (e i).2 hunit hnextA
      -- Identify localized finite free modules with tuples over the localized ring.
      let E : (Fin n → A) ≃ₗ[A] LocalizedModule S (Fin n → R) :=
        (IsLocalizedModule.linearEquiv S (loc n)
          (LocalizedModule.mkLinearMap S (Fin n → R))).extendScalarsOfIsLocalization S A
      have hπE : (LocalizedModule.map S π).comp E.toLinearMap = πA := by
        apply LinearMap.restrictScalars_injective R
        apply IsLocalizedModule.linearMap_ext S (loc n) mloc
        apply LinearMap.ext
        intro x
        simp [E, πA, mloc, IsLocalizedModule.mapExtendScalars,
          LocalizedModule.mkLinearMap_apply]
        exact LocalizedModule.map_mk S π x 1
      refine ⟨E.toLinearMap.comp sA, ?_⟩
      rw [← LinearMap.comp_assoc, hπE, hsA])
  exact Module.Projective.of_split s π hs

end Submission
namespace Submission

/-- The determinantal ideal of a finite presentation is independent of the presentation. -/
theorem p05_fr_rhm_presentation_ideals_eq_a5b449214a
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    (n p n' p' : ℕ) (P : Matrix (Fin n) (Fin p) R)
    (Q : Matrix (Fin n') (Fin p') R)
    (π : (Fin n → R) →ₗ[R] M) (π' : (Fin n' → R) →ₗ[R] M)
    (_hπ : Function.Surjective π)
    (_hker : LinearMap.ker π = LinearMap.range P.mulVecLin)
    (_hπ' : Function.Surjective π')
    (_hker' : LinearMap.ker π' = LinearMap.range Q.mulVecLin) (r : ℕ) :
    (Ideal.span {x : R | ∃ (rows : Fin (n - r) ↪ Fin n)
      (cols : Fin (n - r) ↪ Fin p), x = Matrix.det (P.submatrix rows cols)}) =
    Ideal.span {x : R | ∃ (rows : Fin (n' - r) ↪ Fin n')
      (cols : Fin (n' - r) ↪ Fin p'), x = Matrix.det (Q.submatrix rows cols)} := by
  classical
  let D : {ι κ : Type} → Matrix ι κ R → ℕ → Ideal R := fun {_ _} B d =>
    Ideal.span {x : R | ∃ (rows : Fin d ↪ _) (cols : Fin d ↪ _),
      x = Matrix.det (B.submatrix rows cols)}
  -- Changing the finite list of relation columns does not change its minor ideals.
  have hcol {ι κ ν : Type} [Fintype ι] [Fintype κ] [Fintype ν]
      (B : Matrix ι κ R) (C : Matrix ι ν R)
      (h : LinearMap.range B.mulVecLin ≤ LinearMap.range C.mulVecLin) (d : ℕ) :
      D B d ≤ D C d := by
    have hc (j : κ) : ∃ v, C.mulVecLin v = B.mulVecLin (Pi.single j 1) :=
      h ⟨Pi.single j 1, rfl⟩
    choose v hv using hc
    let V : Matrix ν κ R := fun i j => v j i
    have hfactor : C * V = B := by
      ext i j
      calc
        (C * V) i j = (C.mulVecLin (v j)) i := rfl
        _ = (B.mulVecLin (Pi.single j 1)) i := congrFun (hv j) i
        _ = B i j := by simp
    have hh := (p05_pie_minor_product_containment_a5b449214a C V d).trans inf_le_left
    change D (C * V) d ≤ D C d at hh
    rwa [hfactor] at hh
  -- Row reindexing transports the injective selections without changing determinants.
  have hrow {ι κ ν : Type} (B : Matrix ι κ R) (e : ν ≃ ι) (d : ℕ) :
      D (B.submatrix e id) d = D B d := by
    apply congrArg Ideal.span
    ext x
    constructor
    · rintro ⟨rows, cols, hx⟩
      exact ⟨rows.trans e.toEmbedding, cols, hx⟩
    · rintro ⟨rows, cols, hx⟩
      refine ⟨rows.trans e.symm.toEmbedding, cols, ?_⟩
      simpa [Matrix.submatrix, Function.Embedding.trans] using hx
  -- The two triangular row operations reduce the enlarged relation matrix to a block diagonal.
  have hstabilize (a b t : ℕ) (B : Matrix (Fin a) (Fin b) R)
      (A : Matrix (Fin a) (Fin t) R) :
      D (Matrix.fromBlocks B (-A) 0 (1 : Matrix (Fin t) (Fin t) R)) (a + t - r) =
        D B (a - r) := by
    let T := Matrix.fromBlocks B (-A) 0 (1 : Matrix (Fin t) (Fin t) R)
    let S := Matrix.fromBlocks B 0 0 (1 : Matrix (Fin t) (Fin t) R)
    let E := Matrix.fromBlocks (1 : Matrix (Fin a) (Fin a) R) A 0
      (1 : Matrix (Fin t) (Fin t) R)
    let F := Matrix.fromBlocks (1 : Matrix (Fin a) (Fin a) R) (-A) 0
      (1 : Matrix (Fin t) (Fin t) R)
    have hET : E * T = S := by
      simp [E, T, S, Matrix.fromBlocks_multiply]
    have hFS : F * S = T := by
      simp [F, S, T, Matrix.fromBlocks_multiply]
    have hTS : D T (a + t - r) = D S (a + t - r) := by
      apply le_antisymm
      · have hh := (p05_pie_minor_product_containment_a5b449214a F S
          (a + t - r)).trans inf_le_right
        change D (F * S) (a + t - r) ≤ D S (a + t - r) at hh
        rwa [hFS] at hh
      · have hh := (p05_pie_minor_product_containment_a5b449214a E T
          (a + t - r)).trans inf_le_right
        change D (E * T) (a + t - r) ≤ D T (a + t - r) at hh
        rwa [hET] at hh
    exact hTS.trans (p05_pie_identity_block_stabilization_a5b449214a a b t r B)
  -- Lift the second generator list through the first presentation, and conversely.
  obtain ⟨f, hf⟩ := Module.projective_lifting_property π π' _hπ
  obtain ⟨g, hg⟩ := Module.projective_lifting_property π' π _hπ'
  let A := LinearMap.toMatrix' f
  let B := LinearMap.toMatrix' g
  have hA (y : Fin n' → R) : π (A.mulVecLin y) = π' y := by
    simpa [A] using LinearMap.congr_fun hf y
  have hB (y : Fin n → R) : π' (B.mulVecLin y) = π y := by
    simpa [B] using LinearMap.congr_fun hg y
  let T := Matrix.fromBlocks P (-A) 0 (1 : Matrix (Fin n') (Fin n') R)
  let T' := Matrix.fromBlocks Q (-B) 0 (1 : Matrix (Fin n) (Fin n) R)
  let e : (Fin n ⊕ Fin n') ≃ (Fin n' ⊕ Fin n) := Equiv.sumComm _ _
  let U := T'.submatrix e id
  have hT := p05_pie_redundant_generator_relations_a5b449214a n p n' P A π π' _hker hA
  have hT' := p05_pie_redundant_generator_relations_a5b449214a n' p' n Q B π' π _hker' hB
  have hswap (w : (Fin p' ⊕ Fin n) → R) :
      U.mulVecLin w = T'.mulVecLin w ∘ e := rfl
  have hU (z : (Fin n ⊕ Fin n') → R) :
      (∃ w, U.mulVecLin w = z) ↔ ∃ w, T'.mulVecLin w = z ∘ e.symm := by
    constructor
    · rintro ⟨w, hw⟩
      refine ⟨w, ?_⟩
      have hh := congrArg (fun v => v ∘ e.symm) hw
      simpa [hswap, Function.comp_def] using hh
    · rintro ⟨w, hw⟩
      refine ⟨w, ?_⟩
      rw [hswap, hw]
      simp [Function.comp_def]
  -- Both enlarged relation lists generate the kernel of the combined generator map.
  have hrange : LinearMap.range T.mulVecLin = LinearMap.range U.mulVecLin := by
    ext z
    change (∃ w, T.mulVecLin w = z) ↔ ∃ w, U.mulVecLin w = z
    rw [hU, ← hT z, ← hT' (z ∘ e.symm)]
    simp [e, add_comm]
  change D P (n - r) = D Q (n' - r)
  calc
    D P (n - r) = D T (n + n' - r) := (hstabilize n p n' P A).symm
    _ = D U (n + n' - r) :=
      le_antisymm (hcol T U hrange.le _) (hcol U T hrange.ge _)
    _ = D T' (n + n' - r) := hrow T' e _
    _ = D T' (n' + n - r) := by rw [Nat.add_comm n n']
    _ = D Q (n' - r) := hstabilize n' p' n Q B

end Submission


namespace Submission

theorem p05_fr_rhm_base_change_semilinear_invariance_a5b449214a
    {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S]
    {M : Type*} [AddCommGroup M] [Module R M]
    (n p : ℕ) (P : Matrix (Fin n) (Fin p) R) (π : (Fin n → R) →ₗ[R] M)
    (_hπ : Function.Surjective π)
    (_hker : LinearMap.ker π = LinearMap.range P.mulVecLin)
    (θ : S ≃+* S) (T : TensorProduct R S M ≃+ TensorProduct R S M)
    (_hT : ∀ (s : S) (x : TensorProduct R S M), T (s • x) = θ s • T x)
    (r : ℕ) :
    let J : Ideal R := Ideal.span {x : R |
      ∃ (rows : Fin (n - r) ↪ Fin n) (cols : Fin (n - r) ↪ Fin p),
        x = Matrix.det (P.submatrix rows cols)}
    Ideal.map θ.toRingHom (Ideal.map (algebraMap R S) J) =
      Ideal.map (algebraMap R S) J := by
  classical
  dsimp only
  obtain ⟨q, _hq_formula, hq, hqker⟩ :=
    p05_fr_rhm_bcsi_base_changed_presentation_a5b449214a (S := S) n p P π _hπ _hker
  obtain ⟨qθ, _hqθ_formula, hqθ, hqθker⟩ :=
    p05_fr_rhm_bcsi_twisted_presentation_a5b449214a
      n p (P.map (algebraMap R S)) q hq hqker θ T _hT
  -- Extending the ideal commutes with taking the selected determinants.
  have hbase :
      Ideal.map (algebraMap R S) (Ideal.span {x : R |
        ∃ (rows : Fin (n - r) ↪ Fin n) (cols : Fin (n - r) ↪ Fin p),
          x = Matrix.det (P.submatrix rows cols)}) =
      Ideal.span {x : S |
        ∃ (rows : Fin (n - r) ↪ Fin n) (cols : Fin (n - r) ↪ Fin p),
          x = Matrix.det ((P.map (algebraMap R S)).submatrix rows cols)} := by
    rw [Ideal.map_span]
    congr 1
    ext x
    constructor
    · rintro ⟨y, ⟨rows, cols, rfl⟩, rfl⟩
      exact ⟨rows, cols, (algebraMap R S).map_det _⟩
    · rintro ⟨rows, cols, rfl⟩
      exact ⟨_, ⟨rows, cols, rfl⟩, (algebraMap R S).map_det _⟩
  rw [hbase]
  calc
    Ideal.map θ.toRingHom (Ideal.span {x : S |
        ∃ (rows : Fin (n - r) ↪ Fin n) (cols : Fin (n - r) ↪ Fin p),
          x = Matrix.det ((P.map (algebraMap R S)).submatrix rows cols)}) =
        Ideal.span {x : S |
          ∃ (rows : Fin (n - r) ↪ Fin n) (cols : Fin (n - r) ↪ Fin p),
            x = Matrix.det
              (((P.map (algebraMap R S)).map θ.toRingHom).submatrix rows cols)} := by
      rw [Ideal.map_span]
      congr 1
      ext x
      constructor
      · rintro ⟨y, ⟨rows, cols, rfl⟩, rfl⟩
        exact ⟨rows, cols, θ.toRingHom.map_det _⟩
      · rintro ⟨rows, cols, rfl⟩
        exact ⟨_, ⟨rows, cols, rfl⟩, θ.toRingHom.map_det _⟩
    _ = _ :=
      (p05_fr_rhm_presentation_ideals_eq_a5b449214a n p n p
        (P.map (algebraMap R S)) ((P.map (algebraMap R S)).map θ.toRingHom)
        q qθ hq hqker hqθ hqθker r).symm

end Submission


namespace Submission

/-- A subalgebra stable under comultiplication and antipode inherits a compatible Hopf structure. -/
theorem p05_hte_stable_subalgebra_hopf_structure_a5b449214a
    {k : Type*} [Field k] {H : Type*} [CommRing H] [HopfAlgebra k H]
    (D : Subalgebra k H)
    (hΔ : ∀ x ∈ D, Coalgebra.comul (R := k) x ∈
      Submodule.span k {t : TensorProduct k H H |
        ∃ a ∈ D, ∃ b ∈ D, t = TensorProduct.tmul k a b})
    (hS : ∀ x ∈ D, HopfAlgebra.antipode k x ∈ D) :
    ∃ hD : HopfAlgebra k D,
      hD.toHopfAlgebraStruct.toBialgebra.toAlgebra = (inferInstance : Algebra k D) ∧
      (letI : Algebra k D := hD.toHopfAlgebraStruct.toBialgebra.toAlgebra;
       letI : Module k D := Algebra.toModule;
       letI : HopfAlgebra k D := hD;
       ∃ ι : BialgHom k D H, (∀ d : D, ι d = (d : H)) ∧
         ∀ d : D, ((HopfAlgebra.antipode k d : D) : H) =
           HopfAlgebra.antipode k (d : H)) := by
  obtain ⟨bD, hAlg, hInclusion⟩ :=
    p05_hte_sshs_bialgebra_restriction_a5b449214a D hΔ
  let : Algebra k D := bD.toAlgebra
  let : Module k D := Algebra.toModule
  let : Bialgebra k D := bD
  obtain ⟨ι, hι⟩ := hInclusion
  have hInjective : Function.Injective ι := by
    intro a b hab
    apply Subtype.val_injective
    exact (hι a).symm.trans (hab.trans (hι b))
  have hStable : ∀ a : D, ∃ b : D, ι b = HopfAlgebra.antipode k (ι a) := by
    intro a
    refine ⟨⟨HopfAlgebra.antipode k (a : H), hS a a.property⟩, ?_⟩
    rw [hι, hι]
  obtain ⟨hD, hbD, hAntipode⟩ :=
    p05_hte_sshs_antipode_lift_a5b449214a ι hInjective hStable
  change hD.toHopfAlgebraStruct.toBialgebra = bD at hbD
  subst bD
  refine ⟨hD, hAlg, ?_⟩
  let : HopfAlgebra k D := hD
  refine ⟨ι, hι, ?_⟩
  intro d
  simpa only [hι] using hAntipode d

end Submission



namespace Submission

/-- A finite relative Hopf module is projective over the finite type Hopf algebra. -/
theorem p05_fr_finite_relative_hopf_module_projective_a5b449214a
    {k : Type*} [Field k] {A : Type*} [CommRing A] [HopfAlgebra k A]
    [Algebra.FiniteType k A] {H : Type*} [CommRing H] [HopfAlgebra k H]
    (ι : BialgHom k A H) (hι : Function.Injective ι)
    {M : Type*} [AddCommGroup M] [Module k M] [Module A M]
    [IsScalarTower k A M] [Module.Finite A M]
    (μ : M →ₗ[k] TensorProduct k M H)
    (hcoassoc : ∀ m : M,
      TensorProduct.assoc k M H H
          ((TensorProduct.map μ (LinearMap.id : H →ₗ[k] H)) (μ m)) =
        (TensorProduct.map (LinearMap.id : M →ₗ[k] M)
          (Coalgebra.comul (R := k))) (μ m))
    (hcounit : ∀ m : M,
      TensorProduct.rid k M
        ((TensorProduct.map (LinearMap.id : M →ₗ[k] M)
          (Coalgebra.counit (R := k))) (μ m)) = m)
    (hcompat : ∀ (a : A) (m : M),
      let d := Coalgebra.Repr.arbitrary k a
      μ (a • m) = ∑ i ∈ d.index,
        TensorProduct.map ((Algebra.lsmul k k M) (d.left i))
          (LinearMap.mulLeft k (ι (d.right i))) (μ m)) :
    Module.Projective A M := by
  classical
  -- Choose a finite presentation over the Noetherian ring A.
  let : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  let : Module.FinitePresentation A M := Module.finitePresentation_of_finite A M
  obtain ⟨n, p, π, L, hπ, hL⟩ := Module.FinitePresentation.exists_fin' A M
  let P : Matrix (Fin n) (Fin p) A := LinearMap.toMatrix' L
  have hker : LinearMap.ker π = LinearMap.range P.mulVecLin := by
    have hP : P.mulVecLin = L := Matrix.toLin'_toMatrix' L
    rw [hP]
    exact LinearMap.exact_iff.mp hL
  -- Transport scalar extension to M ⊗ H, with its pure-tensor action.
  let e : TensorProduct A (TensorProduct k A H) M ≃ₗ[A] TensorProduct k M H :=
    (TensorProduct.comm A (TensorProduct k A H) M).trans
      (TensorProduct.AlgebraTensorModule.cancelBaseChange k A A M H)
  let : Module (TensorProduct k A H) (TensorProduct k M H) :=
    e.symm.toAddEquiv.module (TensorProduct k A H)
  have he (s : TensorProduct k A H) (x : TensorProduct A (TensorProduct k A H) M) :
      e (s • x) = s • e x := by
    change e (s • x) = e (s • e.symm (e x))
    rw [e.symm_apply_apply]
  have hact (a : A) (h : H) (m : M) (g : H) :
      (TensorProduct.tmul k a h) • (TensorProduct.tmul k m g) =
        TensorProduct.tmul k (a • m) (h * g) := by
    change e ((TensorProduct.tmul k a h) • e.symm (TensorProduct.tmul k m g)) = _
    simp [e, TensorProduct.smul_tmul', Algebra.TensorProduct.tmul_mul_tmul]
  obtain ⟨θ, T, hθ, _hTmul, hT⟩ :=
    p05_fr_rhm_coaction_twist_a5b449214a ι hact μ hcoassoc hcounit hcompat
  let T' : TensorProduct A (TensorProduct k A H) M ≃+
      TensorProduct A (TensorProduct k A H) M :=
    e.toAddEquiv.trans (T.toAddEquiv.trans e.symm.toAddEquiv)
  have hT' (s : TensorProduct k A H) (x : TensorProduct A (TensorProduct k A H) M) :
      T' (s • x) = θ s • T' x := by
    change e.symm (T (e (s • x))) = θ s • e.symm (T (e x))
    apply e.injective
    rw [e.apply_symm_apply, he, hT, he, e.apply_symm_apply]
  -- Each presentation ideal is a coideal, hence zero or the unit ideal.
  have hF (r : ℕ) :
      let J : Ideal A := Ideal.span {x : A | ∃
        (rows : Fin (n - r) ↪ Fin n) (cols : Fin (n - r) ↪ Fin p),
        x = Matrix.det (P.submatrix rows cols)}
      J = ⊥ ∨ J = ⊤ := by
    dsimp only
    let J : Ideal A := Ideal.span {x : A | ∃
      (rows : Fin (n - r) ↪ Fin n) (cols : Fin (n - r) ↪ Fin p),
      x = Matrix.det (P.submatrix rows cols)}
    have hstable : Ideal.map θ.toRingEquiv.toRingHom
        (Ideal.map (algebraMap A (TensorProduct k A H)) J) =
        Ideal.map (algebraMap A (TensorProduct k A H)) J :=
      p05_fr_rhm_base_change_semilinear_invariance_a5b449214a
        n p P π hπ hker θ.toRingEquiv T' hT' r
    apply p05_fr_coideal_ideal_dichotomy_a5b449214a (k := k) J
    intro a ha
    apply p05_fr_rhm_tensor_ideal_descent_a5b449214a ι.toLinearMap hι J
    have halg : algebraMap A (TensorProduct k A H) =
        (Algebra.TensorProduct.includeLeft : A →ₐ[k] TensorProduct k A H).toRingHom := by
      ext b
      simp
    rw [← halg]
    have ha' : algebraMap A (TensorProduct k A H) a ∈
        Ideal.map (algebraMap A (TensorProduct k A H)) J :=
      Ideal.mem_map_of_mem _ ha
    have hθa := Ideal.mem_map_of_mem θ.toRingEquiv.toRingHom ha'
    rw [hstable] at hθa
    simpa [Algebra.TensorProduct.algebraMap_apply, hθ,
      ← Algebra.TensorProduct.one_def] using hθa
  apply p05_fr_projective_of_trivial_minors_a5b449214a n p P π hπ hker
  intro d
  dsimp only
  by_cases hd : d ≤ n
  · have hnd : n - (n - d) = d := by omega
    have hf := hF (n - d)
    dsimp only at hf
    rw [hnd] at hf
    exact hf
  · left
    have hempty : {x : A | ∃ (rows : Fin d ↪ Fin n) (cols : Fin d ↪ Fin p),
        x = Matrix.det (P.submatrix rows cols)} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro x ⟨rows, cols, hx⟩
      exact hd (by simpa only [Fintype.card_fin] using
        Fintype.card_le_of_injective rows rows.injective)
    rw [hempty, Ideal.span_empty]

end Submission
namespace Submission

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency.types false in
theorem p05_finite_retraction_a5b449214a
    {k : Type*} [Field k] {H : Type*} [CommRing H] [HopfAlgebra k H]
    (A : Subalgebra k H) [Algebra.FiniteType k A]
    (hΔ : ∀ x ∈ A, Coalgebra.comul (R := k) x ∈
      Submodule.span k {t : TensorProduct k H H | ∃ a ∈ A, ∃ b ∈ A,
        t = TensorProduct.tmul k a b})
    (hS : ∀ x ∈ A, HopfAlgebra.antipode k x ∈ A)
    (V : Submodule k H) [FiniteDimensional k V] (h1 : (1 : H) ∈ V)
    (hV : ∀ x ∈ V, Coalgebra.comul (R := k) x ∈
      Submodule.span k {t : TensorProduct k H H | ∃ a ∈ V, ∃ b : H,
        t = TensorProduct.tmul k a b}) :
    ∃ r : (Submodule.span A (V : Set H)) →ₗ[A] A,
      ∀ (a : A) (ha : (a : H) ∈ Submodule.span A (V : Set H)),
        r ⟨(a : H), ha⟩ = a := by
  classical
  -- Restrict the Hopf structure along the injective tensor inclusions (proof step 1).
  let i : A →ₗ[k] H := A.val.toLinearMap
  have hi : Function.Injective i := Subtype.val_injective
  obtain ⟨p, hp⟩ := i.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hi)
  have hpi (a : A) : p (i a) = a := LinearMap.congr_fun hp a
  let δ : A →ₗ[k] A ⊗[k] A :=
    (TensorProduct.map p p).comp ((Coalgebra.comul (R := k)).comp i)
  have hδ (a : A) : TensorProduct.map i i (δ a) = Coalgebra.comul (R := k) (i a) := by
    change TensorProduct.map i i (TensorProduct.map p p (Coalgebra.comul (R := k) (i a))) = _
    have hz := hΔ (i a) a.property
    generalize Coalgebra.comul (R := k) (i a) = z at hz ⊢
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨x, hx, y, hy, rfl⟩ := hz
      change i (p (i ⟨x, hx⟩)) ⊗ₜ[k] i (p (i ⟨y, hy⟩)) = _
      rw [hpi, hpi]
      rfl
    | zero => simp
    | add x y _ _ hx hy => simp only [map_add, hx, hy]
    | smul c x _ hx => simp only [map_smul, hx]
  have hδmap : (TensorProduct.map i i).comp δ = (Coalgebra.comul (R := k)).comp i :=
    LinearMap.ext hδ
  have ht : Function.Injective (TensorProduct.map i i) :=
    TensorProduct.map_injective_of_flat_flat _ _ hi hi
  let ε : A →ₗ[k] k := (Coalgebra.counit (R := k)).comp i
  let : Coalgebra k A :=
    { comul := δ
      counit := ε
      coassoc := by
        ext a : 1
        apply TensorProduct.map_injective_of_flat_flat i (TensorProduct.map i i) hi ht
        change TensorProduct.map i (TensorProduct.map i i)
          (TensorProduct.assoc k A A A (TensorProduct.map δ LinearMap.id (δ a))) =
          TensorProduct.map i (TensorProduct.map i i) (TensorProduct.map LinearMap.id δ (δ a))
        rw [TensorProduct.map_map_assoc]
        simp only [TensorProduct.map_map, LinearMap.comp_id, hδmap]
        have he : TensorProduct.map ((Coalgebra.comul (R := k)).comp i) i =
            (TensorProduct.map (Coalgebra.comul (R := k)) LinearMap.id).comp
              (TensorProduct.map i i) := by
          ext a b
          rfl
        have he' : TensorProduct.map i ((Coalgebra.comul (R := k)).comp i) =
            (TensorProduct.map LinearMap.id (Coalgebra.comul (R := k))).comp
              (TensorProduct.map i i) := by
          ext a b
          rfl
        rw [he, he']
        simp only [LinearMap.comp_apply, hδ]
        exact Coalgebra.coassoc_apply (R := k) (i a)
      rTensor_counit_comp_comul := by
        ext a : 1
        apply TensorProduct.map_injective_of_flat_flat (LinearMap.id : k →ₗ[k] k) i
          Function.injective_id hi
        change TensorProduct.map LinearMap.id i (TensorProduct.map ε LinearMap.id (δ a)) = _
        simp only [TensorProduct.map_map, LinearMap.id_comp, LinearMap.comp_id]
        change TensorProduct.map ((Coalgebra.counit (R := k)).comp i) i (δ a) = _
        rw [show i = (LinearMap.id : H →ₗ[k] H).comp i from rfl, TensorProduct.map_comp]
        simp only [LinearMap.comp_apply, LinearMap.id_comp, hδ,
          TensorProduct.map_tmul, LinearMap.id_apply, TensorProduct.mk_apply]
        exact Coalgebra.rTensor_counit_comul (i a)
      lTensor_counit_comp_comul := by
        ext a : 1
        apply TensorProduct.map_injective_of_flat_flat i (LinearMap.id : k →ₗ[k] k)
          hi Function.injective_id
        change TensorProduct.map i LinearMap.id (TensorProduct.map LinearMap.id ε (δ a)) = _
        simp only [TensorProduct.map_map, LinearMap.id_comp, LinearMap.comp_id]
        change TensorProduct.map i ((Coalgebra.counit (R := k)).comp i) (δ a) = _
        rw [show i = (LinearMap.id : H →ₗ[k] H).comp i from rfl, TensorProduct.map_comp]
        simp only [LinearMap.comp_apply, LinearMap.id_comp, hδ,
          TensorProduct.map_tmul, LinearMap.id_apply, TensorProduct.mk_apply, LinearMap.flip_apply]
        exact Coalgebra.lTensor_counit_comul (i a) }
  let : Bialgebra k A := Bialgebra.mk' k A
    (by change Coalgebra.counit (R := k) (1 : H) = 1; simp)
    (by intros a b; exact Bialgebra.counit_mul (i a) (i b))
    (by
      change δ 1 = 1
      apply ht
      rw [hδ]
      change Coalgebra.comul (R := k) (1 : H) =
        Algebra.TensorProduct.map A.val A.val 1
      simp)
    (by
      intros a b
      change δ (a * b) = δ a * δ b
      apply ht
      rw [hδ]
      change Coalgebra.comul (R := k) (i a * i b) =
        Algebra.TensorProduct.map A.val A.val (δ a * δ b)
      rw [map_mul (Algebra.TensorProduct.map A.val A.val)]
      change _ = TensorProduct.map i i (δ a) * TensorProduct.map i i (δ b)
      rw [hδ, hδ, Bialgebra.comul_mul])
  let sA : A →ₗ[k] A := ((HopfAlgebra.antipode k).comp i).codRestrict A.toSubmodule
    (fun a => hS (i a) a.property)
  let : HopfAlgebra k A :=
    { antipode := sA
      mul_antipode_rTensor_comul := by
        have he : i.comp ((LinearMap.mul' k A).comp (sA.rTensor A)) =
            ((LinearMap.mul' k H).comp ((HopfAlgebra.antipode k).rTensor H)).comp
              (TensorProduct.map i i) := by
          ext a b
          rfl
        ext a : 1
        apply hi
        change (i.comp ((LinearMap.mul' k A).comp (sA.rTensor A))) (δ a) = _
        rw [he]
        simp only [LinearMap.comp_apply, hδ, HopfAlgebra.mul_antipode_rTensor_comul_apply]
        rfl
      mul_antipode_lTensor_comul := by
        have he : i.comp ((LinearMap.mul' k A).comp (sA.lTensor A)) =
            ((LinearMap.mul' k H).comp ((HopfAlgebra.antipode k).lTensor H)).comp
              (TensorProduct.map i i) := by
          ext a b
          rfl
        ext a : 1
        apply hi
        change (i.comp ((LinearMap.mul' k A).comp (sA.lTensor A))) (δ a) = _
        rw [he]
        simp only [LinearMap.comp_apply, hδ, HopfAlgebra.mul_antipode_lTensor_comul_apply]
        rfl }
  let ι : BialgHom k A H :=
    { toLinearMap := i, counit_comp := rfl, map_comp_comul := hδmap,
      map_one' := A.val.map_one, map_mul' := A.val.map_mul }
  -- Restrict the coaction to the finite A-span of V (proof step 3).
  let N : Submodule A H := Submodule.span A (V : Set H)
  let : Module.Finite A N := Module.Finite.of_fg (Module.Finite.iff_fg.mp
    (inferInstance : Module.Finite k V)).span
  have hAN (a : A) : i a ∈ N := by
    have h := N.smul_mem a (Submodule.subset_span h1)
    change (a : H) * 1 ∈ N at h
    change (a : H) ∈ N
    simpa only [mul_one] using h
  let j : A →ₗ[A] N := (Algebra.linearMap A H).codRestrict N hAN
  let v : N →ₗ[k] H := N.subtype.restrictScalars k
  have hv : Function.Injective v := Subtype.val_injective
  let t : N ⊗[k] H →ₗ[k] H ⊗[k] H := v.rTensor H
  have htN : Function.Injective t :=
    Module.Flat.rTensor_preserves_injective_linearMap v hv
  -- The comultiplication of a scalar acts on the restricted tensor product.
  have hact (a : A) (z : N ⊗[k] H) :
      let d := Coalgebra.Repr.arbitrary k a
      t (∑ b ∈ d.index, TensorProduct.map ((Algebra.lsmul k k N) (d.left b))
        (LinearMap.mulLeft k (ι (d.right b))) z) =
        Coalgebra.comul (R := k) (i a) * t z := by
    dsimp only
    let d := Coalgebra.Repr.arbitrary k a
    have hd : Coalgebra.comul (R := k) (i a) =
        ∑ b ∈ d.index, i (d.left b) ⊗ₜ[k] i (d.right b) := by
      rw [← hδ]
      change TensorProduct.map i i (Coalgebra.comul (R := k) a) = _
      rw [← d.eq]
      simp only [map_sum, TensorProduct.map_tmul]
    induction z using TensorProduct.induction_on with
    | zero => simp [t]
    | tmul n h =>
      rw [hd, Finset.sum_mul]
      simp only [map_sum]
      apply Finset.sum_congr rfl
      intro b hb
      change (↑((d.left b) • n) : H) ⊗ₜ[k] (i (d.right b) * h) =
        (i (d.left b) ⊗ₜ[k] i (d.right b)) * ((n : H) ⊗ₜ[k] h)
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      rfl
    | add x y hx hy =>
      simp only [map_add, Finset.sum_add_distrib, hx, hy, mul_add]
  have hN (n : H) (hn : n ∈ N) : Coalgebra.comul (R := k) n ∈ LinearMap.range t := by
    induction hn using Submodule.span_induction with
    | mem x hx =>
      have hz := hV x hx
      generalize Coalgebra.comul (R := k) x = z at hz ⊢
      induction hz using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨a, ha, b, rfl⟩ := hz
        exact ⟨(⟨a, Submodule.subset_span ha⟩ : N) ⊗ₜ[k] b, rfl⟩
      | zero => exact (LinearMap.range t).zero_mem
      | add x y _ _ hx hy => exact (LinearMap.range t).add_mem hx hy
      | smul c x _ hx => exact (LinearMap.range t).smul_mem c hx
    | zero => simp
    | add x y _ _ hx hy => simpa only [map_add] using (LinearMap.range t).add_mem hx hy
    | smul a x _ hx =>
      obtain ⟨z, hz⟩ := hx
      refine ⟨∑ b ∈ (Coalgebra.Repr.arbitrary k a).index,
        TensorProduct.map ((Algebra.lsmul k k N) ((Coalgebra.Repr.arbitrary k a).left b))
          (LinearMap.mulLeft k (ι ((Coalgebra.Repr.arbitrary k a).right b))) z, ?_⟩
      rw [hact, hz]
      exact (Bialgebra.comul_mul (i a) x).symm
  obtain ⟨pN, hpN⟩ := v.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hv)
  let μN : N →ₗ[k] N ⊗[k] H :=
    (pN.rTensor H).comp ((Coalgebra.comul (R := k)).comp v)
  have hμN (n : N) : t (μN n) = Coalgebra.comul (R := k) (v n) := by
    obtain ⟨z, hz⟩ := hN (v n) n.property
    change t (pN.rTensor H (Coalgebra.comul (R := k) (v n))) = _
    rw [← hz]
    have he : (pN.rTensor H).comp t = LinearMap.id := by
      dsimp only [t]
      rw [← LinearMap.rTensor_comp, hpN, LinearMap.rTensor_id]
    exact congrArg t (LinearMap.congr_fun he z)
  have hμmap : t.comp μN = (Coalgebra.comul (R := k)).comp v := LinearMap.ext hμN
  have hNcoassoc (n : N) :
      TensorProduct.assoc k N H H (TensorProduct.map μN LinearMap.id (μN n)) =
        TensorProduct.map LinearMap.id (Coalgebra.comul (R := k)) (μN n) := by
    apply TensorProduct.map_injective_of_flat_flat v (LinearMap.id : H ⊗[k] H →ₗ[k] _)
      hv Function.injective_id
    rw [← TensorProduct.map_id (R := k) (M := H) (N := H), TensorProduct.map_map_assoc]
    simp only [TensorProduct.map_map, LinearMap.comp_id, LinearMap.id_comp,
      TensorProduct.map_id]
    change TensorProduct.assoc k H H H (TensorProduct.map (t.comp μN) LinearMap.id (μN n)) = _
    rw [hμmap]
    have he : TensorProduct.map ((Coalgebra.comul (R := k)).comp v)
        (LinearMap.id : H →ₗ[k] H) =
        (TensorProduct.map (Coalgebra.comul (R := k)) LinearMap.id).comp t := by
      ext n h
      rfl
    have he' : TensorProduct.map v (Coalgebra.comul (R := k)) =
        (TensorProduct.map LinearMap.id (Coalgebra.comul (R := k))).comp t := by
      ext n h
      rfl
    rw [he, he']
    simp only [LinearMap.comp_apply, hμN]
    exact Coalgebra.coassoc_apply (R := k) (v n)
  have hNcounit (n : N) :
      TensorProduct.rid k N (TensorProduct.map LinearMap.id (Coalgebra.counit (R := k))
        (μN n)) = n := by
    apply hv
    have he : v.comp ((TensorProduct.rid k N).toLinearMap.comp
        (TensorProduct.map LinearMap.id (Coalgebra.counit (R := k)))) =
        ((TensorProduct.rid k H).toLinearMap.comp
          (TensorProduct.map LinearMap.id (Coalgebra.counit (R := k)))).comp t := by
      ext n h
      simp [t]
    calc
      _ = TensorProduct.rid k H
          (TensorProduct.map LinearMap.id (Coalgebra.counit (R := k)) (t (μN n))) :=
        LinearMap.congr_fun he _
      _ = v n := by
        rw [hμN]
        simpa only [LinearMap.lTensor, TensorProduct.rid_tmul, one_smul] using
          congrArg (TensorProduct.rid k H) (Coalgebra.lTensor_counit_comul (v n))
  have hNcompat (a : A) (n : N) :
      let d := Coalgebra.Repr.arbitrary k a
      μN (a • n) = ∑ b ∈ d.index,
        TensorProduct.map ((Algebra.lsmul k k N) (d.left b))
          (LinearMap.mulLeft k (ι (d.right b))) (μN n) := by
    apply htN
    rw [hμN, hact, hμN]
    exact Bialgebra.comul_mul (i a) (v n)
  -- The image of A is a subcomodule, so the coaction descends to N/A.
  let L : Submodule A N := LinearMap.range j
  let Q := N ⧸ L
  let q : N →ₗ[k] Q := L.mkQ.restrictScalars k
  have hq : Function.Surjective q := L.mkQ_surjective
  have hμj (a : A) : μN (j a) =
      TensorProduct.map (j.restrictScalars k) i (Coalgebra.comul (R := k) a) := by
    apply htN
    rw [hμN]
    change Coalgebra.comul (R := k) (i a) =
      TensorProduct.map v LinearMap.id
        (TensorProduct.map (j.restrictScalars k) i (δ a))
    rw [TensorProduct.map_map]
    change Coalgebra.comul (R := k) (i a) = TensorProduct.map i i (δ a)
    exact (hδ a).symm
  have hqj (a : A) : q (j a) = 0 :=
    (Submodule.Quotient.mk_eq_zero L).mpr ⟨a, rfl⟩
  have hkill : L.restrictScalars k ≤ LinearMap.ker ((q.rTensor H).comp μN) := by
    rintro _ ⟨a, rfl⟩
    change q.rTensor H (μN (j a)) = 0
    rw [hμj]
    have he : (q.rTensor H).comp (TensorProduct.map (j.restrictScalars k) i) = 0 := by
      ext a h
      simp [hqj]
    exact LinearMap.congr_fun he _
  let μ : Q →ₗ[k] Q ⊗[k] H :=
    ((L.restrictScalars k).liftQ ((q.rTensor H).comp μN) hkill).comp
      (Submodule.Quotient.restrictScalarsEquiv k L).symm.toLinearMap
  have hμq (n : N) : μ (q n) = q.rTensor H (μN n) := rfl
  have hQcoassoc (m : Q) :
      TensorProduct.assoc k Q H H (TensorProduct.map μ LinearMap.id (μ m)) =
        TensorProduct.map LinearMap.id (Coalgebra.comul (R := k)) (μ m) := by
    obtain ⟨n, rfl⟩ := hq m
    rw [hμq]
    have he : (TensorProduct.map μ (LinearMap.id : H →ₗ[k] H)).comp (q.rTensor H) =
        (TensorProduct.map (q.rTensor H) LinearMap.id).comp
          (TensorProduct.map μN LinearMap.id) := by
      apply TensorProduct.ext'
      intro n h
      rfl
    rw [← LinearMap.comp_apply, he, LinearMap.comp_apply]
    change TensorProduct.assoc k Q H H
      (TensorProduct.map (TensorProduct.map q LinearMap.id) LinearMap.id
        (TensorProduct.map μN LinearMap.id (μN n))) = _
    rw [← TensorProduct.map_map_assoc]
    simp only [TensorProduct.map_id]
    rw [hNcoassoc]
    have he' : (TensorProduct.map q (LinearMap.id : H ⊗[k] H →ₗ[k] _)).comp
        (TensorProduct.map LinearMap.id (Coalgebra.comul (R := k))) =
        (TensorProduct.map LinearMap.id (Coalgebra.comul (R := k))).comp (q.rTensor H) := by
      ext n h
      rfl
    exact LinearMap.congr_fun he' (μN n)
  have hQcounit (m : Q) :
      TensorProduct.rid k Q (TensorProduct.map LinearMap.id (Coalgebra.counit (R := k))
        (μ m)) = m := by
    obtain ⟨n, rfl⟩ := hq m
    rw [hμq]
    have he : ((TensorProduct.rid k Q).toLinearMap.comp
        (TensorProduct.map LinearMap.id (Coalgebra.counit (R := k)))).comp (q.rTensor H) =
        q.comp ((TensorProduct.rid k N).toLinearMap.comp
          (TensorProduct.map LinearMap.id (Coalgebra.counit (R := k)))) := by
      ext n h
      simp
    calc
      _ = q (TensorProduct.rid k N
          (TensorProduct.map LinearMap.id (Coalgebra.counit (R := k)) (μN n))) :=
        LinearMap.congr_fun he _
      _ = q n := congrArg q (hNcounit n)
  have hQcompat (a : A) (m : Q) :
      let d := Coalgebra.Repr.arbitrary k a
      μ (a • m) = ∑ b ∈ d.index,
        TensorProduct.map ((Algebra.lsmul k k Q) (d.left b))
          (LinearMap.mulLeft k (ι (d.right b))) (μ m) := by
    obtain ⟨n, rfl⟩ := hq m
    change μ (q (a • n)) = _
    rw [hμq, hNcompat]
    simp only [map_sum, hμq]
    apply Finset.sum_congr rfl
    intro b hb
    have he : (q.rTensor H).comp
        (TensorProduct.map ((Algebra.lsmul k k N) ((Coalgebra.Repr.arbitrary k a).left b))
          (LinearMap.mulLeft k (ι ((Coalgebra.Repr.arbitrary k a).right b)))) =
        (TensorProduct.map ((Algebra.lsmul k k Q) ((Coalgebra.Repr.arbitrary k a).left b))
          (LinearMap.mulLeft k (ι ((Coalgebra.Repr.arbitrary k a).right b)))).comp
            (q.rTensor H) := by
      apply TensorProduct.ext'
      intro n h
      change L.mkQ ((Coalgebra.Repr.arbitrary k a).left b • n) ⊗ₜ[k] _ =
        ((Coalgebra.Repr.arbitrary k a).left b • L.mkQ n) ⊗ₜ[k] _
      rw [map_smul]
      rfl
    exact LinearMap.congr_fun he (μN n)
  -- Apply the supplied projectivity interface, then split the quotient (proof step 14).
  let : Module.Projective A Q :=
    p05_fr_finite_relative_hopf_module_projective_a5b449214a ι hi μ
      hQcoassoc hQcounit hQcompat
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property L.mkQ
    (LinearMap.id : Q →ₗ[A] Q) L.mkQ_surjective
  let e := LinearEquiv.ofInjective j (fun a b hab => hi (congrArg v hab))
  let rL : N →ₗ[A] L := (LinearMap.id - σ.comp L.mkQ).codRestrict L (by
    intro n
    apply (Submodule.Quotient.mk_eq_zero L).mp
    change L.mkQ (n - σ (L.mkQ n)) = 0
    rw [map_sub, show L.mkQ (σ (L.mkQ n)) = L.mkQ n from LinearMap.congr_fun hσ _, sub_self])
  refine ⟨e.symm.toLinearMap.comp rL, ?_⟩
  intro a ha
  apply e.injective
  simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, LinearEquiv.apply_symm_apply]
  apply Subtype.ext
  change (⟨(a : H), ha⟩ : N) - σ (L.mkQ ⟨(a : H), ha⟩) = j a
  have hzero : L.mkQ (⟨(a : H), ha⟩ : N) = 0 := hqj a
  rw [hzero, map_zero, sub_zero]
  rfl

end Submission
    exact Bialgebra.comul_mul
        simpa only [TensorProduct.map_tmul, LinearMap.id_apply] using
          Coalgebra.lTensor_counit_comul (R := k) (i v)
theorem Submission.p05_hte_sshs_antipode_lift_a5b449214a
    {k : Type*} [Field k] {A : Type*} [CommRing A] [bA : Bialgebra k A]
    {H : Type*} [CommRing H] [HopfAlgebra k H]
    (ι : BialgHom k A H) (hι : Function.Injective ι)
    (hS : ∀ a : A, ∃ b : A, ι b = HopfAlgebra.antipode k (ι a)) :
    ∃ hA : HopfAlgebra k A, hA.toHopfAlgebraStruct.toBialgebra = bA ∧
      (letI : Algebra k A := hA.toHopfAlgebraStruct.toBialgebra.toAlgebra
       letI : Module k A := Algebra.toModule
       letI : Bialgebra k A := hA.toHopfAlgebraStruct.toBialgebra
       letI : HopfAlgebra k A := hA
       ∀ a : A, ι (HopfAlgebra.antipode k a) = HopfAlgebra.antipode k (ι a)) := by
  classical
  let S : A → A := fun a => Classical.choose (hS a)
  have hSι (a : A) : ι (S a) = HopfAlgebra.antipode k (ι a) :=
    Classical.choose_spec (hS a)
  let s : A →ₗ[k] A :=
    { toFun := S
      map_add' := fun a b => hι (by simp only [hSι, map_add])
      map_smul' := fun c a => hι (by simp only [hSι, map_smul, RingHom.id_apply]) }
  have hs (a : A) : ι (s a) = HopfAlgebra.antipode k (ι a) := hSι a
  have hr :
      (ι : A →ₗ[k] H) ∘ₗ (LinearMap.mul' k A ∘ₗ s.rTensor A) =
        (LinearMap.mul' k H ∘ₗ (HopfAlgebra.antipode k).rTensor H) ∘ₗ
          TensorProduct.map (ι : A →ₗ[k] H) (ι : A →ₗ[k] H) := by
    apply TensorProduct.ext'
    intro a b
    simp [hs]
  have hl :
      (ι : A →ₗ[k] H) ∘ₗ (LinearMap.mul' k A ∘ₗ s.lTensor A) =
        (LinearMap.mul' k H ∘ₗ (HopfAlgebra.antipode k).lTensor H) ∘ₗ
          TensorProduct.map (ι : A →ₗ[k] H) (ι : A →ₗ[k] H) := by
    apply TensorProduct.ext'
    intro a b
    simp [hs]
  have hleft :
      LinearMap.mul' k A ∘ₗ s.rTensor A ∘ₗ Coalgebra.comul =
        Algebra.linearMap k A ∘ₗ Coalgebra.counit := by
    ext a
    apply hι
    change ι (LinearMap.mul' k A (s.rTensor A (Coalgebra.comul a))) =
      ι (algebraMap k A (Coalgebra.counit a))
    calc
      _ = LinearMap.mul' k H ((HopfAlgebra.antipode k).rTensor H
          (TensorProduct.map (ι : A →ₗ[k] H) (ι : A →ₗ[k] H)
            (Coalgebra.comul a))) := LinearMap.congr_fun hr _
      _ = algebraMap k H (Coalgebra.counit (ι a)) := by
        rw [CoalgHomClass.map_comp_comul_apply]
        exact HopfAlgebra.mul_antipode_rTensor_comul_apply (ι a)
      _ = _ := by simp only [CoalgHomClass.counit_comp_apply, AlgHomClass.commutes]
  have hright :
      LinearMap.mul' k A ∘ₗ s.lTensor A ∘ₗ Coalgebra.comul =
        Algebra.linearMap k A ∘ₗ Coalgebra.counit := by
    ext a
    apply hι
    change ι (LinearMap.mul' k A (s.lTensor A (Coalgebra.comul a))) =
      ι (algebraMap k A (Coalgebra.counit a))
    calc
      _ = LinearMap.mul' k H ((HopfAlgebra.antipode k).lTensor H
          (TensorProduct.map (ι : A →ₗ[k] H) (ι : A →ₗ[k] H)
            (Coalgebra.comul a))) := LinearMap.congr_fun hl _
      _ = algebraMap k H (Coalgebra.counit (ι a)) := by
        rw [CoalgHomClass.map_comp_comul_apply]
        exact HopfAlgebra.mul_antipode_lTensor_comul_apply (ι a)
      _ = _ := by simp only [CoalgHomClass.counit_comp_apply, AlgHomClass.commutes]
  let hA : HopfAlgebra k A :=
    { toBialgebra := bA
      antipode := s
      mul_antipode_rTensor_comul := hleft
      mul_antipode_lTensor_comul := hright }
  exact ⟨hA, rfl, hs⟩


namespace Submission

/-- A subalgebra stable under comultiplication and antipode inherits a compatible Hopf structure. -/
theorem p05_hte_stable_subalgebra_hopf_structure_a5b449214a
    {k : Type*} [Field k] {H : Type*} [CommRing H] [HopfAlgebra k H]
    (D : Subalgebra k H)
    (hΔ : ∀ x ∈ D, Coalgebra.comul (R := k) x ∈
      Submodule.span k {t : TensorProduct k H H |
        ∃ a ∈ D, ∃ b ∈ D, t = TensorProduct.tmul k a b})
    (hS : ∀ x ∈ D, HopfAlgebra.antipode k x ∈ D) :
    ∃ hD : HopfAlgebra k D,
      hD.toHopfAlgebraStruct.toBialgebra.toAlgebra = (inferInstance : Algebra k D) ∧
      (letI : Algebra k D := hD.toHopfAlgebraStruct.toBialgebra.toAlgebra;
       letI : Module k D := Algebra.toModule;
       letI : HopfAlgebra k D := hD;
       ∃ ι : BialgHom k D H, (∀ d : D, ι d = (d : H)) ∧
         ∀ d : D, ((HopfAlgebra.antipode k d : D) : H) =
           HopfAlgebra.antipode k (d : H)) := by
  obtain ⟨bD, hAlg, hInclusion⟩ :=
    p05_hte_sshs_bialgebra_restriction_a5b449214a D hΔ
  let : Algebra k D := bD.toAlgebra
  let : Module k D := Algebra.toModule
  let : Bialgebra k D := bD
  obtain ⟨ι, hι⟩ := hInclusion
  have hInjective : Function.Injective ι := by
    intro a b hab
    apply Subtype.val_injective
    exact (hι a).symm.trans (hab.trans (hι b))
  have hStable : ∀ a : D, ∃ b : D, ι b = HopfAlgebra.antipode k (ι a) := by
    intro a
    refine ⟨⟨HopfAlgebra.antipode k (a : H), hS a a.property⟩, ?_⟩
    rw [hι, hι]
  obtain ⟨hD, hbD, hAntipode⟩ :=
    p05_hte_sshs_antipode_lift_a5b449214a ι hInjective hStable
  change hD.toHopfAlgebraStruct.toBialgebra = bD at hbD
  subst bD
  refine ⟨hD, hAlg, ?_⟩
  let : HopfAlgebra k D := hD
  refine ⟨ι, hι, ?_⟩
  intro d
  simpa only [hι] using hAntipode d

end Submission
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
theorem Submission.p05_ftzw_tensor_relation_kernel_a5b449214a :
    ∀ {D : Type*} [CommRing D] {M : Type*} [AddCommGroup M] [Module D M]
      {P : Type*} [AddCommGroup P] [Module D P],
      let b : M → P → FreeAbelianGroup (M × P) := fun u z => FreeAbelianGroup.of (u, z)
      (FreeAbelianGroup.lift (fun x : M × P => TensorProduct.tmul D x.1 x.2)).ker =
        AddSubgroup.closure {r : FreeAbelianGroup (M × P) |
          (∃ z : P, r = b 0 z) ∨ (∃ u : M, r = b u 0) ∨
          (∃ (u v : M) (z : P), r = b (u + v) z - b u z - b v z) ∨
          (∃ (u : M) (z w : P), r = b u (z + w) - b u z - b u w) ∨
          (∃ (d : D) (u : M) (z : P), r = b (d • u) z - b u (d • z))} := by
  intro D _ M _ _ P _ _
  let b : M → P → FreeAbelianGroup (M × P) := fun u z => FreeAbelianGroup.of (u, z)
  let T : Set (FreeAbelianGroup (M × P)) := {r |
    (∃ z : P, r = b 0 z) ∨ (∃ u : M, r = b u 0) ∨
    (∃ (u v : M) (z : P), r = b (u + v) z - b u z - b v z) ∨
    (∃ (u : M) (z w : P), r = b u (z + w) - b u z - b u w) ∨
    (∃ (d : D) (u : M) (z : P), r = b (d • u) z - b u (d • z))}
  let R := AddSubgroup.closure T
  let E := FreeAbelianGroup.lift (fun x : M × P => TensorProduct.tmul D x.1 x.2)
  change E.ker = R
  have hRE : R ≤ E.ker := by
    apply (AddSubgroup.closure_le _).mpr
    intro r hr
    change E r = 0
    rcases hr with ⟨z, rfl⟩ | ⟨u, rfl⟩ | ⟨u, v, z, rfl⟩ |
      ⟨u, z, w, rfl⟩ | ⟨d, u, z, rfl⟩
    · simp [E, b]
    · simp [E, b]
    · simp [E, b, TensorProduct.add_tmul]
    · simp [E, b, TensorProduct.tmul_add]
    · simp [E, b, TensorProduct.smul_tmul]
  let π := QuotientAddGroup.mk' R
  have hrel {r : FreeAbelianGroup (M × P)} (hr : r ∈ T) : π r = 0 :=
    (QuotientAddGroup.eq_zero_iff r).mpr (AddSubgroup.subset_closure hr)
  have hzero_left (z : P) : π (b 0 z) = 0 :=
    hrel (Or.inl ⟨z, rfl⟩)
  have hzero_right (u : M) : π (b u 0) = 0 :=
    hrel (Or.inr (Or.inl ⟨u, rfl⟩))
  have hadd_left (u v : M) (z : P) :
      π (b (u + v) z) = π (b u z) + π (b v z) := by
    have h := hrel (Or.inr (Or.inr (Or.inl ⟨u, v, z, rfl⟩)))
    simpa only [map_sub, map_add, sub_sub, sub_eq_zero] using h
  have hadd_right (u : M) (z w : P) :
      π (b u (z + w)) = π (b u z) + π (b u w) := by
    have h := hrel (Or.inr (Or.inr (Or.inr (Or.inl ⟨u, z, w, rfl⟩))))
    simpa only [map_sub, map_add, sub_sub, sub_eq_zero] using h
  have hbalance (d : D) (u : M) (z : P) :
      π (b (d • u) z) = π (b u (d • z)) := by
    have h := hrel (Or.inr (Or.inr (Or.inr (Or.inr ⟨d, u, z, rfl⟩))))
    simpa only [map_sub, sub_eq_zero] using h
  let β : M →+ P →+ FreeAbelianGroup (M × P) ⧸ R :=
    { toFun := fun u =>
        { toFun := fun z => π (b u z)
          map_zero' := hzero_right u
          map_add' := hadd_right u }
      map_zero' := by
        ext z
        exact hzero_left z
      map_add' := by
        intro u v
        ext z
        exact hadd_left u v z }
  let L : M ⊗[D] P →+ FreeAbelianGroup (M × P) ⧸ R :=
    TensorProduct.liftAddHom β hbalance
  have hcomp : L.comp E = π := by
    apply FreeAbelianGroup.lift_ext
    intro x
    rcases x with ⟨u, z⟩
    simp [E, L, β, b]
  apply le_antisymm _ hRE
  intro g hg
  apply (QuotientAddGroup.eq_zero_iff g).mp
  change π g = 0
  rw [← hcomp]
  change L (E g) = 0
  rw [show E g = 0 from hg, map_zero]
theorem Submission.p05_ftzw_supported_relations_vanish_a5b449214a :
    ∀ {k : Type*} [CommRing k] {D : Type*} [CommRing D] [Algebra k D] {M : Type*} [AddCommGroup M] [Module D M] {P : Type*} [AddCommGroup P] [Module D P] (A : Subalgebra k D) (N : Submodule A M) (m : N) (p : P), let b : M → P → FreeAbelianGroup (M × P) := fun u z => FreeAbelianGroup.of (u, z); b (m : M) p ∈ AddSubgroup.closure {r : FreeAbelianGroup (M × P) | (∃ z : P, r = b 0 z) ∨ (∃ u : M, u ∈ N ∧ r = b u 0) ∨ (∃ (u v : M) (z : P), u ∈ N ∧ v ∈ N ∧ r = b (u + v) z - b u z - b v z) ∨ (∃ (u : M) (z w : P), u ∈ N ∧ r = b u (z + w) - b u z - b u w) ∨ (∃ (d : D) (u : M) (z : P), d ∈ A ∧ u ∈ N ∧ r = b (d • u) z - b u (d • z))} → (TensorProduct.tmul A m p : TensorProduct A N P) = 0 := by
  classical
  intro k _ D _ _ M _ _ P _ _ A N m p
  dsimp only
  intro h
  let bN : N → P → FreeAbelianGroup (N × P) :=
    fun n z => FreeAbelianGroup.of (n, z)
  let J : FreeAbelianGroup (N × P) →+ FreeAbelianGroup (M × P) :=
    FreeAbelianGroup.lift fun t : N × P => FreeAbelianGroup.of ((t.1 : M), t.2)
  let E : FreeAbelianGroup (N × P) →+ TensorProduct A N P :=
    FreeAbelianGroup.lift fun t : N × P => TensorProduct.tmul A t.1 t.2
  have hcoeff (t : N × P) :
      (FreeAbelianGroup.coeff ((t.1 : M), t.2)).comp J = FreeAbelianGroup.coeff t := by
    rcases t with ⟨n', z'⟩
    apply FreeAbelianGroup.lift_ext
    rintro ⟨n, z⟩
    change (J (FreeAbelianGroup.of (n, z))).toFinsupp ((n' : M), z') =
      (FreeAbelianGroup.of (n, z)).toFinsupp (n', z')
    rw [show J (FreeAbelianGroup.of (n, z)) =
      FreeAbelianGroup.of ((n : M), z) from FreeAbelianGroup.lift_apply_of _ _,
      FreeAbelianGroup.toFinsupp_of, FreeAbelianGroup.toFinsupp_of]
    simp only [Finsupp.single_apply, Prod.mk.injEq, Subtype.ext_iff]
  have hJ : Function.Injective J := by
    intro x y hxy
    apply (FreeAbelianGroup.equivFinsupp (N × P)).injective
    ext t
    change FreeAbelianGroup.coeff t x = FreeAbelianGroup.coeff t y
    rw [← hcoeff t]
    exact congrArg (FreeAbelianGroup.coeff ((t.1 : M), t.2)) hxy
  have hmem : FreeAbelianGroup.of ((m : M), p) ∈ E.ker.map J := by
    apply ((AddSubgroup.closure_le _).mpr ?_) h
    intro r hr
    rcases hr with ⟨z, rfl⟩ | ⟨u, hu, rfl⟩ | ⟨u, v, z, hu, hv, rfl⟩ |
      ⟨u, z, w, hu, rfl⟩ | ⟨d, u, z, hd, hu, rfl⟩
    · refine ⟨bN 0 z, ?_, ?_⟩
      · change E (bN 0 z) = 0
        simp [E, bN]
      · simp [J, bN]
    · refine ⟨bN ⟨u, hu⟩ 0, ?_, ?_⟩
      · change E (bN ⟨u, hu⟩ 0) = 0
        simp [E, bN]
      · simp [J, bN]
    · refine ⟨bN (⟨u, hu⟩ + ⟨v, hv⟩) z - bN ⟨u, hu⟩ z - bN ⟨v, hv⟩ z,
        ?_, ?_⟩
      · change E _ = 0
        simp only [map_sub, E, bN, FreeAbelianGroup.lift_apply_of, TensorProduct.add_tmul]
        abel
      · simp [J, bN]
    · refine ⟨bN ⟨u, hu⟩ (z + w) - bN ⟨u, hu⟩ z - bN ⟨u, hu⟩ w, ?_, ?_⟩
      · change E _ = 0
        simp only [map_sub, E, bN, FreeAbelianGroup.lift_apply_of, TensorProduct.tmul_add]
        abel
      · simp [J, bN]
    · refine ⟨bN ((⟨d, hd⟩ : A) • (⟨u, hu⟩ : N)) z -
        bN ⟨u, hu⟩ ((⟨d, hd⟩ : A) • z), ?_, ?_⟩
      · change E _ = 0
        simp only [map_sub, E, bN, FreeAbelianGroup.lift_apply_of,
          TensorProduct.smul_tmul, sub_self]
      · simp only [map_sub, J, bN, FreeAbelianGroup.lift_apply_of]
        rfl
  have hNm : bN m p ∈ E.ker :=
    (AddSubgroup.mem_map_iff_mem hJ).mp hmem
  change E (bN m p) = 0 at hNm
  simpa only [E, bN, FreeAbelianGroup.lift_apply_of] using hNm


namespace Submission

theorem p05_hte_finite_tensor_zero_witness_a5b449214a
    {k : Type*} [CommRing k] {D : Type*} [CommRing D] [Algebra k D]
    {M : Type*} [AddCommGroup M] [Module D M]
    {P : Type*} [AddCommGroup P] [Module D P] (m : M) (p : P)
    (hmp : (TensorProduct.tmul D m p : TensorProduct D M P) = 0) :
    ∃ S : Finset D, ∃ F : Finset M, m ∈ F ∧
      ∀ (A : Subalgebra k D), (∀ d ∈ S, d ∈ A) →
      ∀ (N : Submodule A M), (∀ y ∈ F, y ∈ N) →
      ∀ hm : m ∈ N,
        (TensorProduct.tmul A (⟨m, hm⟩ : N) p : TensorProduct A N P) = 0 := by
  classical
  let b : M → P → FreeAbelianGroup (M × P) := fun u z => FreeAbelianGroup.of (u, z)
  let R : Set (FreeAbelianGroup (M × P)) :=
    {r | (∃ z : P, r = b 0 z) ∨
      (∃ u : M, r = b u 0) ∨
      (∃ (u v : M) (z : P), r = b (u + v) z - b u z - b v z) ∨
      (∃ (u : M) (z w : P), r = b u (z + w) - b u z - b u w) ∨
      (∃ (d : D) (u : M) (z : P), r = b (d • u) z - b u (d • z))}
  let supported (A : Subalgebra k D) (N : Submodule A M) :
      Set (FreeAbelianGroup (M × P)) :=
    {r | (∃ z : P, r = b 0 z) ∨
      (∃ u : M, u ∈ N ∧ r = b u 0) ∨
      (∃ (u v : M) (z : P), u ∈ N ∧ v ∈ N ∧
        r = b (u + v) z - b u z - b v z) ∨
      (∃ (u : M) (z w : P), u ∈ N ∧
        r = b u (z + w) - b u z - b u w) ∨
      (∃ (d : D) (u : M) (z : P), d ∈ A ∧ u ∈ N ∧
        r = b (d • u) z - b u (d • z))}
  have hrel : b m p ∈ AddSubgroup.closure R := by
    rw [← p05_ftzw_tensor_relation_kernel_a5b449214a (D := D) (M := M) (P := P)]
    change FreeAbelianGroup.lift (fun x : M × P => TensorProduct.tmul D x.1 x.2)
      (FreeAbelianGroup.of (m, p)) = 0
    simpa only [FreeAbelianGroup.lift_apply_of] using hmp
  -- Closure induction collects finite supports for the formal relation identity.
  have finite_support : ∀ r ∈ AddSubgroup.closure R,
      ∃ S : Finset D, ∃ F : Finset M,
        ∀ (A : Subalgebra k D), (∀ d ∈ S, d ∈ A) →
        ∀ (N : Submodule A M), (∀ y ∈ F, y ∈ N) →
          r ∈ AddSubgroup.closure (supported A N) := by
    intro r hr
    induction hr using AddSubgroup.closure_induction with
    | mem r hr =>
      rcases hr with ⟨z, rfl⟩ | ⟨u, rfl⟩ | ⟨u, v, z, rfl⟩ |
        ⟨u, z, w, rfl⟩ | ⟨d, u, z, rfl⟩
      · refine ⟨∅, {0}, ?_⟩
        intro A _ N _
        exact AddSubgroup.subset_closure (Or.inl ⟨z, rfl⟩)
      · refine ⟨∅, {u}, ?_⟩
        intro A _ N hN
        exact AddSubgroup.subset_closure (Or.inr (Or.inl ⟨u, hN u (by simp), rfl⟩))
      · refine ⟨∅, {u, v, u + v}, ?_⟩
        intro A _ N hN
        exact AddSubgroup.subset_closure
          (Or.inr (Or.inr (Or.inl ⟨u, v, z, hN u (by simp), hN v (by simp), rfl⟩)))
      · refine ⟨∅, {u}, ?_⟩
        intro A _ N hN
        exact AddSubgroup.subset_closure
          (Or.inr (Or.inr (Or.inr (Or.inl ⟨u, z, w, hN u (by simp), rfl⟩))))
      · refine ⟨{d}, {u, d • u}, ?_⟩
        intro A hA N hN
        exact AddSubgroup.subset_closure
          (Or.inr (Or.inr (Or.inr (Or.inr
            ⟨d, u, z, hA d (by simp), hN u (by simp), rfl⟩))))
    | zero =>
      exact ⟨∅, ∅, fun A _ N _ => (AddSubgroup.closure (supported A N)).zero_mem⟩
    | add r s _ _ ihr ihs =>
      obtain ⟨Sr, Fr, hr⟩ := ihr
      obtain ⟨Ss, Fs, hs⟩ := ihs
      refine ⟨Sr ∪ Ss, Fr ∪ Fs, ?_⟩
      intro A hA N hN
      exact (AddSubgroup.closure (supported A N)).add_mem
        (hr A (fun d hd => hA d (Finset.mem_union_left Ss hd))
          N (fun y hy => hN y (Finset.mem_union_left Fs hy)))
        (hs A (fun d hd => hA d (Finset.mem_union_right Sr hd))
          N (fun y hy => hN y (Finset.mem_union_right Fr hy)))
    | neg r _ ihr =>
      obtain ⟨S, F, h⟩ := ihr
      exact ⟨S, F, fun A hA N hN =>
        (AddSubgroup.closure (supported A N)).neg_mem (h A hA N hN)⟩
  obtain ⟨S, F, hSF⟩ := finite_support (b m p) hrel
  refine ⟨S, insert m F, Finset.mem_insert_self m F, ?_⟩
  intro A hA N hN hm
  apply p05_ftzw_supported_relations_vanish_a5b449214a A N ⟨m, hm⟩ p
  exact hSF A hA N (fun y hy => hN y (Finset.mem_insert_of_mem hy))

end Submission
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
theorem Submission.p05_umgi_minor_reconstruction_a5b449214a
    {R : Type*} [CommRing R] (n p d : ℕ) (P : Matrix (Fin n) (Fin p) R)
    (rows : Fin d ↪ Fin n) (cols : Fin d ↪ Fin p)
    (_hunit : IsUnit (Matrix.det (P.submatrix rows cols)))
    (_hnext : ∀ (rows' : Fin (d + 1) ↪ Fin n) (cols' : Fin (d + 1) ↪ Fin p),
      Matrix.det (P.submatrix rows' cols') = 0) :
    P = (P.submatrix id cols) * (P.submatrix rows cols)⁻¹ * (P.submatrix rows id) := by
  classical
  let B := P.submatrix rows cols
  let L := P.submatrix id cols
  let H := P.submatrix rows id
  ext i j
  by_cases hi : i ∈ Set.range rows
  · obtain ⟨a, rfl⟩ := hi
    change P (rows a) j = (B * B⁻¹ * H) a j
    rw [Matrix.mul_nonsing_inv B _hunit, Matrix.one_mul]
    rfl
  by_cases hj : j ∈ Set.range cols
  · obtain ⟨b, rfl⟩ := hj
    change P i (cols b) = (L * B⁻¹ * B) i b
    rw [Matrix.nonsing_inv_mul_cancel_right B L _hunit]
    rfl
  let er : Fin d ⊕ Fin 1 ↪ Fin n :=
    { toFun := Sum.elim rows (fun _ => i)
      inj' := by
        intro a b hab
        rcases a with a | a <;> rcases b with b | b
        · exact congrArg Sum.inl (rows.injective hab)
        · exact (hi ⟨a, hab⟩).elim
        · exact (hi ⟨b, hab.symm⟩).elim
        · exact congrArg Sum.inr (Subsingleton.elim _ _) }
  let ec : Fin d ⊕ Fin 1 ↪ Fin p :=
    { toFun := Sum.elim cols (fun _ => j)
      inj' := by
        intro a b hab
        rcases a with a | a <;> rcases b with b | b
        · exact congrArg Sum.inl (cols.injective hab)
        · exact (hj ⟨a, hab⟩).elim
        · exact (hj ⟨b, hab.symm⟩).elim
        · exact congrArg Sum.inr (Subsingleton.elim _ _) }
  let e : Fin d ⊕ Fin 1 ≃ Fin (d + 1) := finSumFinEquiv
  have hz : Matrix.det (P.submatrix er ec) = 0 := by
    rw [← Matrix.det_submatrix_equiv_self e.symm (P.submatrix er ec)]
    exact _hnext (e.symm.toEmbedding.trans er) (e.symm.toEmbedding.trans ec)
  let c : Matrix (Fin d) (Fin 1) R := fun a _ => P (rows a) j
  let r : Matrix (Fin 1) (Fin d) R := fun _ b => P i (cols b)
  let z : Matrix (Fin 1) (Fin 1) R := fun _ _ => P i j
  have hblock : P.submatrix er ec = Matrix.fromBlocks B c r z := by
    ext a b
    cases a <;> cases b <;> rfl
  let : Invertible B := Matrix.invertibleOfIsUnitDet B _hunit
  rw [hblock, Matrix.det_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv] at hz
  have hcorner := _hunit.mul_right_eq_zero.mp hz
  rw [Matrix.det_fin_one] at hcorner
  exact sub_eq_zero.mp hcorner
theorem Submission.p05_umgi_inner_inverse_of_reconstruction_a5b449214a :
    ∀ {R : Type*} [CommRing R] (n p d : ℕ) (P : Matrix (Fin n) (Fin p) R)
      (rows : Fin d ↪ Fin n) (cols : Fin d ↪ Fin p)
      (T : Matrix (Fin d) (Fin d) R)
      (_hfactor : P = (P.submatrix id cols) * T * (P.submatrix rows id)),
      ∃ Q : Matrix (Fin p) (Fin n) R, P * Q * P = P := by
  intro R _ n p d P rows cols T hfactor
  let U : Matrix (Fin p) (Fin d) R := (1 : Matrix (Fin p) (Fin p) R).submatrix id cols
  let V : Matrix (Fin d) (Fin n) R := (1 : Matrix (Fin n) (Fin n) R).submatrix rows id
  have hU : P * U = P.submatrix id cols :=
    Matrix.mul_submatrix_one (Equiv.refl (Fin p)) cols P
  have hV : V * P = P.submatrix rows id :=
    Matrix.one_submatrix_mul rows (Equiv.refl (Fin n)) P
  refine ⟨U * T * V, ?_⟩
  calc
    P * (U * T * V) * P = (P * U) * T * (V * P) := by
      simp only [Matrix.mul_assoc]
    _ = (P.submatrix id cols) * T * (P.submatrix rows id) := by rw [hU, hV]
    _ = P := hfactor.symm


theorem Submission.p05_ums_inner_inverse_of_minors_a5b449214a
    {R : Type*} [CommRing R] (n p d : ℕ)
    (P : Matrix (Fin n) (Fin p) R)
    (rows : Fin d ↪ Fin n) (cols : Fin d ↪ Fin p)
    (_hunit : IsUnit (Matrix.det (P.submatrix rows cols)))
    (_hnext : ∀ (rows' : Fin (d + 1) ↪ Fin n) (cols' : Fin (d + 1) ↪ Fin p),
      Matrix.det (P.submatrix rows' cols') = 0) :
    ∃ Q : Matrix (Fin p) (Fin n) R, P * Q * P = P := by
  exact Submission.p05_umgi_inner_inverse_of_reconstruction_a5b449214a
    n p d P rows cols (P.submatrix rows cols)⁻¹
    (Submission.p05_umgi_minor_reconstruction_a5b449214a
      n p d P rows cols _hunit _hnext)
theorem Submission.p05_ums_section_of_inner_inverse_a5b449214a
    {R : Type*} [CommRing R]
    {F : Type*} [AddCommGroup F] [Module R F]
    {G : Type*} [AddCommGroup G] [Module R G]
    {M : Type*} [AddCommGroup M] [Module R M]
    (f : G →ₗ[R] F) (g : F →ₗ[R] G) (π : F →ₗ[R] M)
    (_hinner : (f.comp g).comp f = f) (_hπ : Function.Surjective π)
    (_hker : LinearMap.ker π = LinearMap.range f) :
    ∃ s : M →ₗ[R] F, π.comp s = LinearMap.id := by
  classical
  let r : F →ₗ[R] F := LinearMap.id - f.comp g
  have hπf (y : G) : π (f y) = 0 := by
    apply LinearMap.mem_ker.mp
    rw [_hker]
    exact LinearMap.mem_range_self f y
  have hfiber (x y : F) (h : π x = π y) : r x = r y := by
    apply sub_eq_zero.mp
    rw [← map_sub]
    have hmem : x - y ∈ LinearMap.ker π := by
      rw [LinearMap.mem_ker, map_sub, h, sub_self]
    rw [_hker] at hmem
    obtain ⟨z, hz⟩ := hmem
    rw [← hz]
    change f z - f (g (f z)) = 0
    rw [show f (g (f z)) = f z from LinearMap.congr_fun _hinner z, sub_self]
  choose t ht using _hπ
  let s : M →ₗ[R] F :=
    { toFun := fun m => r (t m)
      map_add' := by
        intro m n
        rw [← map_add]
        apply hfiber
        rw [ht, map_add, ht, ht]
      map_smul' := by
        intro a m
        change r (t (a • m)) = a • r (t m)
        rw [← map_smul]
        apply hfiber
        rw [ht, map_smul, ht] }
  refine ⟨s, ?_⟩
  ext m
  change π (t m - f (g (t m))) = m
  rw [map_sub, hπf, sub_zero, ht]


namespace Submission

theorem p05_ptm_split_of_unit_minor_a5b449214a
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    (n p d : ℕ) (P : Matrix (Fin n) (Fin p) R) (π : (Fin n → R) →ₗ[R] M)
    (_hπ : Function.Surjective π) (_hker : LinearMap.ker π = LinearMap.range P.mulVecLin)
    (rows : Fin d ↪ Fin n) (cols : Fin d ↪ Fin p)
    (_hunit : IsUnit (Matrix.det (P.submatrix rows cols)))
    (_hnext : ∀ (rows' : Fin (d + 1) ↪ Fin n) (cols' : Fin (d + 1) ↪ Fin p),
      Matrix.det (P.submatrix rows' cols') = 0) :
    ∃ s : M →ₗ[R] (Fin n → R), π.comp s = LinearMap.id := by
  obtain ⟨Q, hQ⟩ := Submission.p05_ums_inner_inverse_of_minors_a5b449214a
    n p d P rows cols _hunit _hnext
  refine Submission.p05_ums_section_of_inner_inverse_a5b449214a
    P.mulVecLin Q.mulVecLin π ?_ _hπ _hker
  simpa only [Matrix.mulVecLin_mul] using
    congrArg (fun A : Matrix (Fin n) (Fin p) R => A.mulVecLin) hQ

end Submission
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


namespace Submission

theorem p05_fr_projective_of_trivial_minors_a5b449214a
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    (n p : ℕ) (P : Matrix (Fin n) (Fin p) R) (π : (Fin n → R) →ₗ[R] M)
    (_hπ : Function.Surjective π)
    (_hker : LinearMap.ker π = LinearMap.range P.mulVecLin)
    (_hminor : ∀ d : ℕ,
      let J : Ideal R := Ideal.span
        {x : R | ∃ (rows : Fin d ↪ Fin n) (cols : Fin d ↪ Fin p),
          x = Matrix.det (P.submatrix rows cols)}
      J = ⊥ ∨ J = ⊤) :
    Module.Projective R M := by
  classical
  -- Choose a maximal size whose minors generate the unit ideal.
  let J : ℕ → Ideal R := fun d ↦ Ideal.span
    {x : R | ∃ (rows : Fin d ↪ Fin n) (cols : Fin d ↪ Fin p),
      x = Matrix.det (P.submatrix rows cols)}
  have hzero : J 0 = ⊤ := by
    apply (Ideal.eq_top_iff_one _).mpr
    apply Ideal.subset_span
    exact ⟨Function.Embedding.ofIsEmpty, Function.Embedding.ofIsEmpty,
      Matrix.det_isEmpty.symm⟩
  let d := Nat.findGreatest (fun k ↦ J k = ⊤) n
  have hd : J d = ⊤ :=
    Nat.findGreatest_spec (P := fun k ↦ J k = ⊤) (Nat.zero_le n) hzero
  have hnext : ∀ (rows : Fin (d + 1) ↪ Fin n) (cols : Fin (d + 1) ↪ Fin p),
      Matrix.det (P.submatrix rows cols) = 0 := by
    intro rows cols
    have hbound : d + 1 ≤ n := by
      simpa using Fintype.card_le_of_injective rows rows.injective
    have hnot : J (d + 1) ≠ ⊤ :=
      Nat.findGreatest_is_greatest (P := fun k ↦ J k = ⊤) (Nat.lt_succ_self d) hbound
    have hbot : J (d + 1) = ⊥ := (_hminor (d + 1)).resolve_right hnot
    have hmem : Matrix.det (P.submatrix rows cols) ∈ J (d + 1) :=
      Ideal.subset_span ⟨rows, cols, rfl⟩
    simpa only [hbot, Ideal.mem_bot] using hmem
  -- Enumerate all minors of this size, including the unique empty minor.
  let I := (Fin d ↪ Fin n) × (Fin d ↪ Fin p)
  let q := Fintype.card I
  let e : Fin q ≃ I := (Fintype.equivFin I).symm
  let f : Fin q → R := fun i ↦ Matrix.det (P.submatrix (e i).1 (e i).2)
  have hcover : Ideal.span (Set.range f) = ⊤ := by
    convert hd using 1
    congr 1
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨(e i).1, (e i).2, rfl⟩
    · rintro ⟨rows, cols, rfl⟩
      exact ⟨e.symm (rows, cols), by simp [f]⟩
  obtain ⟨s, hs⟩ := p05_ptm_split_of_away_splits_a5b449214a
    n p q P π _hπ _hker f hcover (by
      intro i
      let S := Submonoid.powers (f i)
      let A := Localization.Away (f i)
      let loc (k : ℕ) : (Fin k → R) →ₗ[R] (Fin k → A) :=
        LinearMap.pi fun j ↦ (Algebra.linearMap R A).comp (LinearMap.proj j)
      let mloc := LocalizedModule.mkLinearMap S M
      let PA : Matrix (Fin n) (Fin p) A := P.map (algebraMap R A)
      let πA : (Fin n → A) →ₗ[A] LocalizedModule S M :=
        IsLocalizedModule.mapExtendScalars S (loc n) mloc A π
      have hπA : Function.Surjective πA :=
        IsLocalizedModule.map_surjective S (loc n) mloc π _hπ
      -- Localization of the matrix map is entrywise localization of the matrix.
      have hP : IsLocalizedModule.map S (loc p) (loc n) P.mulVecLin =
          PA.mulVecLin.restrictScalars R := by
        apply IsLocalizedModule.linearMap_ext S (loc p) (loc n)
        rw [IsLocalizedModule.map_comp]
        apply LinearMap.ext
        intro x
        funext j
        simp [loc, PA, Matrix.mulVec, dotProduct]
      have hex := IsLocalizedModule.map_exact S (loc p) (loc n) mloc
        P.mulVecLin π (LinearMap.exact_iff.mpr _hker)
      have hkerA : LinearMap.ker πA = LinearMap.range PA.mulVecLin := by
        apply LinearMap.exact_iff.mp
        rw [hP] at hex
        exact hex
      have hunit : IsUnit (Matrix.det (PA.submatrix (e i).1 (e i).2)) := by
        change IsUnit (Matrix.det ((algebraMap R A).mapMatrix
          (P.submatrix (e i).1 (e i).2)))
        rw [← RingHom.map_det]
        exact IsLocalization.map_units A ⟨f i, Submonoid.mem_powers (f i)⟩
      have hnextA : ∀ (rows : Fin (d + 1) ↪ Fin n) (cols : Fin (d + 1) ↪ Fin p),
          Matrix.det (PA.submatrix rows cols) = 0 := by
        intro rows cols
        change Matrix.det ((algebraMap R A).mapMatrix (P.submatrix rows cols)) = 0
        rw [← RingHom.map_det, hnext, map_zero]
      obtain ⟨sA, hsA⟩ := p05_ptm_split_of_unit_minor_a5b449214a
        n p d PA πA hπA hkerA (e i).1 (e i).2 hunit hnextA
      -- Identify localized finite free modules with tuples over the localized ring.
      let E : (Fin n → A) ≃ₗ[A] LocalizedModule S (Fin n → R) :=
        (IsLocalizedModule.linearEquiv S (loc n)
          (LocalizedModule.mkLinearMap S (Fin n → R))).extendScalarsOfIsLocalization S A
      have hπE : (LocalizedModule.map S π).comp E.toLinearMap = πA := by
        apply LinearMap.restrictScalars_injective R
        apply IsLocalizedModule.linearMap_ext S (loc n) mloc
        apply LinearMap.ext
        intro x
        simp [E, πA, mloc, IsLocalizedModule.mapExtendScalars,
          LocalizedModule.mkLinearMap_apply]
        exact LocalizedModule.map_mk S π x 1
      refine ⟨E.toLinearMap.comp sA, ?_⟩
      rw [← LinearMap.comp_assoc, hπE, hsA])
  exact Module.Projective.of_split s π hs

end Submission
