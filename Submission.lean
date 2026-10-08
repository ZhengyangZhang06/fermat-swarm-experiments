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
