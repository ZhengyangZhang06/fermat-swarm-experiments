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
