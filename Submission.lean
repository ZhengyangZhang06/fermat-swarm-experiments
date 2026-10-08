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
