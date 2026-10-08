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
