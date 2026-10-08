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
