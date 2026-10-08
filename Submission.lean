/-
Copyright 2026 Anthropic, PBC. Licensed under Apache-2.0; see LICENSE.
Source: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_Rep_isZero_tateCohomology_of_forall_sylow.lean
Modified: replaced the proof with sorry and removed P2M proof imports.
Requires the upstream Definitions modules and their dependencies.
-/

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
attribute [-simp] Representation.TateResCor.cosetDecomp_apply Rep.coe_tateHneg1Res_apply Representation.TateResCor.coe_tateHneg1Cores_apply Representation.TateResCor.tateH0Res_mk Rep.coe_tateHneg1Cores_apply Rep.tateH0Res_mk Representation.TateResCor.coe_cosetNormInvariants_apply Rep.tateH0Cores_mk Representation.TateResCor.coinvariantsCores_mk Representation.TateResCor.coinvariantsTransfer_mk Representation.TateResCor.tateH0Cores_mk Representation.TateResCor.coe_tateHneg1Res_apply Rep.coe_tateδneg2_apply

set_option autoImplicit false
universe u
open CategoryTheory Rep
theorem Rep.isZero_tateCohomology_of_forall_sylow {k G : Type u} [CommRing k] [Group G] [Fintype G]
    (A : Rep.{u} k G) (q : ℤ)
    (h : ∀ (p : ℕ) [Fact p.Prime] (P : Sylow p G) [Fintype (P : Subgroup G)],
      CategoryTheory.Limits.IsZero ((Rep.res (P : Subgroup G).subtype A).tateCohomology q)) :
    CategoryTheory.Limits.IsZero (A.tateCohomology q) := by
  sorry


theorem Rep.isZero_tateCohomology_of_forall_sylow {k G : Type u} [CommRing k] [Group G] [Fintype G]
    (A : Rep.{u} k G) (q : ℤ)
    (h : ∀ (p : ℕ) [Fact p.Prime] (P : Sylow p G) [Fintype (P : Subgroup G)],
      CategoryTheory.Limits.IsZero ((Rep.res (P : Subgroup G).subtype A).tateCohomology q)) :
    CategoryTheory.Limits.IsZero (A.tateCohomology q) := by
  sorry

namespace Submission

/-- The subgroup coefficient in a right transversal containing `1` gives an equivariant retraction.
`Subgroup.exists_isComplement_right` supplies the normalized transversal, and
`Subgroup.IsComplement.equiv` records the unique factorization into subgroup and transversal parts.
`Subgroup.IsComplement.equiv_mul_left` gives equivariance, and
`Subgroup.IsComplement.equiv_fst_eq_self_of_mem_of_one_mem` gives normalization.
All four APIs are from
`Mathlib/GroupTheory/Complement.lean` at pinned mathlib commit
`db584cd6d46c92f209a44c0f1c829460d327499d`. -/
theorem p04_rsh_82a013d1d0_equivariant_retraction {G : Type*} [Group G] (H : Subgroup G) :
    ∃ r : G → H, (∀ (h : H) (g : G), r ((h : G) * g) = h * r g) ∧
      ∀ h : H, r (h : G) = h := by
  obtain ⟨T, hT, h1⟩ := H.exists_isComplement_right (1 : G)
  refine ⟨fun g => (hT.equiv g).1, ?_, ?_⟩
  · intro h g
    exact congrArg Prod.fst (hT.equiv_mul_left h g)
  · intro h
    exact hT.equiv_fst_eq_self_of_mem_of_one_mem h1 h.property

end Submission

namespace Submission

/-- The signed prism assignment extends to morphisms of the restricted standard complex.

The free-module extension uses `Finsupp.lift` and `MonoidAlgebra.coeffLinearEquiv`, as in
`Rep.standardComplex.d`. Equivariance is checked on generators using
`Representation.ofMulAction_single` and `Fin.insertNth_eq_iff`. -/
theorem p04_prism_a8325b9888_equivariant_components :
    ∀ {k G : Type _} [CommRing k] [Group G] (H : Subgroup G) (u v : G → G),
      (∀ (h : H) (g : G), u ((h : G) * g) = (h : G) * u g) →
      (∀ (h : H) (g : G), v ((h : G) * g) = (h : G) * v g) →
      let P : ∀ n : ℕ, (Fin (n + 1) → G) → MonoidAlgebra k (Fin (n + 2) → G) :=
        fun n c => ∑ j : Fin (n + 1),
          MonoidAlgebra.single (Fin.insertNth j.castSucc (u (c j))
            (fun i : Fin (n + 1) => if i < j then u (c i) else v (c i)))
            ((-1 : k) ^ j.val)
      let C := ((Rep.resFunctor H.subtype).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (Rep.standardComplex k G)
      ∃ D : ∀ n : ℕ, C.X n ⟶ C.X (n + 1), ∀ (n : ℕ) (c : Fin (n + 1) → G),
        (D n).hom (MonoidAlgebra.single c (1 : k)) = P n c := by
  classical
  intro k G _ _ H u v hu hv P C
  let L (n : ℕ) : MonoidAlgebra k (Fin (n + 1) → G) →ₗ[k]
      MonoidAlgebra k (Fin (n + 2) → G) :=
    (Finsupp.lift _ k _ (P n)) ∘ₗ (MonoidAlgebra.coeffLinearEquiv k).toLinearMap
  have hL (n : ℕ) (c : Fin (n + 1) → G) :
      L n (MonoidAlgebra.single c 1) = P n c := by
    simp [L]
  have hP (n : ℕ) (h : H) (c : Fin (n + 1) → G) :
      P n ((h : G) • c) =
        Representation.ofMulAction k G (Fin (n + 2) → G) (h : G) (P n c) := by
    simp only [P, map_sum, Representation.ofMulAction_single]
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    apply Fin.insertNth_eq_iff.mpr
    constructor
    · simpa using hu h (c j)
    · funext i
      simp only [Fin.removeNth, Pi.smul_apply, smul_eq_mul, Fin.insertNth_apply_succAbove]
      split_ifs with hij
      · exact hu h (c i)
      · exact hv h (c i)
  let D (n : ℕ) : C.X n ⟶ C.X (n + 1) := Rep.ofHom
    { toLinearMap := L n
      isIntertwining' := fun h => by
        refine MonoidAlgebra.lhom_ext' fun (c : Fin (n + 1) → G) => LinearMap.ext_ring ?_
        change L n (Representation.ofMulAction k G (Fin (n + 1) → G) (h : G)
          (MonoidAlgebra.single c 1)) =
            Representation.ofMulAction k G (Fin (n + 2) → G) (h : G)
              (L n (MonoidAlgebra.single c 1))
        rw [Representation.ofMulAction_single, hL, hL]
        exact hP n h c }
  exact ⟨D, hL⟩

end Submission

set_option maxHeartbeats 4000000
set_option warningAsError true

namespace Submission

/-- Pair noncentral prism faces with the signed prisms of the boundary.

The inverse pairing sends a boundary index `(b, t)` to `(t + 1, b)` when `b ≤ t`,
and to `(t, b + 1)` otherwise. The paired tuples agree and the exponents differ by one.
-/
theorem p04_pb_60221840b0_noncentral_cancellation
    {k X : Type _} [CommRing k] (u v : X → X) (n : ℕ) (c : Fin (n + 2) → X) :
    let Q : ∀ m : ℕ, (Fin (m + 1) → X) → Fin (m + 1) → (Fin (m + 2) → X) :=
      fun m d j => Fin.insertNth j.castSucc (u (d j))
        (fun i : Fin (m + 1) => if i < j then u (d i) else v (d i))
    (∑ j : Fin (n + 2), ∑ a : Fin (n + 3) with a.val < j.val ∨ j.val + 1 < a.val,
      MonoidAlgebra.single (Q (n + 1) c j ∘ a.succAbove) ((-1 : k) ^ (j.val + a.val))) +
    (∑ b : Fin (n + 2), ∑ t : Fin (n + 1),
      MonoidAlgebra.single (Q n (c ∘ b.succAbove) t) ((-1 : k) ^ (b.val + t.val))) = 0 := by
  classical
  intro Q
  -- Evaluate the inserted tuple on either side of its transition.
  have eval (m : ℕ) (d : Fin (m + 1) → X) (j : Fin (m + 1)) (s : Fin (m + 2)) :
      Q m d j s = if h : s.val ≤ j.val then u (d ⟨s.val, by omega⟩)
        else v (d ⟨s.val - 1, by omega⟩) := by
    dsimp only [Q]
    split_ifs with h
    · by_cases he : s = j.castSucc
      · subst s
        simp
      · have hs : s < j.castSucc := by
          simp only [Fin.lt_def, Fin.val_castSucc]
          have := Fin.ext_iff.not.mp he
          simp only [Fin.val_castSucc] at this
          omega
        rw [Fin.insertNth_apply_below hs]
        simp only [Fin.lt_def, Fin.coe_castPred, if_pos (show s.val < j.val by exact hs)]
        simp
        congr 2
    · have hs : j.castSucc < s := by
        simpa only [Fin.lt_def, Fin.val_castSucc] using Nat.lt_of_not_ge h
      rw [Fin.insertNth_apply_above hs]
      simp only [Fin.lt_def, Fin.val_pred, if_neg (show ¬ s.val - 1 < j.val by omega)]
      simp
      congr 2
  -- Deleting before or after the transition gives the corresponding smaller prism.
  have before (b : Fin (n + 2)) (t : Fin (n + 1)) (h : b.val ≤ t.val) :
      Q (n + 1) c t.succ ∘ b.castSucc.succAbove = Q n (c ∘ b.succAbove) t := by
    funext s
    by_cases hsb : s.val < b.val <;> by_cases hst : s.val ≤ t.val
    all_goals simp (disch := omega) only [Function.comp_apply, eval, Fin.succAbove,
      Fin.lt_def, Fin.val_castSucc, Fin.val_succ, if_pos, if_neg, dif_pos, dif_neg]
    all_goals first | omega | (congr 2 <;> apply Fin.ext <;> simp <;> omega)
  have after (b : Fin (n + 2)) (t : Fin (n + 1)) (h : t.val < b.val) :
      Q (n + 1) c t.castSucc ∘ b.succ.succAbove = Q n (c ∘ b.succAbove) t := by
    funext s
    by_cases hsb : s.val < b.val + 1 <;> by_cases hst : s.val ≤ t.val
    all_goals simp (disch := omega) only [Function.comp_apply, eval, Fin.succAbove,
      Fin.lt_def, Fin.val_castSucc, Fin.val_succ, if_pos, if_neg, dif_pos, dif_neg]
    all_goals first | omega | (congr 2 <;> apply Fin.ext <;> simp <;> omega)
  -- The inverse pairing sends (b, t) to (t + 1, b) or (t, b + 1).
  let I := (Finset.univ : Finset (Fin (n + 2) × Fin (n + 3))).filter
    (fun p => p.2.val < p.1.val ∨ p.1.val + 1 < p.2.val)
  let pair (p : Fin (n + 2) × Fin (n + 1)) : Fin (n + 2) × Fin (n + 3) :=
    if p.1.val ≤ p.2.val then (p.2.succ, p.1.castSucc) else (p.2.castSucc, p.1.succ)
  have reindex :
      (∑ p : Fin (n + 2) × Fin (n + 1),
        -MonoidAlgebra.single (Q n (c ∘ p.1.succAbove) p.2)
          ((-1 : k) ^ (p.1.val + p.2.val))) =
      ∑ p ∈ I, MonoidAlgebra.single (Q (n + 1) c p.1 ∘ p.2.succAbove)
        ((-1 : k) ^ (p.1.val + p.2.val)) := by
    apply Finset.sum_bij (fun p _ => pair p)
    · intro p _
      simp only [I, Finset.mem_filter, Finset.mem_univ, true_and]
      dsimp only [pair]
      split_ifs <;> simp only [Fin.val_succ, Fin.val_castSucc] <;> omega
    · intro p _ q _ hpq
      have h₁ := congrArg (fun r => r.1.val) hpq
      have h₂ := congrArg (fun r => r.2.val) hpq
      dsimp only [pair] at h₁ h₂
      split_ifs at h₁ h₂ <;> simp only [Fin.val_succ, Fin.val_castSucc] at *
      all_goals apply Prod.ext <;> apply Fin.ext <;> omega
    · rintro ⟨j, a⟩ hp
      have hp : a.val < j.val ∨ j.val + 1 < a.val := by simpa [I] using hp
      rcases hp with h | h
      · refine ⟨(⟨a.val, by omega⟩, ⟨j.val - 1, by omega⟩), Finset.mem_univ _, ?_⟩
        dsimp only [pair]
        rw [if_pos (by omega)]
        apply Prod.ext <;> apply Fin.ext <;> simp
        omega
      · refine ⟨(⟨a.val - 1, by omega⟩, ⟨j.val, by omega⟩), Finset.mem_univ _, ?_⟩
        dsimp only [pair]
        rw [if_neg (by omega)]
        apply Prod.ext <;> apply Fin.ext <;> simp
        omega
    -- Corresponding exponents differ by one.
    · rintro ⟨b, t⟩ _
      dsimp only [pair]
      split_ifs with h
      · rw [before b t h]
        simp only [Fin.val_succ, Fin.val_castSucc]
        rw [show t.val + 1 + b.val = (b.val + t.val) + 1 by omega, pow_succ]
        simp
      · rw [after b t (by omega)]
        simp only [Fin.val_succ, Fin.val_castSucc]
        rw [show t.val + (b.val + 1) = (b.val + t.val) + 1 by omega, pow_succ]
        simp
  simp only [I, Finset.sum_filter, Fintype.sum_prod_type, Finset.sum_neg_distrib] at reindex
  simp only [Finset.sum_filter]
  rw [← reindex]
  exact neg_add_cancel _

end Submission

namespace Submission

/-- The two central faces of each inserted tuple telescope to the endpoint tuples. -/
theorem p04_pb_60221840b0_central_telescoping :
    ∀ {k X : Type _} [CommRing k] (u v : X → X) (m : ℕ) (c : Fin (m + 1) → X),
      let Q : Fin (m + 1) → (Fin (m + 2) → X) := fun j =>
        Fin.insertNth j.castSucc (u (c j))
          (fun i : Fin (m + 1) => if i < j then u (c i) else v (c i))
      (∑ j : Fin (m + 1),
        (MonoidAlgebra.single (Q j ∘ j.castSucc.succAbove) (1 : k) -
          MonoidAlgebra.single (Q j ∘ j.succ.succAbove) (1 : k))) =
        MonoidAlgebra.single (v ∘ c) (1 : k) -
          MonoidAlgebra.single (u ∘ c) (1 : k) := by
  intro k X _ u v m c Q
  classical
  -- Moving the transition one position accounts for the two central deletions.
  let T : ℕ → (Fin (m + 1) → X) := fun l i =>
    if i.val < l then u (c i) else v (c i)
  have hleft (j : Fin (m + 1)) : Q j ∘ j.castSucc.succAbove = T j.val := by
    simpa only [Q, T, Fin.lt_def] using
      Fin.insertNth_comp_succAbove j.castSucc (u (c j))
        (fun i : Fin (m + 1) => if i < j then u (c i) else v (c i))
  have hright (j : Fin (m + 1)) : Q j ∘ j.succ.succAbove = T (j.val + 1) := by
    funext i
    change Fin.insertNth (α := fun _ => X) j.castSucc (u (c j))
      (fun i : Fin (m + 1) => if i < j then u (c i) else v (c i))
      (j.succ.succAbove i) = if i.val < j.val + 1 then u (c i) else v (c i)
    rcases lt_trichotomy i j with hij | rfl | hji
    · rw [Fin.succAbove_succ_of_le _ _ hij.le,
        ← Fin.succAbove_castSucc_of_lt _ _ hij, Fin.insertNth_apply_succAbove]
      simp [hij, show i.val < j.val + 1 by omega]
    · simp
    · rw [Fin.succAbove_succ_of_lt _ _ hji,
        ← Fin.succAbove_castSucc_of_le _ _ hji.le, Fin.insertNth_apply_succAbove]
      simp [not_lt_of_gt hji, show ¬i.val < j.val + 1 by omega]
  have hzero : T 0 = v ∘ c := by
    funext i
    simp [T]
  have hlast : T (m + 1) = u ∘ c := by
    funext i
    simp [T, i.is_lt]
  -- The adjacent differences cancel, leaving the all-v and all-u tuples.
  simp_rw [hleft, hright]
  rw [Fin.sum_univ_eq_sum_range (fun l =>
    MonoidAlgebra.single (T l) (1 : k) - MonoidAlgebra.single (T (l + 1)) (1 : k)),
    Finset.sum_range_sub', hzero, hlast]

end Submission

namespace Submission

/-- The alternating prism has boundary equal to its two endpoints. -/
theorem p04_prism_a8325b9888_boundary_identity :
    ∀ {k X : Type _} [CommRing k] (u v : X → X),
    let P : ∀ n : ℕ, (Fin (n + 1) → X) → MonoidAlgebra k (Fin (n + 2) → X) :=
      fun n c => ∑ j : Fin (n + 1),
        MonoidAlgebra.single
          (Fin.insertNth j.castSucc (u (c j))
            (fun i : Fin (n + 1) => if i < j then u (c i) else v (c i)))
          ((-1 : k) ^ j.val)
    (∀ c : Fin 1 → X, Rep.standardComplex.d k X 1 (P 0 c) =
      MonoidAlgebra.single (v ∘ c) (1 : k) - MonoidAlgebra.single (u ∘ c) (1 : k)) ∧
    ∀ (n : ℕ) (c : Fin (n + 2) → X),
      Rep.standardComplex.d k X (n + 2) (P (n + 1) c) +
          ∑ b : Fin (n + 2), ((-1 : k) ^ b.val) • P n (c ∘ b.succAbove) =
        MonoidAlgebra.single (v ∘ c) (1 : k) -
          MonoidAlgebra.single (u ∘ c) (1 : k) := by
  classical
  intro k X _ u v P
  let Q : ∀ m : ℕ, (Fin (m + 1) → X) → Fin (m + 1) → (Fin (m + 2) → X) :=
    fun m c j => Fin.insertNth j.castSucc (u (c j))
      (fun i : Fin (m + 1) => if i < j then u (c i) else v (c i))
  -- Separate the two central faces from all other faces, retaining their signs.
  have split_faces (m : ℕ) (c : Fin (m + 1) → X) (j : Fin (m + 1)) :
      (∑ a : Fin (m + 2),
        MonoidAlgebra.single (Q m c j ∘ a.succAbove) ((-1 : k) ^ (j.val + a.val))) =
      (∑ a : Fin (m + 2) with a.val < j.val ∨ j.val + 1 < a.val,
        MonoidAlgebra.single (Q m c j ∘ a.succAbove) ((-1 : k) ^ (j.val + a.val))) +
      (MonoidAlgebra.single (Q m c j ∘ j.castSucc.succAbove) (1 : k) -
        MonoidAlgebra.single (Q m c j ∘ j.succ.succAbove) (1 : k)) := by
    have central :
        (Finset.univ.filter fun a : Fin (m + 2) =>
          ¬ (a.val < j.val ∨ j.val + 1 < a.val)) = {j.castSucc, j.succ} := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, Fin.val_castSucc,
        Fin.val_succ]
      omega
    have distinct : j.castSucc ≠ j.succ := by
      intro h
      have := congrArg Fin.val h
      simp only [Fin.val_castSucc, Fin.val_succ] at this
      omega
    have even_sign : (-1 : k) ^ (j.val + j.val) = 1 := by
      rw [← two_mul, pow_mul]
      simp
    have odd_sign : (-1 : k) ^ (j.val + (j.val + 1)) = -1 := by
      rw [← Nat.add_assoc, pow_succ, even_sign, one_mul]
    rw [← Finset.sum_filter_add_sum_filter_not
      (s := Finset.univ) (p := fun a : Fin (m + 2) =>
        a.val < j.val ∨ j.val + 1 < a.val)]
    rw [central, Finset.sum_pair distinct]
    simp only [Fin.val_castSucc, Fin.val_succ, even_sign, odd_sign,
      MonoidAlgebra.single_neg, sub_eq_add_neg]
  have boundary (m : ℕ) (c : Fin (m + 1) → X) :
      Rep.standardComplex.d k X (m + 1) (P m c) =
      (∑ j : Fin (m + 1),
        ∑ a : Fin (m + 2) with a.val < j.val ∨ j.val + 1 < a.val,
          MonoidAlgebra.single (Q m c j ∘ a.succAbove) ((-1 : k) ^ (j.val + a.val))) +
      (MonoidAlgebra.single (v ∘ c) (1 : k) -
        MonoidAlgebra.single (u ∘ c) (1 : k)) := by
    change Rep.standardComplex.d k X (m + 1)
      (∑ j : Fin (m + 1), MonoidAlgebra.single (Q m c j) ((-1 : k) ^ j.val)) = _
    simp only [map_sum, Rep.standardComplex.d_single, ← pow_add]
    simp_rw [split_faces]
    rw [Finset.sum_add_distrib]
    congr 1
    exact Submission.p04_pb_60221840b0_central_telescoping u v m c
  constructor
  · intro c
    rw [boundary]
    have no_noncentral (j : Fin 1) (a : Fin 2) :
        ¬ (a.val < j.val ∨ j.val + 1 < a.val) := by
      have hj := j.isLt
      have ha := a.isLt
      omega
    simp only [no_noncentral, Finset.filter_false, Finset.sum_empty,
      Finset.sum_const_zero, zero_add]
  · intro n c
    have lower :
        (∑ b : Fin (n + 2), ((-1 : k) ^ b.val) • P n (c ∘ b.succAbove)) =
        ∑ b : Fin (n + 2), ∑ t : Fin (n + 1),
          MonoidAlgebra.single (Q n (c ∘ b.succAbove) t)
            ((-1 : k) ^ (b.val + t.val)) := by
      simp only [P, Q, Finset.smul_sum, MonoidAlgebra.smul_single, smul_eq_mul, pow_add]
    rw [boundary, lower, add_right_comm]
    have cancel := Submission.p04_pb_60221840b0_noncentral_cancellation (k := k) u v n c
    change _ + _ = 0 at cancel
    rw [cancel, zero_add]

end Submission

namespace Submission

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The equivariant prism operators give a homotopy from the vertex map `v` to `u`. -/
theorem p04_rsh_82a013d1d0_prism_homotopy
    {k G : Type _} [CommRing k] [Group G] (H : Subgroup G) (u v : G → G)
    (hu : ∀ (h : H) (g : G), u ((h : G) * g) = (h : G) * u g)
    (hv : ∀ (h : H) (g : G), v ((h : G) * g) = (h : G) * v g) :
    let C := ((Rep.resFunctor H.subtype).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (Rep.standardComplex k G)
    ∀ U V : CategoryTheory.End C,
      (∀ (n : ℕ) (c : Fin (n + 1) → G),
        (U.f n).hom (MonoidAlgebra.single c (1 : k)) =
          MonoidAlgebra.single (u ∘ c) (1 : k)) →
      (∀ (n : ℕ) (c : Fin (n + 1) → G),
        (V.f n).hom (MonoidAlgebra.single c (1 : k)) =
          MonoidAlgebra.single (v ∘ c) (1 : k)) →
      Nonempty (Homotopy V U) := by
  classical
  intro C U V hU hV
  let P : ∀ n : ℕ, (Fin (n + 1) → G) → MonoidAlgebra k (Fin (n + 2) → G) :=
    fun n c => ∑ j : Fin (n + 1),
      MonoidAlgebra.single
        (Fin.insertNth j.castSucc (u (c j))
          (fun i : Fin (n + 1) => if i < j then u (c i) else v (c i)))
        ((-1 : k) ^ j.val)
  obtain ⟨D, hD⟩ := p04_prism_a8325b9888_equivariant_components (k := k) H u v hu hv
  change ∀ (n : ℕ) (c : Fin (n + 1) → G),
    (D n).hom (MonoidAlgebra.single c (1 : k)) = P n c at hD
  obtain ⟨hzero, hsucc⟩ := p04_prism_a8325b9888_boundary_identity (k := k) u v
  change ∀ c : Fin 1 → G, Rep.standardComplex.d k G 1 (P 0 c) =
    MonoidAlgebra.single (v ∘ c) (1 : k) - MonoidAlgebra.single (u ∘ c) (1 : k) at hzero
  change ∀ (n : ℕ) (c : Fin (n + 2) → G),
    Rep.standardComplex.d k G (n + 2) (P (n + 1) c) +
      ∑ b : Fin (n + 2), ((-1 : k) ^ b.val) • P n (c ∘ b.succAbove) =
    MonoidAlgebra.single (v ∘ c) (1 : k) - MonoidAlgebra.single (u ∘ c) (1 : k) at hsucc
  have hd (n : ℕ) (x : MonoidAlgebra k (Fin (n + 2) → G)) :
      (C.d (n + 1) n).hom x = Rep.standardComplex.d k G (n + 1) x :=
    Rep.standardComplex.d_apply k G x
  let hom : ∀ i j, C.X i ⟶ C.X j := fun i j =>
    if h : i + 1 = j then D i ≫ eqToHom (congrArg C.X h) else 0
  have hom_succ (i : ℕ) : hom i (i + 1) = D i := by
    simp [hom]
  refine ⟨{ hom := hom, zero := ?_, comm := ?_ }⟩
  · intro i j hij
    exact dif_neg hij
  · intro n
    cases n with
    | zero =>
      rw [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex, hom_succ, zero_add]
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.toLinearMap_injective
      refine MonoidAlgebra.lhom_ext' fun (c : Fin 1 → G) => LinearMap.ext_ring ?_
      change (V.f 0).hom (MonoidAlgebra.single c (1 : k)) =
        (C.d 1 0).hom ((D 0).hom (MonoidAlgebra.single c (1 : k))) +
          (U.f 0).hom (MonoidAlgebra.single c (1 : k))
      rw [hU, hV, hD, hd, hzero, sub_add_cancel]
    | succ n =>
      rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex, hom_succ, hom_succ]
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.toLinearMap_injective
      refine MonoidAlgebra.lhom_ext' fun (c : Fin (n + 2) → G) => LinearMap.ext_ring ?_
      change (V.f (n + 1)).hom (MonoidAlgebra.single c (1 : k)) =
        (D n).hom ((C.d (n + 1) n).hom (MonoidAlgebra.single c (1 : k))) +
          (C.d (n + 2) (n + 1)).hom
            ((D (n + 1)).hom (MonoidAlgebra.single c (1 : k))) +
          (U.f (n + 1)).hom (MonoidAlgebra.single c (1 : k))
      rw [hU, hV, hD, hd, hd, Rep.standardComplex.d_of, map_sum]
      have hsum :
          (∑ b : Fin (n + 2), (D n).hom
            (MonoidAlgebra.single (c ∘ b.succAbove) ((-1 : k) ^ b.val))) =
          ∑ b : Fin (n + 2), ((-1 : k) ^ b.val) • P n (c ∘ b.succAbove) := by
        apply Finset.sum_congr rfl
        intro b _
        rw [← mul_one ((-1 : k) ^ b.val), ← smul_eq_mul,
          ← MonoidAlgebra.smul_single, map_smul, hD]
        simp only [smul_eq_mul, mul_one]
      rw [hsum, add_comm _ (Rep.standardComplex.d k G (n + 2) (P (n + 1) c)),
        hsucc, sub_add_cancel]

set_option backward.isDefEq.respectTransparency.types false in
/-- The coordinatewise retraction and inclusion of homogeneous tuples give the
restricted standard-complex homotopy equivalence.

The linear extensions and their differential compatibility use
`MonoidAlgebra.mapDomainLinearMap` and `Rep.standardComplex.d_of` from pinned mathlib
`db584cd6d46c92f209a44c0f1c829460d327499d`; the two approved child declarations supply
the retraction and the prism homotopy. -/
theorem p04_tia_coh_restricted_standard_homotopy_equiv
    {k G : Type _} [CommRing k] [Group G] (H : Subgroup G) :
    Nonempty (HomotopyEquiv
      (((Rep.resFunctor H.subtype).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (Rep.standardComplex k G)) (Rep.standardComplex k H)) := by
  classical
  obtain ⟨r, hr, hrH⟩ := p04_rsh_82a013d1d0_equivariant_retraction H
  let C := ((Rep.resFunctor H.subtype).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj (Rep.standardComplex k G)
  let D := Rep.standardComplex k H
  -- Coordinatewise maps commute with every vertex deletion.
  have natural_d (L M : Type _) (f : L → M) (n : ℕ) :
      (Rep.standardComplex.d k M (n + 1)).comp
          (MonoidAlgebra.mapDomainLinearMap k k (fun c : Fin (n + 2) → L => f ∘ c)) =
        (MonoidAlgebra.mapDomainLinearMap k k (fun c : Fin (n + 1) → L => f ∘ c)).comp
          (Rep.standardComplex.d k L (n + 1)) := by
    apply MonoidAlgebra.lhom_ext'
    intro c
    apply LinearMap.ext_ring
    simp [Rep.standardComplex.d_of, Function.comp_assoc]
  let pF : ∀ n, C.X n ⟶ D.X n := fun n => Rep.ofHom
    { toLinearMap := MonoidAlgebra.mapDomainLinearMap k k
        (fun c : Fin (n + 1) → G => r ∘ c)
      isIntertwining' := by
        intro h
        apply MonoidAlgebra.lhom_ext'
        intro c
        apply LinearMap.ext_ring
        change MonoidAlgebra.mapDomainLinearMap k k (fun c => r ∘ c)
            (Representation.ofMulAction k G (Fin (n + 1) → G) (h : G)
              (MonoidAlgebra.single c 1)) =
          Representation.ofMulAction k H (Fin (n + 1) → H) h
            (MonoidAlgebra.mapDomainLinearMap k k (fun c => r ∘ c)
              (MonoidAlgebra.single c 1))
        simp only [Representation.ofMulAction_single,
          MonoidAlgebra.mapDomainLinearMap_single]
        congr 1
        funext i
        exact hr h (c i) }
  let qF : ∀ n, D.X n ⟶ C.X n := fun n => Rep.ofHom
    { toLinearMap := MonoidAlgebra.mapDomainLinearMap k k
        (fun c : Fin (n + 1) → H => H.subtype ∘ c)
      isIntertwining' := by
        intro h
        apply MonoidAlgebra.lhom_ext'
        intro c
        apply LinearMap.ext_ring
        change MonoidAlgebra.mapDomainLinearMap k k (fun c => H.subtype ∘ c)
            (Representation.ofMulAction k H (Fin (n + 1) → H) h
              (MonoidAlgebra.single c 1)) =
          Representation.ofMulAction k G (Fin (n + 1) → G) (h : G)
            (MonoidAlgebra.mapDomainLinearMap k k (fun c => H.subtype ∘ c)
              (MonoidAlgebra.single c 1))
        simp only [Representation.ofMulAction_single,
          MonoidAlgebra.mapDomainLinearMap_single]
        rfl }
  let p : C ⟶ D :=
    { f := pF
      comm' := by
        intro i j hij
        obtain rfl : j + 1 = i := hij
        apply Rep.hom_ext
        apply Representation.IntertwiningMap.ext
        apply LinearMap.ext
        intro x
        change ((Rep.standardComplex k H).d (j + 1) j).hom
            (MonoidAlgebra.mapDomainLinearMap k k (fun c => r ∘ c) x) =
          MonoidAlgebra.mapDomainLinearMap k k (fun c => r ∘ c)
            ((Rep.standardComplex k G).d (j + 1) j |>.hom x)
        rw [Rep.standardComplex.d_apply, Rep.standardComplex.d_apply]
        exact LinearMap.congr_fun (natural_d G H r j) x }
  let q : D ⟶ C :=
    { f := qF
      comm' := by
        intro i j hij
        obtain rfl : j + 1 = i := hij
        apply Rep.hom_ext
        apply Representation.IntertwiningMap.ext
        apply LinearMap.ext
        intro x
        change ((Rep.standardComplex k G).d (j + 1) j).hom
            (MonoidAlgebra.mapDomainLinearMap k k (fun c => H.subtype ∘ c) x) =
          MonoidAlgebra.mapDomainLinearMap k k (fun c => H.subtype ∘ c)
            ((Rep.standardComplex k H).d (j + 1) j |>.hom x)
        rw [Rep.standardComplex.d_apply, Rep.standardComplex.d_apply]
        exact LinearMap.congr_fun (natural_d H G H.subtype j) x }
  have hpq : q ≫ p = 𝟙 D := by
    apply HomologicalComplex.hom_ext
    intro n
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply MonoidAlgebra.lhom_ext'
    intro c
    apply LinearMap.ext_ring
    change MonoidAlgebra.mapDomainLinearMap k k (fun c => r ∘ c)
        (MonoidAlgebra.mapDomainLinearMap k k (fun c => H.subtype ∘ c)
          (MonoidAlgebra.single c 1)) = MonoidAlgebra.single c 1
    simp only [MonoidAlgebra.mapDomainLinearMap_single]
    congr 1
    funext i
    exact hrH (c i)
  obtain ⟨hp⟩ := p04_rsh_82a013d1d0_prism_homotopy (k := k) H
    id (fun g => (r g : G)) (fun _ _ => rfl)
    (fun h g => congrArg Subtype.val (hr h g)) (𝟙 C) (p ≫ q)
    (by intro n c; rfl)
    (by
      intro n c
      change MonoidAlgebra.mapDomainLinearMap k k (fun c => H.subtype ∘ c)
          (MonoidAlgebra.mapDomainLinearMap k k (fun c => r ∘ c)
            (MonoidAlgebra.single c 1)) = _
      simp only [MonoidAlgebra.mapDomainLinearMap_single]
      rfl)
  exact ⟨{ hom := p
           inv := q
           homotopyHomInvId := hp
           homotopyInvHomId := Homotopy.ofEq hpq }⟩
namespace Submission

set_option warningAsError true in
/-- Conjugating an `H`-equivariant morphism depends only on the left coset in `G ⧸ H`.
The proof uses `QuotientGroup.eq` to identify the subgroup element and
`Rep.hom_comm_apply` to cancel its action through the restricted morphism. -/

namespace Submission

set_option warningAsError true in
theorem p04_hca_bc7c754a4b_summand_eq_of_coset_eq
    {k G : Type _} [CommRing k] [Group G] (A B : Rep k G) (H : Subgroup G)
    (F : Quiver.Hom (Rep.res H.subtype B) (Rep.res H.subtype A)) (s t : G)
    (hst : (QuotientGroup.mk s : G ⧸ H) = QuotientGroup.mk t) (x : B) :
    A.ρ s (F.hom (B.ρ s⁻¹ x)) = A.ρ t (F.hom (B.ρ t⁻¹ x)) := by
  -- Equal left cosets differ by right multiplication by an element of H.
  let h : H := ⟨s⁻¹ * t, QuotientGroup.eq.mp hst⟩
  have ht : t = s * (h : G) := by simp [h]
  -- Equivariance moves the inverse subgroup action through F.
  have hF : F.hom (B.ρ (h : G)⁻¹ (B.ρ s⁻¹ x)) =
      A.ρ (h : G)⁻¹ (F.hom (B.ρ s⁻¹ x)) :=
    Rep.hom_comm_apply F h⁻¹ (B.ρ s⁻¹ x)
  -- Expand the product action, use equivariance, and cancel the inverse actions.
  let h : H := ⟨s⁻¹ * t, QuotientGroup.eq.mp hst⟩
  have ht : t = s * (h : G) := by simp [h]
  -- Equivariance moves the inverse subgroup action through F.
  have hF : F.hom (B.ρ (h : G)⁻¹ (B.ρ s⁻¹ x)) =
      A.ρ (h : G)⁻¹ (F.hom (B.ρ s⁻¹ x)) :=
    Rep.hom_comm_apply F h⁻¹ (B.ρ s⁻¹ x)
  rw [ht]
  simp only [mul_inv_rev, map_mul, Module.End.mul_apply]
  rw [hF, Representation.self_inv_apply]

end Submission
