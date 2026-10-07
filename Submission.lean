/-
Copyright 2026 Anthropic, PBC. Licensed under Apache-2.0; see LICENSE.
Source: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_Rep_isZero_tateCohomology_of_forall_sylow.lean
Modified: replaced the proof with sorry and removed P2M proof imports.
Requires the upstream Definitions modules and their dependencies.
-/

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology

set_option autoImplicit false
universe u
open CategoryTheory Rep
theorem Rep.isZero_tateCohomology_of_forall_sylow {k G : Type u} [CommRing k] [Group G] [Fintype G]
    (A : Rep.{u} k G) (q : ℤ)
    (h : ∀ (p : ℕ) [Fact p.Prime] (P : Sylow p G) [Fintype (P : Subgroup G)],
      CategoryTheory.Limits.IsZero ((Rep.res (P : Subgroup G).subtype A).tateCohomology q)) :
    CategoryTheory.Limits.IsZero (A.tateCohomology q) := by
  sorry

set_option maxHeartbeats 4000000

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

namespace Submission

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
  simp_rw [hleft, hright]
  rw [Fin.sum_univ_eq_sum_range (fun l =>
    MonoidAlgebra.single (T l) (1 : k) - MonoidAlgebra.single (T (l + 1)) (1 : k)),
    Finset.sum_range_sub', hzero, hlast]

end Submission
