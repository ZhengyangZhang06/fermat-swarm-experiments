/-
Copyright 2026 Anthropic, PBC. Licensed under Apache-2.0; see LICENSE.
Source: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_Rep_isZero_tateCohomology_of_forall_sylow.lean
Modified: replaced the proof with sorry and removed P2M proof imports.
Requires the upstream Definitions modules and their dependencies.
-/

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology

set_option autoImplicit false

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
