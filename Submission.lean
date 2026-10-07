/-
Copyright 2026 Anthropic, PBC. Licensed under Apache-2.0; see LICENSE.
Source: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_Rep_isZero_tateCohomology_of_forall_sylow.lean
Selected arithmetic child of the frozen Tate cohomology problem.
-/

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology

set_option autoImplicit false

namespace Submission

/-- An additive group is trivial if every prime is avoided by a positive global annihilator. -/
theorem p04_eq_zero_of_prime_avoiding_annihilators :
    ∀ {V : Type*} [AddCommGroup V],
      (∀ p : ℕ, p.Prime → ∃ m : ℕ, 0 < m ∧ ¬ p ∣ m ∧ ∀ v : V, m • v = 0) →
      ∀ v : V, v = 0 := by
  intro V _ h v
  obtain ⟨m₂, hm₂, _, h₂⟩ := h 2 Nat.prime_two
  have hv : IsOfFinAddOrder v :=
    isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨m₂, hm₂, h₂ v⟩
  have hn_le : addOrderOf v ≤ 1 := by
    by_contra! hn
    obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd (Nat.ne_of_gt hn)
    obtain ⟨m, _, hpm, hm⟩ := h p hp
    exact hpm (hpn.trans (addOrderOf_dvd_of_nsmul_eq_zero (hm v)))
  exact AddMonoid.addOrderOf_eq_one_iff.mp (Nat.le_antisymm hn_le hv.addOrderOf_pos)

end Submission
