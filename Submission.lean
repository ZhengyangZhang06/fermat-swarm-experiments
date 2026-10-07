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

namespace Submission

theorem p04_eq_zero_of_prime_avoiding_annihilators :
    ∀ {V : Type*} [AddCommGroup V],
      (∀ p : ℕ, p.Prime → ∃ m : ℕ, 0 < m ∧ ¬ p ∣ m ∧ ∀ v : V, m • v = 0) →
      ∀ v : V, v = 0 := by
  intro V _ h v
  obtain ⟨m₂, hm₂, _, h₂⟩ := h 2 Nat.prime_two
  have hn : 0 < addOrderOf v :=
    (isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨m₂, hm₂, h₂ v⟩).addOrderOf_pos
  have hn_le : addOrderOf v ≤ 1 := by
    by_contra hn_le
    obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd (Nat.ne_of_gt (Nat.lt_of_not_ge hn_le))
    obtain ⟨m, _, hpm, hm⟩ := h p hp
    exact hpm (hpn.trans (addOrderOf_dvd_iff_nsmul_eq_zero.mpr (hm v)))
  exact AddMonoid.addOrderOf_eq_one_iff.mp (Nat.le_antisymm hn_le hn)

end Submission
