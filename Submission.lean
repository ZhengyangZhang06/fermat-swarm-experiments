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

/-- An additive group is trivial if every prime is avoided by a positive global annihilator. -/
theorem p04_eq_zero_of_prime_avoiding_annihilators :
    ∀ {V : Type*} [AddCommGroup V],
      (∀ p : ℕ, p.Prime → ∃ m : ℕ, 0 < m ∧ ¬ p ∣ m ∧ ∀ v : V, m • v = 0) →
      ∀ v : V, v = 0 := by
  classical
  intro V _ h v
  obtain ⟨m₂, hm₂, _, h₂⟩ := h 2 Nat.prime_two
  have hex : ∃ n : ℕ, 0 < n ∧ n • v = 0 := ⟨m₂, hm₂, h₂ v⟩
  let n := Nat.find hex
  have hn_pos : 0 < n := (Nat.find_spec hex).1
  have hn_zero : n • v = 0 := (Nat.find_spec hex).2
  have hn_dvd : ∀ m : ℕ, m • v = 0 → n ∣ m := by
    intro m hm
    apply Nat.dvd_of_mod_eq_zero
    have hrem : (m % n) • v = 0 := by
      calc
        (m % n) • v = (m % n) • v + (m / n) • (n • v) := by
          rw [hn_zero, nsmul_zero, add_zero]
        _ = (m % n + n * (m / n)) • v := by
          rw [add_nsmul, mul_nsmul]
        _ = m • v := by rw [Nat.mod_add_div]
        _ = 0 := hm
    by_contra hrem_ne
    have hn_le : n ≤ m % n := Nat.find_min' hex ⟨Nat.pos_of_ne_zero hrem_ne, hrem⟩
    exact (Nat.not_le_of_gt (Nat.mod_lt m hn_pos)) hn_le
  have hn_one : n = 1 := by
    by_contra hn_ne
    obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd hn_ne
    obtain ⟨m, _, hpm, hm⟩ := h p hp
    exact hpm (hpn.trans (hn_dvd m (hm v)))
  simpa only [hn_one, one_smul] using hn_zero

end Submission
