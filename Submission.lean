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

namespace Submission

/-- An additive group is trivial if every prime is avoided by a positive global annihilator.

For each element, its least positive annihilator divides every annihilator by Euclidean
division. A prime divisor of that least annihilator would contradict the hypothesis,
so the least annihilator is one and the element is zero.

The well-ordering step uses `Nat.find_spec` and `Nat.find_min` from
`Mathlib.Data.Nat.Find`. Euclidean division uses `nsmul_eq_mod_nsmul` from
`Mathlib.Algebra.Group.Basic`, and the prime divisor is supplied by
`Nat.exists_prime_and_dvd` from `Mathlib.Data.Nat.Prime.Defs`.
-/
theorem p04_eq_zero_of_prime_avoiding_annihilators :
    ∀ {V : Type*} [AddCommGroup V],
      (∀ p : ℕ, p.Prime → ∃ m : ℕ, 0 < m ∧ ¬ p ∣ m ∧ ∀ v : V, m • v = 0) →
      ∀ v : V, v = 0 := by
  intro V _ h v
  classical
  -- Choose the least positive annihilator of this element.
  obtain ⟨m₂, hm₂, _, h₂⟩ := h 2 Nat.prime_two
  have hex : ∃ n : ℕ, 0 < n ∧ n • v = 0 := ⟨m₂, hm₂, h₂ v⟩
  let n := Nat.find hex
  obtain ⟨hn_pos, hn_zero⟩ : 0 < n ∧ n • v = 0 := Nat.find_spec hex
  -- A nonzero remainder would be a smaller positive annihilator.
  have hn_dvd : ∀ m : ℕ, m • v = 0 → n ∣ m := by
    intro m hm
    apply Nat.dvd_of_mod_eq_zero
    by_contra hr
    have hr_zero : (m % n) • v = 0 := (nsmul_eq_mod_nsmul m hn_zero).symm.trans hm
    exact Nat.find_min hex (Nat.mod_lt m hn_pos) ⟨Nat.pos_of_ne_zero hr, hr_zero⟩
  -- Any prime divisor of n would divide its prime-avoiding annihilator.
  have hn_one : n = 1 := by
    by_contra hn
    obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd hn
    obtain ⟨m, _, hpm, hm⟩ := h p hp
    exact hpm (hpn.trans (hn_dvd m (hm v)))
  simpa only [hn_one, one_nsmul] using hn_zero

end Submission
