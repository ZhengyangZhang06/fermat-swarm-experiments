/-
Copyright 2026 Anthropic, PBC. Licensed under Apache-2.0; see LICENSE.
Source: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_AlgebraicCurve_hasPrincipalDivisors_of_transcendental.lean
The frozen root statement is retained in Fermat. This module proves the selected
integer-order principal-ideal node using the upstream Definitions context.
-/

import Definitions.Def_AlgebraicCurve_PlacesOverDVR
namespace Submission

/-- An integer order characterizing subring membership makes every ideal principal. -/
theorem p06_9e0f5043ff_elp_principal_ideals_of_order :
    ∀ (F : Type*) [Field F] (A : Subring F) (ν : F → ℤ),
      (∀ f g : F, f ≠ 0 → g ≠ 0 → ν (f / g) = ν f - ν g) →
      (∀ f : F, f ≠ 0 → (f ∈ A ↔ 0 ≤ ν f)) → IsPrincipalIdealRing A := by
  intro F _ A ν hdiv hmem
  classical
  constructor
  intro I
  by_cases hI : I = ⊥
  · subst I
    infer_instance
  obtain ⟨z, hzI, hz⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  have hex : ∃ n : ℕ, ∃ h : A, h ∈ I ∧ (h : F) ≠ 0 ∧ (ν (h : F)).toNat = n :=
    ⟨_, z, hzI, fun h => hz (Subtype.ext h), rfl⟩
  obtain ⟨h, hhI, hh, hν⟩ := Nat.find_spec hex
  refine ⟨⟨h, le_antisymm ?_ ((Ideal.span_singleton_le_iff_mem I).mpr hhI)⟩⟩
  intro z hzI
  by_cases hz : (z : F) = 0
  · have hz' : z = 0 := Subtype.ext hz
    rw [hz']
    exact Ideal.zero_mem _
  have hh_nonneg : 0 ≤ ν (h : F) := (hmem _ hh).mp h.property
  have hz_nonneg : 0 ≤ ν (z : F) := (hmem _ hz).mp z.property
  have hmin : (ν (h : F)).toNat ≤ (ν (z : F)).toNat := by
    rw [hν]
    exact Nat.find_min' hex ⟨z, hzI, hz, rfl⟩
  have horder : ν (h : F) ≤ ν (z : F) := by omega
  have hquot : (z : F) / (h : F) ∈ A := by
    apply (hmem _ (div_ne_zero hz hh)).mpr
    rw [hdiv _ _ hz hh]
    exact sub_nonneg.mpr horder
  apply Ideal.mem_span_singleton'.mpr
  refine ⟨⟨(z : F) / (h : F), hquot⟩, ?_⟩
  apply Subtype.ext
  exact div_mul_cancel₀ _ hh

end Submission
