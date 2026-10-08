/-
Copyright 2026 Anthropic, PBC. Licensed under Apache-2.0; see LICENSE.
Source: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_AlgebraicCurve_hasPrincipalDivisors_of_transcendental.lean
Modified: selected-node proof of compatible normalized-order invariance.
Requires the upstream Definitions modules and their dependencies.
-/

import Definitions.Def_AlgebraicCurve_PlacesOverDVR

namespace Submission

set_option warningAsError true in
/-- A compatible equivalence of valuation rings preserves normalized orders.

Transport a unit-times-uniformizer factorization through the two compatible equivalences,
then evaluate its normalized order in the target valuation ring. The factorization and
evaluation lemmas are `Place.exists_unit_mul_zpow` and `Place.ord_unit_smul_zpow`
from `Definitions.Def_AlgebraicCurve_DivisorClassGroup`. -/
theorem p06_9e0f5043ff_pae_compatible_order_invariance
    (K E L : Type*) [Field K] [Field E] [Field L] [Algebra K E] [Algebra K L]
    (e : E ≃ₐ[K] L) (v : AlgebraicCurve.Place K E) (w : AlgebraicCurve.Place K L)
    (r : v.toValuationSubring ≃ₐ[K] w.toValuationSubring)
    (hcompat : ∀ a : v.toValuationSubring, (r a : L) = e (a : E))
    (f : E) (hf : f ≠ 0) : w.ord (e f) = v.ord f := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  have hπ' : Irreducible (r π) := (MulEquiv.irreducible_iff r).mpr hπ
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  let u' : w.toValuationSubringˣ := Units.map r.toRingEquiv.toMonoidHom u
  have hcoeu : ((u' : w.toValuationSubring) : L) =
      e ((u : v.toValuationSubring) : E) := hcompat (u : v.toValuationSubring)
  have hfactor : e f = ((u' : w.toValuationSubring) : L) *
      ((r π : L) ^ v.ord f) := by
    rw [hcoeu, hcompat π]
    simpa only [map_mul, map_zpow₀] using congrArg e hu
  rw [hfactor, w.ord_unit_smul_zpow u' hπ' (v.ord f)]

end Submission
