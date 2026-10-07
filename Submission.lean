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

namespace Submission

theorem p04_hct139_coset_average_laws :
    ∀ {k G : Type _} [CommRing k] [Group G] [Fintype G]
      (A : Rep k G) (H : Subgroup G) [Fintype H] [Fintype (G ⧸ H)]
      (C : ∀ B : Rep k G,
        (Quiver.Hom (Rep.res H.subtype B) (Rep.res H.subtype A)) →ₗ[k] (Quiver.Hom B A)),
      (∀ (B : Rep k G)
        (F : Quiver.Hom (Rep.res H.subtype B) (Rep.res H.subtype A)) (x : B),
        (C B F).hom x = ∑ q : G ⧸ H, A.ρ q.out (F.hom (B.ρ q.out⁻¹ x))) →
      (∀ (B D : Rep k G) (f : Quiver.Hom D B)
        (F : Quiver.Hom (Rep.res H.subtype B) (Rep.res H.subtype A)),
        C D (CategoryTheory.CategoryStruct.comp ((Rep.resFunctor H.subtype).map f) F) =
          CategoryTheory.CategoryStruct.comp f (C B F)) ∧
      (∀ (B : Rep k G) (F : Quiver.Hom B A),
        C B ((Rep.resFunctor H.subtype).map F) = H.index • F) := by
  classical
  intro k G _ _ _ A H _ _ C hC
  constructor
  · intro B D f F
    ext x
    change (C D _).hom x = (C B F).hom (f.hom x)
    rw [hC, hC]
    change (∑ q : G ⧸ H, A.ρ q.out (F.hom (f.hom (D.ρ q.out⁻¹ x)))) =
      ∑ q : G ⧸ H, A.ρ q.out (F.hom (B.ρ q.out⁻¹ (f.hom x)))
    apply Finset.sum_congr rfl
    intro q _
    rw [Rep.hom_comm_apply]
  · intro B F
    ext x
    change (C B _).hom x = H.index • F.hom x
    rw [hC]
    change (∑ q : G ⧸ H, A.ρ q.out (F.hom (B.ρ q.out⁻¹ x))) = H.index • F.hom x
    simp [Rep.hom_comm_apply, Subgroup.index_eq_card, Nat.card_eq_fintype_card]

end Submission
