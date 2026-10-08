import Mathlib

set_option autoImplicit false

namespace Submission

/-- The subgroup coefficient in a right transversal containing `1` gives an equivariant retraction. -/
theorem p04_rsh_82a013d1d0_equivariant_retraction {G : Type*} [Group G] (H : Subgroup G) :
    ∃ r : G → H, (∀ (h : H) (g : G), r ((h : G) * g) = h * r g) ∧
      ∀ h : H, r (h : G) = h := by
  classical
  obtain ⟨T, hT, h1⟩ := H.exists_isComplement_right (1 : G)
  refine ⟨fun g => (hT.equiv g).1, ?_, ?_⟩
  · intro h g
    exact congrArg Prod.fst (hT.equiv_mul_left h g)
  · intro h
    exact hT.equiv_fst_eq_self_of_mem_of_one_mem h1 h.property

end Submission
