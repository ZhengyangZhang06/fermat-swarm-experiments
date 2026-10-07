import Mathlib

set_option autoImplicit false

namespace Submission

open CategoryTheory

/-- The restricted standard resolution computes subgroup homology. -/
theorem p04_ht_restricted_standard_comparison
    {k G : Type _} [CommRing k] [Group G] [Fintype G]
    (A : Rep k G) (H : Subgroup G) [Fintype H] (n : ℕ) :
    Nonempty
      (((((Rep.resFunctor (k := k) H.subtype).mapHomologicalComplex
          (ComplexShape.down ℕ)).obj (Rep.standardComplex k G)).coinvariantsTensorObj
          (Rep.res H.subtype A)).homology n ≃ₗ[k]
        groupHomology (Rep.res H.subtype A) n) := by
  classical
  exact ⟨(groupHomologyIso (Rep.res H.subtype A) n
    ((Rep.resFunctor H.subtype).mapProjectiveResolution
      (Rep.standardResolution k G))).symm.toLinearEquiv⟩

end Submission
