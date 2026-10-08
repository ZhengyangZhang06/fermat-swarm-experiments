/-
Copyright 2026 Anthropic, PBC. Licensed under Apache-2.0; see LICENSE.
Source: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_AlgebraicCurve_hasPrincipalDivisors_of_transcendental.lean
Modified: replaced the proof with sorry and removed P2M proof imports.
Requires the upstream Definitions modules and their dependencies.
-/

import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Quotient.Basic

namespace Submission

/-- Left and right multiplication by unit matrices preserve the cokernel up to linear equivalence. -/
theorem p06_9e0f5043ff_dmc_cokernel_units :
    ∀ (R : Type*) [CommRing R] (m : ℕ) (D P Q : Matrix (Fin m) (Fin m) R),
      IsUnit P → IsUnit Q →
        Nonempty (((Fin m → R) ⧸ LinearMap.range (Matrix.mulVecLin D)) ≃ₗ[R]
          ((Fin m → R) ⧸ LinearMap.range (Matrix.mulVecLin (P * D * Q)))) := by
  intro R _ m D P Q hP hQ
  let eP := Matrix.toLinearEquiv' P hP.invertible
  let eQ := Matrix.toLinearEquiv' Q hQ.invertible
  -- Descend P and its inverse to the quotients once P maps the two ranges onto each other.
  refine ⟨Submodule.Quotient.equiv _ _ eP ?_⟩
  -- P(range D) = range (P * D), and surjectivity of Q gives range (P * D * Q).
  change (LinearMap.range D.mulVecLin).map P.mulVecLin =
    LinearMap.range (P * D * Q).mulVecLin
  rw [← LinearMap.range_comp, ← Matrix.mulVecLin_mul, Matrix.mulVecLin_mul (P * D) Q]
  exact (LinearMap.range_comp_of_range_eq_top _ eQ.range).symm

end Submission
