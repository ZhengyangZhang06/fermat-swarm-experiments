/-
Copyright 2026 Anthropic, PBC. Licensed under Apache-2.0; see LICENSE.
Source: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_CerednikDrinfeld_QM_RigidifiedPairClass_exists_ptR_eq.lean
Modified: isolated the selected precomposition naturality child theorem.
Requires the upstream Definitions modules and their dependencies.
-/

import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMFineModuliT
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneCharts
import Definitions.Def_CerednikDrinfeld_RigidifiedPairClassModel

set_option autoImplicit false

namespace Submission

/-- Repeated addition commutes with compatible precomposition of points.
The induction uses identity and multiplication naturality for the specified relative group law. -/
theorem p07_flp_nsmul_precomp_857cd4d38c :
    ∀ (R : Type) [CommRing R] (A W W' : AlgebraicGeometry.Scheme.{0})
      (f : Quiver.Hom A (AlgebraicGeometry.Spec (CommRingCat.of R)))
      (L : GoodReductionJacobian.RelativeGroupLaw R f)
      (t : Quiver.Hom W (AlgebraicGeometry.Spec (CommRingCat.of R)))
      (t' : Quiver.Hom W' (AlgebraicGeometry.Spec (CommRingCat.of R)))
      (ψ : Quiver.Hom W' W) (hψ : CategoryTheory.CategoryStruct.comp ψ t = t')
      (k : ℕ) (P : NeronModelInfra.SchemeHomOver t f),
      GoodReductionJacobian.schemeHomOverComp ψ hψ (CerednikDrinfeld.QM.nsmulPt L t k P) =
        CerednikDrinfeld.QM.nsmulPt L t' k (GoodReductionJacobian.schemeHomOverComp ψ hψ P) := by
  intro R _ A W W' f L t t' ψ hψ k P
  induction k with
  -- At zero, precomposition preserves the identity point.
  | zero => exact L.one_natural t t' ψ hψ
  | succ k ih =>
      -- The recursive step commutes with precomposition by multiplication naturality.
      simp only [CerednikDrinfeld.QM.nsmulPt, L.mul_natural, ih]

end Submission
