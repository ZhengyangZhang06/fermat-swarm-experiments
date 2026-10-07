/-
Copyright 2026 Anthropic, PBC. Licensed under Apache-2.0; see LICENSE.
Source: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_HeckeEis_eichlerShimuraMap_injective.lean
Modified: selected the modular pullback derivative node and removed P2M proof imports.
Requires the upstream Definitions modules and their dependencies.
-/

import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_HeckeEis_EichlerIntegral

set_option autoImplicit false

open scoped Manifold MatrixGroups ModularForm

namespace Submission

/-- Coefficientwise derivative of an Eichler integral after a modular substitution. -/
theorem p02_es_177ebb5a_cd_modular_pullback_derivative
    (N : ℕ) [NeZero N] (n : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) ((n : ℤ) + 2))
    (F : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n))
    (hF : HeckeEis.IsEichlerIntegral n (fun τ => f τ) F)
    (γ : CongruenceSubgroup.Gamma0 N) (e : Fin 2 →₀ ℕ) (τ : UpperHalfPlane) :
    HasDerivAt
      (fun z : ℂ => MvPolynomial.coeff e
        (F ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) • UpperHalfPlane.ofComplex z)).val)
      (f τ * MvPolynomial.coeff e
        ((((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype) γ)
          (HeckeEis.linePow n (τ : ℂ))).val)
      (τ : ℂ) := by
  let g : Matrix.SpecialLinearGroup (Fin 2) ℤ := γ
  have hj := HeckeEis.jFactor_ne_zero g τ
  have hT : HasDerivAt
      (fun z : ℂ => ((g • UpperHalfPlane.ofComplex z : UpperHalfPlane) : ℂ))
      (1 / HeckeEis.jFactor g τ ^ 2) (τ : ℂ) := by
    have hdet : (Matrix.SpecialLinearGroup.mapGL ℝ g).val.det = 1 :=
      (g.map (algebraMap ℤ ℝ)).det_coe
    simpa only [MulAction.compHom_smul_def, hdet, Complex.ofReal_one,
      ← HeckeEis.jFactor_eq_denom] using
      (UpperHalfPlane.hasStrictDerivAt_smul
        (g := Matrix.SpecialLinearGroup.mapGL ℝ g) (by rw [hdet]; exact zero_lt_one) τ).hasDerivAt
  have hcomp := (hF e (g • τ)).comp_of_eq (τ : ℂ) hT (by
    simp only [UpperHalfPlane.ofComplex_apply])
  have hslash : f (g • τ) = HeckeEis.jFactor g τ ^ (n + 2) * f τ := by
    have h := SlashInvariantForm.slash_action_eqn_SL'' (Γ := CongruenceSubgroup.Gamma0 N)
      f (γ := g) γ.property τ
    change f (g • τ) = UpperHalfPlane.denom (Matrix.SpecialLinearGroup.mapGL ℝ g)
      (τ : ℂ) ^ ((n : ℤ) + 2) * f τ at h
    rw [← HeckeEis.jFactor_eq_denom] at h
    simpa only [show (n : ℤ) + 2 = ((n + 2 : ℕ) : ℤ) by simp, zpow_natCast] using h
  have hrep : MvPolynomial.coeff e
      ((((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype) γ)
        (HeckeEis.linePow n (τ : ℂ))).val =
      HeckeEis.jFactor g τ ^ n *
        MvPolynomial.coeff e (HeckeEis.linePow n ((g • τ : UpperHalfPlane) : ℂ)).val := by
    change MvPolynomial.coeff e ((HeckeEis.binaryFormRepSL ℂ n g)
      (HeckeEis.linePow n (τ : ℂ))).val = _
    rw [HeckeEis.binaryFormRepSL_linePow]
    simp only [Submodule.coe_smul, MvPolynomial.coeff_smul, smul_eq_mul]
  have hscalar : (f (g • τ) *
      MvPolynomial.coeff e (HeckeEis.linePow n ((g • τ : UpperHalfPlane) : ℂ)).val) *
        (1 / HeckeEis.jFactor g τ ^ 2) =
      f τ * MvPolynomial.coeff e
        ((((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype) γ)
          (HeckeEis.linePow n (τ : ℂ))).val := by
    rw [hslash, hrep, pow_add]
    field_simp [hj]
  simpa only [Function.comp_def, UpperHalfPlane.ofComplex_apply, hscalar] using hcomp

end Submission
