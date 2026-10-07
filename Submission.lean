/-
Copyright 2026 Anthropic, PBC. Licensed under Apache-2.0; see LICENSE.
Source: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_HeckeEis_eichlerShimuraMap_injective.lean
Modified: replaced the proof with sorry and removed P2M proof imports.
Requires the upstream Definitions modules and their dependencies.
-/

import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_HeckeEis_EichlerIntegral

set_option autoImplicit false

open scoped Manifold MatrixGroups ModularForm

theorem HeckeEis.eichlerShimuraMap_injective (N : ℕ) [NeZero N] (n : ℕ) :
    Function.Injective
      (fun f : CuspForm (CongruenceSubgroup.Gamma0 N) ((n : ℤ) + 2) ↦ HeckeEis.eichlerShimuraMap n N f) := by
  sorry

namespace Submission

theorem p02_es_177ebb5a_sm_holomorphic
    (n : ℕ) (h : UpperHalfPlane → ℂ)
    (E : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n))
    (hE : HeckeEis.IsEichlerIntegral n h E) :
    DifferentiableOn ℂ
      (fun z : ℂ => MvPolynomial.eval (fun j : Fin 2 => if j = 0 then 1 else -z)
        (E (UpperHalfPlane.ofComplex z)).val)
      {z : ℂ | 0 < z.im} := by
  classical
  let s := (Finsupp.finite_of_degree_eq (σ := Fin 2) n).toFinset
  have hexpand (z : ℂ) :
      MvPolynomial.eval (fun j : Fin 2 => if j = 0 then 1 else -z)
          (E (UpperHalfPlane.ofComplex z)).val =
        ∑ d ∈ s, MvPolynomial.coeff d (E (UpperHalfPlane.ofComplex z)).val *
          (-z) ^ d 1 := by
    rw [MvPolynomial.eval_eq']
    simp only [Fin.prod_univ_two, Fin.isValue, ite_true, one_pow, one_ne_zero,
      ite_false, one_mul]
    apply Finset.sum_subset
    · intro d hd
      have hdeg := (E (UpperHalfPlane.ofComplex z)).property
        (MvPolynomial.mem_support_iff.mp hd)
      simpa [s, Finsupp.degree_eq_weight_one, Pi.one_def] using hdeg
    · intro d _ hd
      simp [MvPolynomial.notMem_support_iff.mp hd]
  simp_rw [hexpand]
  apply DifferentiableOn.fun_sum
  intro d _
  apply DifferentiableOn.mul
  · intro z hz
    exact (hE d ⟨z, hz⟩).differentiableAt.differentiableWithinAt
  · exact (differentiable_id.neg.pow (d 1)).differentiableOn

theorem p02_es_177ebb5a_pcl_scaled_pullback_derivative :
    ∀ (n : ℕ) (f : UpperHalfPlane → ℂ)
      (F : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n)),
      HeckeEis.IsEichlerIntegral n f F →
      ∀ (σ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (d : Fin 2 →₀ ℕ)
        (τ : UpperHalfPlane),
        HasDerivAt (fun z : ℂ => MvPolynomial.coeff d
          (F (σ • UpperHalfPlane.ofComplex z)).val)
          ((HeckeEis.jFactor σ τ) ^ (-((n : ℤ) + 2)) * f (σ • τ) *
            MvPolynomial.coeff d ((HeckeEis.binaryFormRepSL ℂ n σ)
              (HeckeEis.linePow n (τ : ℂ))).val) (τ : ℂ) := by
  intro n f F hF σ d τ
  have hσ : HasDerivAt
      (fun z : ℂ => ((σ • UpperHalfPlane.ofComplex z : UpperHalfPlane) : ℂ))
      ((HeckeEis.jFactor σ τ) ^ (-2 : ℤ)) (τ : ℂ) := by
    simpa [HeckeEis.jFactor_eq_denom, zpow_neg, MulAction.compHom_smul_def,
      ← Int.cast_det] using
      (UpperHalfPlane.hasStrictDerivAt_smul
        (g := Matrix.SpecialLinearGroup.mapGL ℝ σ)
        (by simp [← Int.cast_det]) τ).hasDerivAt
  have houter : HasDerivAt
      (fun z : ℂ => MvPolynomial.coeff d (F (UpperHalfPlane.ofComplex z)).val)
      (f (σ • τ) * MvPolynomial.coeff d
        (HeckeEis.linePow n ((σ • τ : UpperHalfPlane) : ℂ)).val)
      ((σ • UpperHalfPlane.ofComplex (τ : ℂ) : UpperHalfPlane) : ℂ) := by
    simpa only [UpperHalfPlane.ofComplex_apply] using hF d (σ • τ)
  have hcomp := houter.comp (τ : ℂ) hσ
  simp only [Function.comp_def, UpperHalfPlane.ofComplex_apply] at hcomp
  apply hcomp.congr_deriv
  rw [HeckeEis.binaryFormRepSL_linePow, Submodule.coe_smul,
    MvPolynomial.coeff_smul, smul_eq_mul, ← zpow_natCast]
  have hp : (HeckeEis.jFactor σ τ) ^ (-((n : ℤ) + 2)) *
      (HeckeEis.jFactor σ τ) ^ (n : ℤ) =
      (HeckeEis.jFactor σ τ) ^ (-2 : ℤ) := by
    rw [← zpow_add₀ (HeckeEis.jFactor_ne_zero σ τ)]
    congr 1
    omega
  rw [← hp]
  ring

end Submission
