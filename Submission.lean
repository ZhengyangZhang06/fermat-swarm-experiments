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
theorem p02_es_177ebb5a_sm_slash :
    ∀ (n : ℕ) (E : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n))
      (σ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (τ : UpperHalfPlane),
      (SlashAction.map (-(n : ℤ)) σ (fun z : UpperHalfPlane =>
        MvPolynomial.eval (fun j : Fin 2 => if j = 0 then 1 else -(z : ℂ)) (E z).val)) τ =
      MvPolynomial.eval (fun j : Fin 2 => if j = 0 then 1 else -(τ : ℂ))
        (((HeckeEis.binaryFormRepSL ℂ n) σ⁻¹) (E (σ • τ))).val := by
  intro n E σ τ
  let R := HeckeEis.binaryFormRepSL ℂ n σ⁻¹ (E (σ • τ))
  let j : ℂ := UpperHalfPlane.denom σ τ
  have hj : j ≠ 0 := UpperHalfPlane.denom_ne_zero σ τ
  have hR : HeckeEis.binaryFormRepSL ℂ n σ R = E (σ • τ) := by
    change ((HeckeEis.binaryFormRepSL ℂ n σ) *
      (HeckeEis.binaryFormRepSL ℂ n σ⁻¹)) (E (σ • τ)) = _
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl
  have hdet : (σ 0 0 : ℂ) * (σ 1 1 : ℂ) - (σ 0 1 : ℂ) * (σ 1 0 : ℂ) = 1 := by
    exact_mod_cast (show σ 0 0 * σ 1 1 - σ 0 1 * σ 1 0 = 1 by
      simpa only [Matrix.det_fin_two] using σ.property)
  have hjdef : j = (σ 1 0 : ℂ) * (τ : ℂ) + (σ 1 1 : ℂ) := by
    simp [j, UpperHalfPlane.denom]
  have hw : ((σ • τ : UpperHalfPlane) : ℂ) =
      ((σ 0 0 : ℂ) * (τ : ℂ) + (σ 0 1 : ℂ)) / j := by
    simpa [hjdef] using UpperHalfPlane.coe_specialLinearGroup_apply σ τ
  have hcoords : (fun k : Fin 2 =>
      MvPolynomial.eval (fun i : Fin 2 => if i = 0 then 1 else -((σ • τ : UpperHalfPlane) : ℂ))
        (∑ i : Fin 2, MvPolynomial.C (σ i k : ℂ) * MvPolynomial.X i)) =
      j⁻¹ • (fun k : Fin 2 => if k = 0 then (1 : ℂ) else -(τ : ℂ)) := by
    rw [hw]
    funext k
    fin_cases k <;>
      simp [Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul] <;>
      field_simp [hj] <;> rw [hjdef]
    · linear_combination hdet
    · linear_combination -(τ : ℂ) * hdet
  have heval : MvPolynomial.eval
      (fun k : Fin 2 => if k = 0 then 1 else -((σ • τ : UpperHalfPlane) : ℂ))
      (E (σ • τ)).val = j⁻¹ ^ n *
      MvPolynomial.eval (fun k : Fin 2 => if k = 0 then 1 else -(τ : ℂ)) R.val := by
    rw [← hR, HeckeEis.binaryFormRepSL_apply_coe]
    change MvPolynomial.aeval _ (MvPolynomial.aeval _ R.val) = _
    rw [MvPolynomial.comp_aeval_apply]
    simp only [MvPolynomial.aeval_eq_eval]
    rw [hcoords, HeckeEis.eval_smul_of_isHomogeneous
      ((MvPolynomial.mem_homogeneousSubmodule _ _).mp R.property)]
  rw [ModularForm.SL_slash_apply, heval]
  simp only [neg_neg, zpow_natCast]
  change (j⁻¹ ^ n * _) * j ^ n = _
  rw [mul_right_comm, ← mul_pow, inv_mul_cancel₀ hj, one_pow, one_mul]

end Submission
