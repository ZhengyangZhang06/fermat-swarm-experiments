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

theorem p02_es_177ebb5a_pnf_primitive_eigenvector_triangular :
    ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (ε p q : ℤ),
      ε ^ 2 = 1 → IsCoprime p q →
      (γ : Matrix (Fin 2) (Fin 2) ℤ).mulVec ![p, q] = ![ε * p, ε * q] →
      ∃ (σ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (b : ℤ),
        (σ⁻¹ * γ * σ : Matrix.SpecialLinearGroup (Fin 2) ℤ).val =
          Matrix.of ![![ε, b], ![0, ε]] := by
  intro γ ε p q hε hpq hγ
  obtain ⟨σ, hσ₀, hσ₁⟩ := hpq.exists_SL2_col 0
  have hσ : σ.val.mulVec ![1, 0] = ![p, q] := by
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hσ₀, hσ₁]
  have heigen : γ.val.mulVec ![p, q] = ε • ![p, q] := by
    simpa using hγ
  let δ := σ⁻¹ * γ * σ
  have hδ : δ.val.mulVec ![1, 0] = ε • ![1, 0] := by
    change ((σ⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℤ).val * γ.val * σ.val).mulVec
      ![1, 0] = ε • ![1, 0]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hσ, heigen,
      Matrix.mulVec_smul, ← hσ, Matrix.mulVec_mulVec,
      ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
  have hδ₀ : δ.val 0 0 = ε := by
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun hδ 0
  have hδ₁ : δ.val 1 0 = 0 := by
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun hδ 1
  have hdet : ε * δ.val 1 1 = 1 := by
    simpa only [Matrix.det_fin_two, hδ₀, hδ₁, mul_zero, sub_zero] using δ.property
  have hdiag : δ.val 1 1 = ε := by
    calc
      δ.val 1 1 = ε ^ 2 * δ.val 1 1 := by rw [hε, one_mul]
      _ = ε * (ε * δ.val 1 1) := by rw [pow_two, mul_assoc]
      _ = ε := by rw [hdet, mul_one]
  refine ⟨σ, δ.val 0 1, ?_⟩
  change δ.val = Matrix.of ![![ε, δ.val 0 1], ![0, ε]]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hδ₀, hδ₁, hdiag]

end Submission
