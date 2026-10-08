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

theorem p02_es_177ebb5a_pnf_primitive_kernel :
    ∀ M : Matrix (Fin 2) (Fin 2) ℤ, M.det = 0 →
      ∃ p q : ℤ, IsCoprime p q ∧ M.mulVec ![p, q] = 0 := by
  intro M hdet
  by_cases hM : M = 0
  · subst M
    exact ⟨1, 0, ⟨1, 0, by norm_num⟩, by simp⟩
  rw [Matrix.det_fin_two] at hdet
  -- A vector perpendicular to a nonzero row lies in the kernel when the determinant vanishes.
  obtain ⟨x, y, hxy, hker⟩ :
      ∃ x y : ℤ, (x ≠ 0 ∨ y ≠ 0) ∧
        ∀ i : Fin 2, M i 0 * x + M i 1 * y = 0 := by
    by_cases hrow : M 0 0 = 0 ∧ M 0 1 = 0
    · refine ⟨M 1 1, -M 1 0, ?_, ?_⟩
      · by_contra! h
        apply hM
        ext i j
        fin_cases i <;> fin_cases j <;> simp_all
      · intro i
        fin_cases i
        · simp [hrow.1, hrow.2]
        · change M 1 0 * M 1 1 + M 1 1 * (-M 1 0) = 0
          ring
    · refine ⟨M 0 1, -M 0 0, ?_, ?_⟩
      · simpa only [not_and_or, neg_ne_zero, or_comm] using hrow
      · intro i
        fin_cases i
        · change M 0 0 * M 0 1 + M 0 1 * (-M 0 0) = 0
          ring
        · change M 1 0 * M 0 1 + M 1 1 * (-M 0 0) = 0
          nlinarith [hdet]
  -- Dividing by the positive gcd gives coprime coordinates; cancel it in the kernel equations.
  have hg : 0 < Int.gcd x y := Int.gcd_pos_iff.mpr hxy
  obtain ⟨p, q, hpq, hx, hy⟩ := Int.exists_gcd_one hg
  refine ⟨p, q, Int.isCoprime_iff_gcd_eq_one.mpr hpq, ?_⟩
  have hg' : (Int.gcd x y : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hg)
  ext i
  simp only [Matrix.mulVec_apply_eq_sum, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Pi.zero_apply]
  apply (mul_eq_zero_iff_right hg').mp
  calc
    (M i 0 * p + M i 1 * q) * (Int.gcd x y : ℤ) =
        M i 0 * (p * (Int.gcd x y : ℤ)) + M i 1 * (q * (Int.gcd x y : ℤ)) := by
          rw [add_mul, mul_assoc, mul_assoc]
    _ = 0 := by rw [← hx, ← hy]; exact hker i
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

theorem p02_es_177ebb5a_pp_integral_parabolic_normal_form :
    ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      (γ : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4 →
      ∃ (σ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (m : ℤ),
        σ⁻¹ * γ * σ = ModularGroup.T ^ m ∨ σ⁻¹ * γ * σ = -(ModularGroup.T ^ m) := by
  intro γ htrace
  obtain ⟨ε, hε, htr⟩ :
      ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ γ.val.trace = 2 * ε := by
    have ht : γ.val.trace ^ 2 = (2 : ℤ) ^ 2 := by simpa using htrace
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp ht with ht | ht
    · exact ⟨1, Or.inl rfl, by simpa using ht⟩
    · exact ⟨-1, Or.inr rfl, by simpa using ht⟩
  have hεsq : ε ^ 2 = 1 := by rcases hε with rfl | rfl <;> norm_num
  -- The primitive-kernel dependency also handles the central case γ = εI.
  have hsing : (γ.val - ε • (1 : Matrix (Fin 2) (Fin 2) ℤ)).det = 0 := by
    have hdet := γ.property
    have htr' : γ.val 0 0 + γ.val 1 1 = 2 * ε := by
      simpa [Matrix.trace, Matrix.diag, Fin.sum_univ_two] using htr
    simp only [Matrix.det_fin_two] at hdet ⊢
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    norm_num
    nlinarith only [hdet, hεsq, congrArg (ε * ·) htr']
  obtain ⟨p, q, hpq, hker⟩ :=
    p02_es_177ebb5a_pnf_primitive_kernel _ hsing
  have heigen : γ.val.mulVec ![p, q] = ![ε * p, ε * q] := by
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hker
    simpa using hker
  obtain ⟨σ, b, hσ⟩ :=
    p02_es_177ebb5a_pnf_primitive_eigenvector_triangular γ ε p q hεsq hpq heigen
  rcases hε with rfl | rfl
  · refine ⟨σ, b, Or.inl ?_⟩
    apply Subtype.ext
    exact hσ.trans (ModularGroup.coe_T_zpow b).symm
  · refine ⟨σ, -b, Or.inr ?_⟩
    apply Subtype.ext
    change (σ⁻¹ * γ * σ).val = -((ModularGroup.T ^ (-b)).val)
    rw [hσ, ModularGroup.coe_T_zpow]
    ext i j
    fin_cases i <;> fin_cases j <;> simp

end Submission
