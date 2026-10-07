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

/-- Expand a homogeneous binary form in the monomials with exponents `(r, n - r)`. -/
theorem p02_es_177ebb5a_ic_lct_monomial_expansion
    (n : ℕ) (Q : ↥(HeckeEis.BinaryForm ℂ n)) :
    Q.val = ∑ r : Fin (n + 1),
      MvPolynomial.coeff (Finsupp.single (0 : Fin 2) r.val +
        Finsupp.single (1 : Fin 2) (n - r.val)) Q.val •
      MvPolynomial.monomial (Finsupp.single (0 : Fin 2) r.val +
        Finsupp.single (1 : Fin 2) (n - r.val)) (1 : ℂ) := by
  classical
  let exponent (r : Fin (n + 1)) : Fin 2 →₀ ℕ :=
    Finsupp.single 0 r.val + Finsupp.single 1 (n - r.val)
  have hdegree (r : Fin (n + 1)) : (exponent r).degree = n := by
    simp only [exponent, map_add, Finsupp.degree_single]
    exact Nat.add_sub_of_le (Nat.le_of_lt_succ r.isLt)
  apply MvPolynomial.ext
  intro d
  rw [MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_smul, MvPolynomial.coeff_monomial, smul_eq_mul]
  change MvPolynomial.coeff d Q.val = ∑ r : Fin (n + 1),
    MvPolynomial.coeff (exponent r) Q.val * (if exponent r = d then 1 else 0)
  by_cases hd : d.degree = n
  · have hd01 : d 0 + d 1 = n := by
      simpa only [Finsupp.degree_eq_sum, Fin.sum_univ_two] using hd
    let r₀ : Fin (n + 1) := ⟨d 0, by omega⟩
    have hr₀ : exponent r₀ = d := by
      ext i
      fin_cases i <;> simp [exponent, r₀]
      omega
    rw [Finset.sum_eq_single r₀]
    · simp [hr₀]
    · intro r _ hne
      have hrd : exponent r ≠ d := by
        intro h
        apply hne
        apply Fin.ext
        have h0 := congrArg (fun e : Fin 2 →₀ ℕ => e 0) h
        simpa [exponent, r₀] using h0
      simp [hrd]
    · simp
  · have hQ : MvPolynomial.coeff d Q.val = 0 :=
      MvPolynomial.IsHomogeneous.coeff_eq_zero Q.property hd
    rw [hQ]
    symm
    apply Finset.sum_eq_zero
    intro r _
    have hrd : exponent r ≠ d := by
      intro h
      exact hd (h ▸ hdegree r)
    simp [hrd]
theorem p02_es_177ebb5a_ic_lmd_scalar_pullback
    (h : UpperHalfPlane → ℂ) (v : ℂ)
    (σ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (τ : UpperHalfPlane)
    (hh : HasDerivAt (fun z : ℂ => h (UpperHalfPlane.ofComplex z)) v
      ((σ • τ : UpperHalfPlane) : ℂ)) :
    HasDerivAt (fun z : ℂ => h (σ • UpperHalfPlane.ofComplex z))
      (v / (HeckeEis.jFactor σ τ) ^ 2) (τ : ℂ) := by
  have hdet : (Matrix.SpecialLinearGroup.mapGL ℝ σ).val.det = 1 :=
    (Matrix.SpecialLinearGroup.map (algebraMap ℤ ℝ) σ).property
  have hσ : HasDerivAt
      (fun z : ℂ => ((σ • UpperHalfPlane.ofComplex z : UpperHalfPlane) : ℂ))
      (1 / (HeckeEis.jFactor σ τ) ^ 2) (τ : ℂ) := by
    simpa only [hdet, Complex.ofReal_one, ← HeckeEis.jFactor_eq_denom] using!
      (UpperHalfPlane.hasStrictDerivAt_smul
        (g := Matrix.SpecialLinearGroup.mapGL ℝ σ) (by rw [hdet]; exact zero_lt_one) τ).hasDerivAt
  simpa only [Function.comp_def, UpperHalfPlane.ofComplex_apply, mul_one_div] using
    hh.comp_of_eq (τ : ℂ) hσ (by simp only [UpperHalfPlane.ofComplex_apply])


end Submission

/-- Each output coefficient of a linear map is a fixed linear combination of input coefficients. -/
theorem Submission.p02_es_177ebb5a_ic_lct_coeff_linear_combination
    (n : ℕ) (A : ↥(HeckeEis.BinaryForm ℂ n) →ₗ[ℂ] ↥(HeckeEis.BinaryForm ℂ n))
    (e : Fin 2 →₀ ℕ) :
    ∃ c : Fin (n + 1) → ℂ, ∀ Q : ↥(HeckeEis.BinaryForm ℂ n),
      MvPolynomial.coeff e (A Q).val = ∑ r : Fin (n + 1), c r *
        MvPolynomial.coeff (Finsupp.single (0 : Fin 2) r.val +
          Finsupp.single (1 : Fin 2) (n - r.val)) Q.val := by
  classical
  let exponent (r : Fin (n + 1)) : Fin 2 →₀ ℕ :=
    Finsupp.single 0 r.val + Finsupp.single 1 (n - r.val)
  have hdegree (r : Fin (n + 1)) : (exponent r).degree = n := by
    simp only [exponent, map_add, Finsupp.degree_single]
    exact Nat.add_sub_of_le (Nat.le_of_lt_succ r.isLt)
  let b (r : Fin (n + 1)) : ↥(HeckeEis.BinaryForm ℂ n) :=
    ⟨MvPolynomial.monomial (exponent r) (1 : ℂ),
      MvPolynomial.isHomogeneous_monomial 1 (hdegree r)⟩
  refine ⟨fun r => MvPolynomial.coeff e (A (b r)).val, ?_⟩
  intro Q
  have hQ : Q = ∑ r : Fin (n + 1), MvPolynomial.coeff (exponent r) Q.val • b r := by
    apply Subtype.ext
    simpa [b, exponent] using Submission.p02_es_177ebb5a_ic_lct_monomial_expansion n Q
  let L : ↥(HeckeEis.BinaryForm ℂ n) →ₗ[ℂ] ℂ :=
    (MvPolynomial.lcoeff ℂ e).comp ((HeckeEis.BinaryForm ℂ n).subtype.comp A)
  change L Q = ∑ r : Fin (n + 1), L (b r) * MvPolynomial.coeff (exponent r) Q.val
  calc
    L Q = L (∑ r : Fin (n + 1), MvPolynomial.coeff (exponent r) Q.val • b r) :=
      congrArg L hQ
    _ = ∑ r : Fin (n + 1), L (b r) * MvPolynomial.coeff (exponent r) Q.val := by
      simp only [map_sum, map_smul, smul_eq_mul, mul_comm]

/-- A linear map of binary forms preserves coefficientwise derivatives. -/
theorem Submission.p02_es_177ebb5a_ic_lmd_linear_coeff
    (n : ℕ) (A : ↥(HeckeEis.BinaryForm ℂ n) →ₗ[ℂ] ↥(HeckeEis.BinaryForm ℂ n))
    (F : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n))
    (P : ↥(HeckeEis.BinaryForm ℂ n)) (τ : UpperHalfPlane) :
    (∀ d : Fin 2 →₀ ℕ,
      HasDerivAt (fun z : ℂ => MvPolynomial.coeff d (F (UpperHalfPlane.ofComplex z)).val)
        (MvPolynomial.coeff d P.val) (τ : ℂ)) →
    ∀ e : Fin 2 →₀ ℕ,
      HasDerivAt (fun z : ℂ => MvPolynomial.coeff e (A (F (UpperHalfPlane.ofComplex z))).val)
        (MvPolynomial.coeff e (A P).val) (τ : ℂ) := by
  intro h e
  obtain ⟨c, hc⟩ := Submission.p02_es_177ebb5a_ic_lct_coeff_linear_combination n A e
  simp_rw [hc]
  exact HasDerivAt.fun_sum fun r _ => (h _).const_mul (c r)

namespace Submission

theorem p02_es_177ebb5a_ic_linear_mobius_derivative
    (n : ℕ)
    (A : ↥(HeckeEis.BinaryForm ℂ n) →ₗ[ℂ] ↥(HeckeEis.BinaryForm ℂ n))
    (F : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n))
    (P : ↥(HeckeEis.BinaryForm ℂ n))
    (σ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (τ : UpperHalfPlane)
    (hF : ∀ d : Fin 2 →₀ ℕ,
      HasDerivAt (fun z : ℂ => MvPolynomial.coeff d (F (UpperHalfPlane.ofComplex z)).val)
        (MvPolynomial.coeff d P.val) ((σ • τ : UpperHalfPlane) : ℂ)) :
    ∀ e : Fin 2 →₀ ℕ,
      HasDerivAt
        (fun z : ℂ => MvPolynomial.coeff e (A (F (σ • UpperHalfPlane.ofComplex z))).val)
        (MvPolynomial.coeff e (A P).val / (HeckeEis.jFactor σ τ) ^ 2) (τ : ℂ) := by
  intro e
  exact p02_es_177ebb5a_ic_lmd_scalar_pullback
    (fun w => MvPolynomial.coeff e (A (F w)).val)
    (MvPolynomial.coeff e (A P).val) σ τ
    (Submission.p02_es_177ebb5a_ic_lmd_linear_coeff n A F P (σ • τ) hF e)
theorem p02_es_177ebb5a_ic_inverse_linepow
    (n : ℕ) (σ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (τ : UpperHalfPlane) :
    (HeckeEis.binaryFormRepSL ℂ n) σ⁻¹
        (HeckeEis.linePow n ((σ • τ : UpperHalfPlane) : ℂ)) =
      ((HeckeEis.jFactor σ τ) ^ n)⁻¹ • HeckeEis.linePow n (τ : ℂ) := by
  have h := congrArg ((HeckeEis.binaryFormRepSL ℂ n) σ⁻¹)
    (HeckeEis.binaryFormRepSL_linePow n σ τ)
  rw [Representation.inv_self_apply, map_smul] at h
  have hj := pow_ne_zero n (HeckeEis.jFactor_ne_zero σ τ)
  simpa only [smul_smul, inv_mul_cancel₀ hj, one_smul] using
    congrArg (fun v => ((HeckeEis.jFactor σ τ) ^ n)⁻¹ • v) h.symm

theorem p02_es_177ebb5a_sm_transformed_integral
    (n : ℕ) (h : UpperHalfPlane → ℂ)
    (E : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n))
    (σ : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (hE : HeckeEis.IsEichlerIntegral n h E) :
    HeckeEis.IsEichlerIntegral n (SlashAction.map ((n : ℤ) + 2) σ h)
      (fun τ : UpperHalfPlane =>
        ((HeckeEis.binaryFormRepSL ℂ n) σ⁻¹) (E (σ • τ))) := by
  intro e τ
  have hderiv := p02_es_177ebb5a_ic_linear_mobius_derivative n
    ((HeckeEis.binaryFormRepSL ℂ n) σ⁻¹) E
    (h (σ • τ) • HeckeEis.linePow n ((σ • τ : UpperHalfPlane) : ℂ)) σ τ
    (fun d => by
      simpa only [Submodule.coe_smul, MvPolynomial.coeff_smul, smul_eq_mul] using
        hE d (σ • τ)) e
  rw [map_smul, p02_es_177ebb5a_ic_inverse_linepow, Submodule.coe_smul,
    MvPolynomial.coeff_smul, Submodule.coe_smul, MvPolynomial.coeff_smul,
    smul_eq_mul, smul_eq_mul] at hderiv
  convert hderiv using 1
  have hdenom := HeckeEis.jFactor_eq_denom σ τ
  rw [Matrix.SpecialLinearGroup.mapGL, MonoidHom.comp_apply,
    show algebraMap ℤ ℝ = Int.castRingHom ℝ from rfl] at hdenom
  rw [ModularForm.SL_slash_apply, ← hdenom]
  rw [show (n : ℤ) + 2 = ((n + 2 : ℕ) : ℤ) by norm_cast,
    zpow_neg, zpow_natCast, pow_add, mul_inv_rev, div_eq_mul_inv]
  ring

open Filter MeasureTheory Set
open scoped Topology

/-- The polynomial-exponential weight has a finite nonnegative integral, controls its
translated interval integrals, and tends to zero at infinity. -/
theorem p02_es_177ebb5a_scl_polynomial_exp_tail :
    ∀ (n : ℕ) (a : ℝ), 0 < a →
      IntegrableOn (fun s : ℝ => (1 + s) ^ n * Real.exp (-a * s)) (Ioi 0) ∧
      0 ≤ (∫ s in Ioi (0 : ℝ), (1 + s) ^ n * Real.exp (-a * s)) ∧
      (∀ (y t : ℝ), 0 ≤ y → y ≤ t →
        (∫ s in y..t, (1 + s) ^ n * Real.exp (-a * s)) ≤
          (∫ s in Ioi (0 : ℝ), (1 + s) ^ n * Real.exp (-a * s)) *
            (1 + y) ^ n * Real.exp (-a * y)) ∧
      Tendsto (fun y : ℝ => (1 + y) ^ n * Real.exp (-a * y)) atTop (𝓝 0) := by
  intro n a ha
  -- Polynomial growth is dominated by every positive exponential rate.
  have hdecay (b : ℝ) (hb : 0 < b) :
      Tendsto (fun y : ℝ => (1 + y) ^ n * Real.exp (-b * y)) atTop (𝓝 0) := by
    -- Shift the library's polynomial/exponential ratio by 1 and cancel the shift by exp b.
    have h := ((isLittleO_pow_exp_pos_mul_atTop n hb).tendsto_div_nhds_zero.comp
      (tendsto_atTop_add_const_left atTop 1 tendsto_id)).mul_const (Real.exp b)
    simp only [zero_mul] at h
    convert h using 1
    ext y
    simp only [Function.comp_apply, id_eq]
    rw [div_eq_mul_inv, ← Real.exp_neg, mul_assoc, ← Real.exp_add]
    congr 2
    ring
  let w : ℝ → ℝ := fun s => (1 + s) ^ n * Real.exp (-a * s)
  have hw : Continuous w := by fun_prop
  have hw_nonneg (s : ℝ) (hs : 0 ≤ s) : 0 ≤ w s := by
    dsimp [w]
    positivity
  -- Comparison with the exponential of half the rate gives integrability.
  have hint : IntegrableOn w (Ioi 0) := by
    apply integrable_of_isBigO_exp_neg (half_pos ha) hw.continuousOn
    -- Dividing w by exp (-(a / 2) * s) leaves the same weight at the positive half-rate.
    apply Asymptotics.IsLittleO.isBigO
    apply Asymptotics.isLittleO_of_tendsto (fun x hx => (Real.exp_ne_zero _ hx).elim)
    convert hdecay (a / 2) (half_pos ha) using 1
    ext s
    dsimp [w]
    rw [div_eq_mul_inv, ← Real.exp_neg, mul_assoc, ← Real.exp_add]
    congr 2
    ring
  refine ⟨hint, setIntegral_nonneg measurableSet_Ioi (fun s hs => hw_nonneg s hs.le),
    ?_, hdecay a ha⟩
  intro y t hy hyt
  have hty : 0 ≤ t - y := sub_nonneg.mpr hyt
  -- Translation reduces the tail estimate to submultiplicativity on [0, ∞).
  have hsub (v : ℝ) (hv : 0 ≤ v) : w (y + v) ≤ w y * w v := by
    have hp : (1 + (y + v)) ^ n ≤ ((1 + y) * (1 + v)) ^ n :=
      pow_le_pow_left₀ (by positivity) (by nlinarith [mul_nonneg hy hv]) n
    dsimp [w]
    calc
      (1 + (y + v)) ^ n * Real.exp (-a * (y + v)) ≤
          ((1 + y) * (1 + v)) ^ n * Real.exp (-a * (y + v)) :=
        mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
      _ = ((1 + y) ^ n * Real.exp (-a * y)) *
          ((1 + v) ^ n * Real.exp (-a * v)) := by
        rw [mul_pow, show -a * (y + v) = -a * y + -a * v by ring, Real.exp_add]
        ring
  have hfinite : (∫ v in (0 : ℝ)..t - y, w v) ≤ ∫ v in Ioi (0 : ℝ), w v := by
    rw [intervalIntegral.integral_of_le hty]
    apply setIntegral_mono_set hint
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv using hw_nonneg v hv.le
    · exact Filter.Eventually.of_forall (fun v hv => hv.1)
  change (∫ s in y..t, w s) ≤ (∫ s in Ioi (0 : ℝ), w s) *
    (1 + y) ^ n * Real.exp (-a * y)
  calc
    (∫ s in y..t, w s) = ∫ v in (0 : ℝ)..t - y, w (y + v) := by
      rw [intervalIntegral.integral_comp_add_left]
      simp
    _ ≤ ∫ v in (0 : ℝ)..t - y, w y * w v := by
      apply intervalIntegral.integral_mono_on hty
        ((hw.comp (continuous_const.add continuous_id)).intervalIntegrable _ _)
        ((continuous_const.mul hw).intervalIntegrable _ _)
      intro v hv
      exact hsub v hv.1
    _ = w y * ∫ v in (0 : ℝ)..t - y, w v := intervalIntegral.integral_const_mul _ _
    _ ≤ w y * ∫ v in Ioi (0 : ℝ), w v :=
      mul_le_mul_of_nonneg_left hfinite (hw_nonneg y hy)
    _ = (∫ s in Ioi (0 : ℝ), w s) * (1 + y) ^ n * Real.exp (-a * y) := by
      dsimp [w]
      ring


end Submission

theorem Submission.p02_es_177ebb5a_ssl_segment_estimates :
    ∀ (F H : ℂ → ℂ) (w : ℝ → ℝ) (L y₀ : ℝ),
      0 ≤ L → 0 < y₀ → ContinuousOn H {z : ℂ | 0 < z.im} →
      (∀ z : ℂ, 0 < z.im → HasDerivAt F (H z) z) →
      ContinuousOn w (Set.Ici y₀) →
      (∀ z : ℂ, 0 ≤ z.re → z.re ≤ L → y₀ ≤ z.im → ‖H z‖ ≤ w z.im) →
      (∀ (x y t : ℝ), 0 ≤ x → x ≤ L → y₀ ≤ y → y ≤ t →
        ‖F ((x : ℂ) + (t : ℂ) * Complex.I) -
          F ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤ ∫ s in y..t, w s) ∧
      (∀ (x y : ℝ), 0 ≤ x → x ≤ L → y₀ ≤ y →
        ‖F ((x : ℂ) + (y : ℂ) * Complex.I) - F ((y : ℂ) * Complex.I)‖ ≤
          x * w y) := by
  intro F H w L y₀ _hL hy₀ hH hF hw hbound
  constructor
  · intro x y t hx hxL hy hyt
    have hpath : Continuous (fun s : ℝ => (x : ℂ) + (s : ℂ) * Complex.I) := by
      fun_prop
    have hupper (s : ℝ) (hs : s ∈ Set.uIcc y t) :
        0 < ((x : ℂ) + (s : ℂ) * Complex.I).im := by
      have hys : y ≤ s := (Set.uIcc_of_le hyt ▸ hs).1
      simpa using hy₀.trans_le (hy.trans hys)
    have hderiv (s : ℝ) (hs : s ∈ Set.uIcc y t) :
        HasDerivAt (fun u : ℝ => F ((x : ℂ) + (u : ℂ) * Complex.I))
          (H ((x : ℂ) + (s : ℂ) * Complex.I) * Complex.I) s := by
      have hp : HasDerivAt (fun z : ℂ => (x : ℂ) + z * Complex.I) Complex.I
          (s : ℂ) := by
        simpa using ((hasDerivAt_id (s : ℂ)).mul_const Complex.I).const_add (x : ℂ)
      exact ((hF _ (hupper s hs)).comp (s : ℂ) hp).comp_ofReal
    have hint : IntervalIntegrable
        (fun s : ℝ => H ((x : ℂ) + (s : ℂ) * Complex.I) * Complex.I)
        MeasureTheory.volume y t :=
      ((hH.comp hpath.continuousOn (fun s hs => hupper s hs)).mul_const
        Complex.I).intervalIntegrable
    rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
    apply intervalIntegral.norm_integral_le_of_norm_le hyt
    · apply Filter.Eventually.of_forall
      intro s hs
      have hys : y₀ ≤ s := hy.trans hs.1.le
      simpa using hbound ((x : ℂ) + (s : ℂ) * Complex.I)
        (by simpa using hx) (by simpa using hxL) (by simpa using hys)
    · apply (hw.mono ?_).intervalIntegrable
      intro s hs
      exact hy.trans (Set.uIcc_of_le hyt ▸ hs).1
  · intro x y hx hxL hy
    have hpath : Continuous (fun s : ℝ => (s : ℂ) + (y : ℂ) * Complex.I) := by
      fun_prop
    have hupper (s : ℝ) : 0 < ((s : ℂ) + (y : ℂ) * Complex.I).im := by
      simpa using hy₀.trans_le hy
    have hderiv (s : ℝ) (_hs : s ∈ Set.uIcc 0 x) :
        HasDerivAt (fun u : ℝ => F ((u : ℂ) + (y : ℂ) * Complex.I))
          (H ((s : ℂ) + (y : ℂ) * Complex.I)) s := by
      simpa only [mul_one] using!
        ((hF _ (hupper s)).comp (s : ℂ)
          ((hasDerivAt_id (s : ℂ)).add_const ((y : ℂ) * Complex.I))).comp_ofReal
    have hint : IntervalIntegrable
        (fun s : ℝ => H ((s : ℂ) + (y : ℂ) * Complex.I))
        MeasureTheory.volume 0 x :=
      (hH.comp hpath.continuousOn (fun s _ => hupper s)).intervalIntegrable
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
    simp only [Complex.ofReal_zero, zero_add] at hFTC
    rw [← hFTC]
    calc
      _ ≤ w y * |x - 0| := intervalIntegral.norm_integral_le_of_norm_le_const (by
        intro s hs
        have hs' : s ∈ Set.Ioc 0 x := Set.uIoc_of_le hx ▸ hs
        simpa using hbound ((s : ℂ) + (y : ℂ) * Complex.I)
          (by simpa using hs'.1.le) (by simpa using hs'.2.trans hxL)
          (by simpa using hy))
      _ = x * w y := by rw [sub_zero, abs_of_nonneg hx, mul_comm]

/-- A uniform coefficient bound for the homogeneous power `(z * X₀ + X₁) ^ n`. -/
theorem Submission.p02_es_177ebb5a_scl_linepow_coeff_bound :
    ∀ (n : ℕ) (z : ℂ) (d : Fin 2 →₀ ℕ),
      ‖MvPolynomial.coeff d (HeckeEis.linePow n z).val‖ ≤
        (2 : ℝ) ^ n * (max 1 ‖z‖) ^ n := by
  classical
  intro n z d
  have hsum : d.sum (fun _ m ↦ m) = d 0 + d 1 := by
    simp [Finsupp.sum_of_support_subset d (Finset.subset_univ d.support)]
  have hprod : d.prod (fun j m ↦ (if j = 0 then z else (1 : ℂ)) ^ m) =
      z ^ d 0 := by
    rw [d.prod_fintype _ (by simp)]
    simp
  have hmulti : d.multinomial = (d 0 + d 1).choose (d 0) := by
    rw [Finsupp.multinomial_eq_of_support_subset (Finset.subset_univ d.support),
      Finset.univ_fin2, Nat.binomial_eq_choose Fin.zero_ne_one]
  have hcoeff : MvPolynomial.coeff d (HeckeEis.linePow n z).val =
      if d 0 + d 1 = n then (n.choose (d 0) : ℂ) * z ^ d 0 else 0 := by
    have h := MvPolynomial.coeff_linearCombination_X_pow_of_fintype
      (fun j : Fin 2 ↦ if j = 0 then z else (1 : ℂ)) d n
    simp only [Fin.sum_univ_two, Fin.isValue, ite_true, one_ne_zero, ite_false,
      MvPolynomial.smul_eq_C_mul, map_one, one_mul] at h
    change MvPolynomial.coeff d
      ((MvPolynomial.C z * MvPolynomial.X 0 + MvPolynomial.X 1) ^ n) = _
    rw [h, hsum, hprod, hmulti]
    split_ifs with hd
    · rw [hd]
    · rfl
  rw [hcoeff]
  by_cases hd : d 0 + d 1 = n
  · rw [if_pos hd, norm_mul, Complex.norm_natCast, norm_pow]
    have hchoose : (n.choose (d 0) : ℝ) ≤ (2 : ℝ) ^ n := by
      exact_mod_cast Nat.choose_le_two_pow n (d 0)
    have hpow : ‖z‖ ^ d 0 ≤ (max 1 ‖z‖) ^ n := by
      exact (pow_le_pow_left₀ (norm_nonneg z) (le_max_right 1 ‖z‖) (d 0)).trans
        (pow_le_pow_right₀ (le_max_left 1 ‖z‖) (by omega))
    exact mul_le_mul hchoose hpow (pow_nonneg (norm_nonneg z) _) (by positivity)
  · rw [if_neg hd, norm_zero]
    positivity
theorem Submission.p02_es_177ebb5a_sd_jr_linepow_eval :
    ∀ (n r : ℕ), r ≤ n → ∀ t : ℂ,
      MvPolynomial.eval (fun j : Fin 2 => if j = 0 then 1 else -t)
        ((fun p : MvPolynomial (Fin 2) ℂ => MvPolynomial.pderiv (1 : Fin 2) p)^[r]
          (HeckeEis.linePow n t).val) =
        (if r = n then (Nat.factorial n : ℂ) else 0) := by
  intro n r hr t
  let L : MvPolynomial (Fin 2) ℂ := MvPolynomial.C t * MvPolynomial.X 0 +
    MvPolynomial.X 1
  have hD : MvPolynomial.pderiv (1 : Fin 2) L = 1 := by
    simp [L]
  -- Each derivative lowers the power and contributes the next descending factor.
  have hiter (s : ℕ) (hs : s ≤ n) :
      (fun p : MvPolynomial (Fin 2) ℂ => MvPolynomial.pderiv (1 : Fin 2) p)^[s]
        (L ^ n) = MvPolynomial.C (n.descFactorial s : ℂ) * L ^ (n - s) := by
    induction s with
    | zero => simp
    | succ s ih =>
      rw [Function.iterate_succ_apply', ih (by omega), MvPolynomial.pderiv_C_mul,
        MvPolynomial.pderiv_pow, hD, mul_one]
      simp only [Nat.descFactorial_succ, Nat.cast_mul, map_mul, map_natCast,
        Nat.sub_sub]
      ac_rfl
  have hEval : MvPolynomial.eval (fun j : Fin 2 => if j = 0 then 1 else -t) L = 0 := by
    simp [L]
  change MvPolynomial.eval _
    ((fun p : MvPolynomial (Fin 2) ℂ => MvPolynomial.pderiv (1 : Fin 2) p)^[r]
      (L ^ n)) = _
  rw [hiter r hr, map_mul, MvPolynomial.eval_C, map_pow, hEval]
  by_cases h : r = n
  · subst r
    simp [Nat.descFactorial_self]
  · have hnr : n - r ≠ 0 := by omega
    simp [h, zero_pow hnr]


theorem Submission.p02_es_177ebb5a_ssl_tail_limit :
    ∀ (f : ℝ → ℂ) (e : ℝ → ℝ) (y₀ : ℝ),
      Filter.Tendsto e Filter.atTop (nhds (0 : ℝ)) →
      (∀ (y t : ℝ), y₀ ≤ y → y ≤ t → ‖f t - f y‖ ≤ e y) →
      ∃ b : ℂ, Filter.Tendsto f Filter.atTop (nhds b) ∧
        ∀ y : ℝ, y₀ ≤ y → ‖f y - b‖ ≤ e y := by
  intro f e y₀ he hbound
  have hcauchy : CauchySeq f := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp (he.eventually (gt_mem_nhds hε))
    refine ⟨max y₀ T, ?_⟩
    intro s hs t ht
    have hsy : y₀ ≤ s := (le_max_left _ _).trans hs
    have hty : y₀ ≤ t := (le_max_left _ _).trans ht
    have hsT : T ≤ s := (le_max_right _ _).trans hs
    have htT : T ≤ t := (le_max_right _ _).trans ht
    rcases le_total s t with hst | hts
    · rw [dist_eq_norm, norm_sub_rev]
      exact (hbound s t hsy hst).trans_lt (hT s hsT)
    · rw [dist_eq_norm]
      exact (hbound t s hty hts).trans_lt (hT t htT)
  obtain ⟨b, hb⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨b, hb, ?_⟩
  intro y hy
  rw [norm_sub_rev]
  apply le_of_tendsto (hb.sub_const (f y)).norm
  exact (Filter.eventually_ge_atTop y).mono fun t ht => hbound y t hy ht

/-- A primitive whose derivative decays on a vertical strip has one common limit,
with the polynomial-exponential tail bound throughout the strip. -/
theorem Submission.p02_es_177ebb5a_scl_scalar_strip_limit :
    ∀ (n : ℕ) (a D L y₀ : ℝ) (F H : ℂ → ℂ),
      0 < a → 0 ≤ D → 0 ≤ L → 1 ≤ y₀ →
      ContinuousOn H {z : ℂ | 0 < z.im} →
      (∀ z : ℂ, 0 < z.im → HasDerivAt F (H z) z) →
      (∀ z : ℂ, 0 ≤ z.re → z.re ≤ L → y₀ ≤ z.im →
        ‖H z‖ ≤ D * (1 + z.im) ^ n * Real.exp (-a * z.im)) →
      ∃ b : ℂ, ∀ z : ℂ, 0 ≤ z.re → z.re ≤ L → y₀ ≤ z.im →
        ‖F z - b‖ ≤
          (D * (∫ s in Set.Ioi (0 : ℝ), (1 + s) ^ n * Real.exp (-a * s))) *
            (1 + z.im) ^ n * Real.exp (-a * z.im) := by
  intro n a D L y₀ F H ha hD hL hy₀ hH hF hbound
  let w : ℝ → ℝ := fun y => (1 + y) ^ n * Real.exp (-a * y)
  let J : ℝ := ∫ s in Set.Ioi (0 : ℝ), w s
  -- Keep the weight estimates local to the approved dependency boundary.
  -- Pinned mathlib: Pow/Asymptotics.isLittleO_pow_exp_pos_mul_atTop and
  -- Integral/ExpDecay.integrable_of_isBigO_exp_neg supply decay and integrability.
  have hdecay_rate (b : ℝ) (hb : 0 < b) :
      Filter.Tendsto (fun y : ℝ => (1 + y) ^ n * Real.exp (-b * y))
        Filter.atTop (nhds 0) := by
    have h := ((isLittleO_pow_exp_pos_mul_atTop n hb).tendsto_div_nhds_zero.comp
      (Filter.tendsto_atTop_add_const_left Filter.atTop 1 Filter.tendsto_id)).mul_const
        (Real.exp b)
    simp only [zero_mul] at h
    convert h using 1
    ext y
    simp only [Function.comp_apply, id_eq]
    rw [div_eq_mul_inv, ← Real.exp_neg, mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have hdecay := hdecay_rate a ha
  have hw_cont : Continuous w := by fun_prop
  have hw_nonneg (s : ℝ) (hs : 0 ≤ s) : 0 ≤ w s := by
    dsimp [w]
    positivity
  have hint : MeasureTheory.IntegrableOn w (Set.Ioi 0) := by
    apply integrable_of_isBigO_exp_neg (half_pos ha) hw_cont.continuousOn
    apply Asymptotics.IsLittleO.isBigO
    apply Asymptotics.isLittleO_of_tendsto (fun x hx => (Real.exp_ne_zero _ hx).elim)
    convert hdecay_rate (a / 2) (half_pos ha) using 1
    ext s
    dsimp [w]
    rw [div_eq_mul_inv, ← Real.exp_neg, mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have htail (y t : ℝ) (hy : 0 ≤ y) (hyt : y ≤ t) :
      (∫ s in y..t, w s) ≤ J * w y := by
    have hty : 0 ≤ t - y := sub_nonneg.mpr hyt
    have hsub (v : ℝ) (hv : 0 ≤ v) : w (y + v) ≤ w y * w v := by
      have hp : (1 + (y + v)) ^ n ≤ ((1 + y) * (1 + v)) ^ n :=
        pow_le_pow_left₀ (by positivity) (by nlinarith [mul_nonneg hy hv]) n
      dsimp [w]
      calc
        (1 + (y + v)) ^ n * Real.exp (-a * (y + v)) ≤
            ((1 + y) * (1 + v)) ^ n * Real.exp (-a * (y + v)) :=
          mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
        _ = ((1 + y) ^ n * Real.exp (-a * y)) *
            ((1 + v) ^ n * Real.exp (-a * v)) := by
          rw [mul_pow, show -a * (y + v) = -a * y + -a * v by ring, Real.exp_add]
          ring
    have hfinite : (∫ v in (0 : ℝ)..t - y, w v) ≤ J := by
      rw [intervalIntegral.integral_of_le hty]
      apply MeasureTheory.setIntegral_mono_set hint
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with v hv
        exact hw_nonneg v hv.le
      · exact Filter.Eventually.of_forall (fun v hv => hv.1)
    calc
      (∫ s in y..t, w s) = ∫ v in (0 : ℝ)..t - y, w (y + v) := by
        rw [intervalIntegral.integral_comp_add_left]
        simp
      _ ≤ ∫ v in (0 : ℝ)..t - y, w y * w v := by
        apply intervalIntegral.integral_mono_on hty
          ((hw_cont.comp (continuous_const.add continuous_id)).intervalIntegrable _ _)
          ((continuous_const.mul hw_cont).intervalIntegrable _ _)
        intro v hv
        exact hsub v hv.1
      _ = w y * ∫ v in (0 : ℝ)..t - y, w v := intervalIntegral.integral_const_mul _ _
      _ ≤ w y * J := mul_le_mul_of_nonneg_left hfinite (hw_nonneg y hy)
      _ = J * w y := mul_comm _ _
  have hw : Continuous (fun y => D * w y) := continuous_const.mul hw_cont
  obtain ⟨hvertical, hhorizontal⟩ :=
    Submission.p02_es_177ebb5a_ssl_segment_estimates F H (fun y => D * w y) L y₀
      hL (by linarith) hH hF hw.continuousOn (by
        intro z hx hxL hy
        simpa only [w, mul_assoc] using hbound z hx hxL hy)
  have herror : Filter.Tendsto (fun y => (D * J) * w y) Filter.atTop (nhds 0) := by
    simpa only [mul_zero] using hdecay.const_mul (D * J)
  -- The vertical segment estimate gives a limit and its tail bound on each vertical line.
  have hlimit (x : ℝ) (hx : 0 ≤ x) (hxL : x ≤ L) :
      ∃ b : ℂ,
        Filter.Tendsto (fun y : ℝ => F ((x : ℂ) + (y : ℂ) * Complex.I))
          Filter.atTop (nhds b) ∧
        ∀ y : ℝ, y₀ ≤ y →
          ‖F ((x : ℂ) + (y : ℂ) * Complex.I) - b‖ ≤ (D * J) * w y := by
    apply Submission.p02_es_177ebb5a_ssl_tail_limit _ _ y₀ herror
    intro y t hy hyt
    calc
      ‖F ((x : ℂ) + (t : ℂ) * Complex.I) -
          F ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤
          ∫ s in y..t, D * w s := hvertical x y t hx hxL hy hyt
      _ = D * ∫ s in y..t, w s := intervalIntegral.integral_const_mul _ _
      _ ≤ D * (J * w y) :=
        mul_le_mul_of_nonneg_left (htail y t (by linarith) hyt) hD
      _ = (D * J) * w y := (mul_assoc _ _ _).symm
  obtain ⟨b, hb, _⟩ := hlimit 0 le_rfl hL
  refine ⟨b, ?_⟩
  intro z hx hxL hy
  obtain ⟨bx, hbx, hbx_bound⟩ := hlimit z.re hx hxL
  -- Horizontal differences vanish, so every vertical limit agrees with that at x = 0.
  have hbzero : Filter.Tendsto (fun y : ℝ => F ((y : ℂ) * Complex.I))
      Filter.atTop (nhds b) := by simpa only [Complex.ofReal_zero, zero_add] using hb
  have hhorizontal_decay : Filter.Tendsto (fun y => z.re * (D * w y))
      Filter.atTop (nhds 0) := by
    simpa only [mul_zero] using (hdecay.const_mul D).const_mul z.re
  have hnorm : ‖bx - b‖ ≤ 0 :=
    le_of_tendsto_of_tendsto (hbx.sub hbzero).norm hhorizontal_decay
      ((Filter.eventually_ge_atTop y₀).mono fun y hy => hhorizontal z.re y hx hxL hy)
  have heq : bx = b := sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hnorm (norm_nonneg _)))
  have hz := hbx_bound z.im hy
  rw [heq, Complex.re_add_im] at hz
  simpa only [w, J, mul_assoc] using hz

namespace Submission

/-- The coefficients of an Eichler integral have a common limit on a finite strip,
with a uniform polynomial-exponential error bound. -/
theorem p02_es_177ebb5a_tb_strip_coefficient_limit :
    ∀ (n : ℕ) (u : UpperHalfPlane → ℂ)
      (G : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n)) (a C Y L : ℝ),
      0 < a → 0 ≤ C → 0 ≤ L → Continuous u → HeckeEis.IsEichlerIntegral n u G →
      (∀ τ : UpperHalfPlane, Y ≤ τ.im → ‖u τ‖ ≤ C * Real.exp (-a * τ.im)) →
      ∃ (A : ↥(HeckeEis.BinaryForm ℂ n)) (K : ℝ), 0 ≤ K ∧
        ∀ τ : UpperHalfPlane, 0 ≤ τ.re → τ.re ≤ L → max 1 Y ≤ τ.im →
          ∀ d : Fin 2 →₀ ℕ,
            ‖MvPolynomial.coeff d ((G τ).val - A.val)‖ ≤
              K * (1 + τ.im) ^ n * Real.exp (-a * τ.im) := by
  classical
  intro n u G a C Y L ha hC hL hu hG hubound
  let D := C * (2 : ℝ) ^ n * (L + 1) ^ n
  let J := ∫ s in Set.Ioi (0 : ℝ), (1 + s) ^ n * Real.exp (-a * s)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hJ : 0 ≤ J := (p02_es_177ebb5a_scl_polynomial_exp_tail n a ha).2.1
  -- Each coefficient of the line power is a scalar polynomial in z.
  have hline_cont (d : Fin 2 →₀ ℕ) :
      Continuous (fun z : ℂ => MvPolynomial.coeff d (HeckeEis.linePow n z).val) := by
    have hformula (z : ℂ) :
        MvPolynomial.coeff d (HeckeEis.linePow n z).val =
          if d.sum (fun _ m ↦ m) = n then (d.multinomial : ℂ) * z ^ d 0 else 0 := by
      have h := MvPolynomial.coeff_linearCombination_X_pow_of_fintype
        (fun j : Fin 2 ↦ if j = 0 then z else (1 : ℂ)) d n
      simp only [Fin.sum_univ_two, Fin.isValue, ite_true, one_ne_zero, ite_false,
        MvPolynomial.smul_eq_C_mul, map_one, one_mul] at h
      change MvPolynomial.coeff d
        ((MvPolynomial.C z * MvPolynomial.X 0 + MvPolynomial.X 1) ^ n) = _
      rw [h, d.prod_fintype _ (by simp)]
      simp
    simp_rw [hformula]
    split_ifs <;> fun_prop
  -- Apply the scalar strip theorem with the same majorant for every coefficient.
  have hscalar (d : Fin 2 →₀ ℕ) : ∃ b : ℂ,
      ∀ z : ℂ, 0 ≤ z.re → z.re ≤ L → max 1 Y ≤ z.im →
        ‖MvPolynomial.coeff d (G (UpperHalfPlane.ofComplex z)).val - b‖ ≤
          (D * J) * (1 + z.im) ^ n * Real.exp (-a * z.im) := by
    apply p02_es_177ebb5a_scl_scalar_strip_limit n a D L (max 1 Y)
      (fun z => MvPolynomial.coeff d (G (UpperHalfPlane.ofComplex z)).val)
      (fun z => u (UpperHalfPlane.ofComplex z) *
        MvPolynomial.coeff d (HeckeEis.linePow n z).val)
      ha hD hL (le_max_left 1 Y)
    · intro z hz
      exact ((hu.continuousAt.comp
        (UpperHalfPlane.mdifferentiableAt_ofComplex hz).continuousAt).mul
          (hline_cont d).continuousAt).continuousWithinAt
    · intro z hz
      simpa only [UpperHalfPlane.ofComplex_apply_of_im_pos hz] using hG d ⟨z, hz⟩
    · intro z hx hxL hy
      have hy1 : 1 ≤ z.im := (le_max_left 1 Y).trans hy
      have hy0 : 0 ≤ z.im := by linarith
      have hz : 0 < z.im := by linarith
      have hum : ‖u (UpperHalfPlane.ofComplex z)‖ ≤ C * Real.exp (-a * z.im) := by
        simpa only [UpperHalfPlane.ofComplex_apply_of_im_pos hz, UpperHalfPlane.im] using
          hubound ⟨z, hz⟩ ((le_max_right 1 Y).trans hy)
      have hnorm : max 1 ‖z‖ ≤ (L + 1) * (1 + z.im) := by
        apply max_le
        · nlinarith [mul_nonneg hL hy0]
        · have hzbound := Complex.norm_le_abs_re_add_abs_im z
          rw [abs_of_nonneg hx, abs_of_nonneg hy0] at hzbound
          nlinarith [mul_nonneg hL hy0]
      calc
        ‖u (UpperHalfPlane.ofComplex z) *
            MvPolynomial.coeff d (HeckeEis.linePow n z).val‖ =
            ‖u (UpperHalfPlane.ofComplex z)‖ *
              ‖MvPolynomial.coeff d (HeckeEis.linePow n z).val‖ := norm_mul _ _
        _ ≤ (C * Real.exp (-a * z.im)) * ((2 : ℝ) ^ n * (max 1 ‖z‖) ^ n) :=
          mul_le_mul hum (p02_es_177ebb5a_scl_linepow_coeff_bound n z d)
            (norm_nonneg _) (by positivity)
        _ ≤ (C * Real.exp (-a * z.im)) *
            ((2 : ℝ) ^ n * ((L + 1) * (1 + z.im)) ^ n) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀ (by positivity) hnorm n) (by positivity)) (by positivity)
        _ = D * (1 + z.im) ^ n * Real.exp (-a * z.im) := by
          dsimp [D]
          rw [mul_pow]
          ring
  choose b hb using hscalar
  -- Only degree-n exponents are used in the limiting homogeneous polynomial.
  let s := (Finsupp.finite_of_degree_eq (σ := Fin 2) n).toFinset
  have hs (d : Fin 2 →₀ ℕ) : d ∈ s ↔ d.degree = n := by simp [s]
  let A : ↥(HeckeEis.BinaryForm ℂ n) :=
    ⟨∑ d ∈ s, MvPolynomial.monomial d (b d), by
      apply MvPolynomial.IsHomogeneous.sum
      intro d hd
      exact MvPolynomial.isHomogeneous_monomial (b d) ((hs d).mp hd)⟩
  have hA (d : Fin 2 →₀ ℕ) (hd : d ∈ s) : MvPolynomial.coeff d A.val = b d := by
    simp [A, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, hd]
  refine ⟨A, D * J, mul_nonneg hD hJ, ?_⟩
  intro τ hx hxL hy d
  rw [MvPolynomial.coeff_sub]
  by_cases hd : d ∈ s
  · rw [hA d hd]
    simpa only [UpperHalfPlane.ofComplex_apply, UpperHalfPlane.im] using
      hb d (τ : ℂ) hx hxL hy
  · have hdeg : d.degree ≠ n := by simpa only [hs d] using hd
    rw [(G τ).property.coeff_eq_zero hdeg, A.property.coeff_eq_zero hdeg,
      sub_self, norm_zero]
    have hy0 : 0 ≤ τ.im := τ.im_pos.le
    positivity
/-- A complex polynomial fixed by a nonzero translation is constant.
For positive degree `d + 1`, its `d`th Hasse derivative is linear; the Taylor
coefficient identity makes translation invariance contradict its nonzero slope. -/
theorem p02_es_177ebb5a_tff_periodic_polynomial_constant
    (p : Polynomial ℂ) (c : ℂ) (hc : c ≠ 0)
    (hperiod : p.comp (Polynomial.X + Polynomial.C c) = p) :
    p = Polynomial.C (p.coeff 0) := by
  apply Polynomial.eq_C_of_natDegree_eq_zero
  by_contra hdegree
  obtain ⟨d, hd⟩ := Nat.exists_eq_succ_of_ne_zero hdegree
  have hp : p ≠ 0 := Polynomial.ne_zero_of_natDegree_gt (Nat.pos_of_ne_zero hdegree)
  have hlinear : (Polynomial.hasseDeriv d p).natDegree ≤ 1 := by
    simpa [hd] using Polynomial.natDegree_hasseDeriv_le p d
  -- The degree-d coefficient of the translate is (d + 1) * p.coeff (d + 1) * c
  -- plus p.coeff d; invariance forces the first summand to vanish.
  have hcoeff := congrArg (fun q : Polynomial ℂ => q.coeff d) hperiod
  rw [← Polynomial.taylor_apply, Polynomial.taylor_coeff,
    Polynomial.eq_X_add_C_of_natDegree_le_one hlinear] at hcoeff
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.hasseDeriv_coeff, Nat.zero_add, Nat.choose_self,
    Nat.cast_one, one_mul, Nat.add_comm 1 d, Nat.choose_succ_self_right] at hcoeff
  have hlead : p.coeff (d + 1) ≠ 0 := by
    simpa only [Polynomial.leadingCoeff, hd, Nat.succ_eq_add_one] using
      Polynomial.leadingCoeff_ne_zero.mpr hp
  have hcast : ((d + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero d)
  exact (mul_ne_zero (mul_ne_zero hcast hlead) hc)
    (add_right_cancel (hcoeff.trans (zero_add _).symm))
theorem p02_es_177ebb5a_tff_constant_dehomogenization
    (n : ℕ) (A : ↥(HeckeEis.BinaryForm ℂ n)) (α : ℂ)
    (hA : MvPolynomial.eval₂ Polynomial.C
      (fun j : Fin 2 => if j = 0 then 1 else Polynomial.X) A.val = Polynomial.C α) :
    A.val = MvPolynomial.C α * MvPolynomial.X (0 : Fin 2) ^ n := by
  classical
  have hdegree (d : Fin 2 →₀ ℕ) (hd : d ∈ A.val.support) : d 0 + d 1 = n := by
    simpa only [← Finsupp.degree_apply, Finsupp.degree_eq_sum, Fin.sum_univ_two] using
      (A.property.degree_eq_sum_deg_support hd).symm
  -- At fixed total degree, the exponent of X₁ uniquely determines the monomial.
  have hcoeff (d : Fin 2 →₀ ℕ) (hd : d 0 + d 1 = n) :
      (MvPolynomial.eval₂ Polynomial.C
        (fun j : Fin 2 => if j = 0 then 1 else Polynomial.X) A.val).coeff (d 1) =
        MvPolynomial.coeff d A.val := by
    rw [MvPolynomial.eval₂_eq']
    simp only [Fin.prod_univ_two, Fin.isValue, ite_true, one_pow, one_ne_zero,
      ite_false, one_mul, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single d]
    · simp
    · intro e he hne
      have hedeg := hdegree e he
      have hne1 : d 1 ≠ e 1 := by
        intro he1
        apply hne
        have he0 : e 0 = d 0 := by omega
        ext j
        fin_cases j
        · exact he0
        · exact he1.symm
      simp [hne1]
    · intro hnot
      simp [MvPolynomial.notMem_support_iff.mp hnot]
  apply MvPolynomial.ext
  intro d
  by_cases hd : d 0 + d 1 = n
  · have hc := hcoeff d hd
    rw [hA, Polynomial.coeff_C] at hc
    rw [← hc, MvPolynomial.C_mul_X_pow_eq_monomial, MvPolynomial.coeff_monomial]
    have heq : Finsupp.single (0 : Fin 2) n = d ↔ d 1 = 0 := by
      constructor
      · intro h
        rw [← h]
        simp
      · intro h
        ext j
        fin_cases j <;> simp at * <;> omega
    simp only [heq]
  · rw [A.property.coeff_eq_zero, (MvPolynomial.isHomogeneous_C_mul_X_pow α
      (0 : Fin 2) n).coeff_eq_zero]
    all_goals simpa [Finsupp.degree_eq_sum, Fin.sum_univ_two] using hd

/-- A homogeneous binary form fixed by a nonzero integral translation is a power of X₀. -/
theorem p02_es_177ebb5a_tb_fixed_form
    (N : ℕ) [NeZero N] (n : ℕ) (A : ↥(HeckeEis.BinaryForm ℂ n))
    (hA : HeckeEis.binaryFormRepSL ℂ n (ModularGroup.T ^ N) A = A) :
    ∃ α : ℂ, A.val = MvPolynomial.C α * MvPolynomial.X (0 : Fin 2) ^ n := by
  classical
  let d : MvPolynomial (Fin 2) ℂ →+* Polynomial ℂ :=
    MvPolynomial.eval₂Hom Polynomial.C (fun j => if j = 0 then 1 else Polynomial.X)
  let t := Polynomial.compRingHom (Polynomial.X + Polynomial.C (N : ℂ))
  have hmatrix : ((ModularGroup.T ^ N : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      !![1, (N : ℤ); 0, 1] := by
    simpa only [zpow_natCast] using ModularGroup.coe_T_zpow (N : ℤ)
  -- Dehomogenizing the column substitution is translation of the univariate polynomial.
  have hcomm : d.comp (HeckeEis.binarySubst ℂ (ModularGroup.T ^ N : SL(2, ℤ))).toRingHom =
      t.comp d := by
    apply MvPolynomial.ringHom_ext
    · intro a
      change d (HeckeEis.binarySubst ℂ (ModularGroup.T ^ N : SL(2, ℤ)) (MvPolynomial.C a)) =
        t (d (MvPolynomial.C a))
      rw [HeckeEis.binarySubst_C]
      simp [d, t]
    · intro a
      change d (HeckeEis.binarySubst ℂ (ModularGroup.T ^ N : SL(2, ℤ)) (MvPolynomial.X a)) =
        t (d (MvPolynomial.X a))
      rw [HeckeEis.binarySubst_X, hmatrix]
      fin_cases a <;> simp [d, t, Fin.sum_univ_two, add_comm]
  have hfixed : HeckeEis.binarySubst ℂ (ModularGroup.T ^ N : SL(2, ℤ)) A.val = A.val :=
    congrArg Subtype.val hA
  have hperiod : (d A.val).comp (Polynomial.X + Polynomial.C (N : ℂ)) = d A.val := by
    calc
      _ = d (HeckeEis.binarySubst ℂ (ModularGroup.T ^ N : SL(2, ℤ)) A.val) :=
        (congrArg (fun f : MvPolynomial (Fin 2) ℂ →+* Polynomial ℂ => f A.val) hcomm).symm
      _ = d A.val := congrArg d hfixed
  refine ⟨(d A.val).coeff 0, p02_es_177ebb5a_tff_constant_dehomogenization n A _ ?_⟩
  exact p02_es_177ebb5a_tff_periodic_polynomial_constant (d A.val) (N : ℂ)
    (Nat.cast_ne_zero.mpr (NeZero.ne N)) hperiod
/-- A coefficient bound controls evaluation of a homogeneous binary form at `(1, -z)`. -/
theorem p02_es_177ebb5a_tb_eval_bound
    (n : ℕ) (R : ↥(HeckeEis.BinaryForm ℂ n)) (z : ℂ) (b : ℝ)
    (hb : 0 ≤ b)
    (hcoeff : ∀ d : Fin 2 →₀ ℕ, ‖MvPolynomial.coeff d R.val‖ ≤ b) :
    ‖MvPolynomial.eval (fun j : Fin 2 => if j = 0 then 1 else -z) R.val‖ ≤
      ((n + 1 : ℕ) : ℝ) * (max 1 ‖z‖) ^ n * b := by
  classical
  have hdeg (d : Fin 2 →₀ ℕ) (hd : d ∈ R.val.support) : d 0 + d 1 = n := by
    simpa only [Finsupp.weight_eq_sum, Fin.sum_univ_two, Pi.one_apply,
      smul_eq_mul, mul_one] using R.property (MvPolynomial.mem_support_iff.mp hd)
  have hcard : R.val.support.card ≤ n + 1 := by
    calc
      R.val.support.card ≤ (Finset.range (n + 1)).card := by
        apply Finset.card_le_card_of_injOn (fun d : Fin 2 →₀ ℕ => d 1)
        · intro d hd
          have := hdeg d hd
          exact Finset.mem_range.mpr (by change d 1 < n + 1; omega)
        · intro d hd e he hde
          change d 1 = e 1 at hde
          have hddeg := hdeg d hd
          have hedeg := hdeg e he
          ext j
          fin_cases j
          · change d 0 = e 0
            omega
          · exact hde
      _ = n + 1 := Finset.card_range _
  have hterm (d : Fin 2 →₀ ℕ) (hd : d ∈ R.val.support) :
      ‖MvPolynomial.coeff d R.val * (-z) ^ d 1‖ ≤ b * (max 1 ‖z‖) ^ n := by
    have hpow : ‖z‖ ^ d 1 ≤ (max 1 ‖z‖) ^ n := by
      calc
        ‖z‖ ^ d 1 ≤ (max 1 ‖z‖) ^ d 1 :=
          pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) _
        _ ≤ (max 1 ‖z‖) ^ n :=
          pow_le_pow_right₀ (le_max_left _ _) (by have := hdeg d hd; omega)
    simpa only [norm_mul, norm_pow, norm_neg] using
      mul_le_mul (hcoeff d) hpow (pow_nonneg (norm_nonneg _) _) hb
  rw [MvPolynomial.eval_eq']
  simp only [Fin.prod_univ_two, Fin.isValue, ite_true, one_pow, one_ne_zero,
    ite_false, one_mul]
  calc
    ‖∑ d ∈ R.val.support, MvPolynomial.coeff d R.val * (-z) ^ d 1‖ ≤
        ∑ d ∈ R.val.support, ‖MvPolynomial.coeff d R.val * (-z) ^ d 1‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _d ∈ R.val.support, b * (max 1 ‖z‖) ^ n := Finset.sum_le_sum hterm
    _ = (R.val.support.card : ℝ) * (b * (max 1 ‖z‖) ^ n) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((n + 1 : ℕ) : ℝ) * (b * (max 1 ‖z‖) ^ n) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcard)
        (mul_nonneg hb (pow_nonneg (le_trans (norm_nonneg _) (le_max_right _ _)) _))
    _ = ((n + 1 : ℕ) : ℝ) * (max 1 ‖z‖) ^ n * b := by ring
/-- A bound on one period strip gives a uniform bound for sufficiently large imaginary part. -/
theorem p02_es_177ebb5a_tb_periodic_strip_bound
    (N : ℕ) [NeZero N] (q : UpperHalfPlane → ℂ)
    (hperiod : ∀ τ : UpperHalfPlane, q ((ModularGroup.T ^ N) • τ) = q τ)
    (hstrip : ∃ M Y : ℝ, ∀ τ : UpperHalfPlane,
      0 ≤ τ.re → τ.re ≤ (N : ℝ) → Y ≤ τ.im → ‖q τ‖ ≤ M) :
    UpperHalfPlane.IsBoundedAtImInfty q := by
  obtain ⟨M, Y, hstrip⟩ := hstrip
  have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  apply UpperHalfPlane.isBoundedAtImInfty_iff.mpr
  refine ⟨M, Y, ?_⟩
  intro τ hτ
  have hper : Function.Periodic (fun x : ℝ => q (x +ᵥ τ)) (N : ℝ) := by
    intro x
    simpa only [← zpow_natCast, UpperHalfPlane.modular_T_zpow_smul,
      Int.cast_natCast, ← add_vadd, add_comm] using hperiod (x +ᵥ τ)
  let m : ℤ := ⌊τ.re / (N : ℝ)⌋
  let τ' : UpperHalfPlane := (-(m : ℝ) * (N : ℝ)) +ᵥ τ
  have hre : τ'.re = τ.re - (m : ℝ) * N := by
    simp only [τ', UpperHalfPlane.vadd_re, neg_mul, sub_eq_add_neg, add_comm]
  have hq : q τ' = q τ := by
    simpa only [τ', Int.cast_neg, zero_vadd] using hper.int_mul_eq (-m)
  rw [← hq]
  apply hstrip τ'
  · rw [hre]
    exact Int.sub_floor_div_mul_nonneg τ.re hN
  · rw [hre]
    exact (Int.sub_floor_div_mul_lt τ.re hN).le
  · simpa only [τ', UpperHalfPlane.vadd_im] using hτ

open Filter Topology

/-- Exponential decay of an Eichler derivative and translation equivariance bound its scalarization. -/
theorem p02_es_177ebb5a_sm_translation_bound
    (N : ℕ) [NeZero N] (n : ℕ) (u : UpperHalfPlane → ℂ)
    (G : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n))
    (hu : Continuous u) (hG : HeckeEis.IsEichlerIntegral n u G)
    (htrans : ∀ τ : UpperHalfPlane, G ((ModularGroup.T ^ N) • τ) =
      (HeckeEis.binaryFormRepSL ℂ n (ModularGroup.T ^ N)) (G τ))
    (hdecay : ∃ a C Y : ℝ, 0 < a ∧ 0 ≤ C ∧ ∀ τ : UpperHalfPlane,
      Y ≤ τ.im → ‖u τ‖ ≤ C * Real.exp (-a * τ.im)) :
    UpperHalfPlane.IsBoundedAtImInfty (fun τ : UpperHalfPlane =>
      MvPolynomial.eval (fun j : Fin 2 => if j = 0 then 1 else -(τ : ℂ)) (G τ).val) := by
  classical
  obtain ⟨a, C, Y, ha, hC, hu_decay⟩ := hdecay
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  obtain ⟨A, K, hK, hcoeff⟩ := p02_es_177ebb5a_tb_strip_coefficient_limit
    n u G a C Y N ha hC hN hu hG hu_decay
  -- All polynomial factors are dominated by the exponential, also after shifting y by 1.
  have hpoly (m : ℕ) : Tendsto (fun y : ℝ => (1 + y) ^ m * Real.exp (-a * y))
      atTop (𝓝 0) := by
    have h := ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (m : ℝ) a ha).comp
      (tendsto_atTop_add_const_left atTop (1 : ℝ) tendsto_id)).mul_const (Real.exp a)
    simp only [Function.comp_def, id_eq, Real.rpow_natCast, zero_mul] at h
    convert h using 1
    funext y
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have hsmall : Tendsto (fun y : ℝ => K * (1 + y) ^ n * Real.exp (-a * y))
      atTop (𝓝 0) := by
    simpa only [mul_assoc, mul_zero] using (hpoly n).const_mul K
  -- A single finite set of degree-n monomials works for every binary form.
  let s := (Finsupp.finite_of_degree_eq (σ := Fin 2) n).toFinset
  have hexpand (B : ↥(HeckeEis.BinaryForm ℂ n)) : B.val =
      ∑ d ∈ s, MvPolynomial.coeff d B.val • MvPolynomial.monomial d (1 : ℂ) := by
    conv_lhs => rw [MvPolynomial.as_sum B.val]
    simp only [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    apply Finset.sum_subset
    · intro d hd
      have hdeg := B.property (MvPolynomial.mem_support_iff.mp hd)
      simpa [s, Finsupp.degree_eq_weight_one, Pi.one_def] using hdeg
    · intro d _ hd
      simp [MvPolynomial.notMem_support_iff.mp hd]
  let z (y : ℝ) : UpperHalfPlane := ⟨⟨0, max 1 y⟩,
    lt_of_lt_of_le zero_lt_one (le_max_left _ _)⟩
  have hlimcoeff (x : ℝ) (hx : 0 ≤ x) (hxN : x ≤ N) (d : Fin 2 →₀ ℕ) :
      Tendsto (fun y : ℝ => MvPolynomial.coeff d (G (x +ᵥ z y)).val)
        atTop (𝓝 (MvPolynomial.coeff d A.val)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hsmall
    filter_upwards [eventually_ge_atTop (max 1 Y)] with y hy
    have hy1 : 1 ≤ y := (le_max_left _ _).trans hy
    simpa [z, max_eq_right hy1, MvPolynomial.coeff_sub,
      UpperHalfPlane.vadd_re, UpperHalfPlane.vadd_im] using
      hcoeff (x +ᵥ z y) (by simpa [z] using hx) (by simpa [z] using hxN)
        (by simpa [z, max_eq_right hy1] using hy) d
  have hlim (ℓ : MvPolynomial (Fin 2) ℂ →ₗ[ℂ] ℂ)
      (x : ℝ) (hx : 0 ≤ x) (hxN : x ≤ N) :
      Tendsto (fun y : ℝ => ℓ (G (x +ᵥ z y)).val) atTop (𝓝 (ℓ A.val)) := by
    have hex (B : ↥(HeckeEis.BinaryForm ℂ n)) : ℓ B.val =
        ∑ d ∈ s, MvPolynomial.coeff d B.val * ℓ (MvPolynomial.monomial d 1) := by
      conv_lhs => rw [hexpand B]
      simp only [map_sum, map_smul, smul_eq_mul]
    simp_rw [hex]
    exact tendsto_finsetSum s (fun d _ => (hlimcoeff x hx hxN d).mul_const _)
  have hshift (τ : UpperHalfPlane) : (ModularGroup.T ^ N) • τ = (N : ℝ) +ᵥ τ := by
    simpa only [zpow_natCast, Int.cast_natCast] using
      UpperHalfPlane.modular_T_zpow_smul τ (N : ℤ)
  -- Coefficient limits commute with substitution because the expansion is finite.
  have hfixed : HeckeEis.binaryFormRepSL ℂ n (ModularGroup.T ^ N) A = A := by
    apply Subtype.ext
    apply MvPolynomial.ext
    intro d
    let ℓ := (MvPolynomial.lcoeff ℂ d).comp
      (HeckeEis.binarySubst ℂ (ModularGroup.T ^ N : SL(2, ℤ))).toLinearMap
    have hleft := hlim ℓ 0 le_rfl hN
    have hright := hlimcoeff (N : ℝ) hN le_rfl d
    have heq (y : ℝ) : ℓ (G ((0 : ℝ) +ᵥ z y)).val =
        MvPolynomial.coeff d (G ((N : ℝ) +ᵥ z y)).val := by
      rw [zero_vadd, ← hshift, htrans]
      rfl
    simp_rw [heq] at hleft
    exact tendsto_nhds_unique hleft hright
  obtain ⟨α, hA⟩ := p02_es_177ebb5a_tb_fixed_form N n A hfixed
  have hevalA (w : ℂ) :
      MvPolynomial.eval (fun j : Fin 2 => if j = 0 then 1 else -w) A.val = α := by
    simp [hA]
  let q (τ : UpperHalfPlane) :=
    MvPolynomial.eval (fun j : Fin 2 => if j = 0 then 1 else -(τ : ℂ)) (G τ).val
  apply p02_es_177ebb5a_tb_periodic_strip_bound N q
  · intro τ
    have hmatrix : ((ModularGroup.T ^ N : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
        !![1, (N : ℤ); 0, 1] := by
      simpa only [zpow_natCast] using ModularGroup.coe_T_zpow (N : ℤ)
    have heval : (MvPolynomial.eval (fun j : Fin 2 => if j = 0 then 1 else
          -(((ModularGroup.T ^ N) • τ : UpperHalfPlane) : ℂ))).comp
          (HeckeEis.binarySubst ℂ (ModularGroup.T ^ N : SL(2, ℤ))).toRingHom =
        MvPolynomial.eval (fun j : Fin 2 => if j = 0 then 1 else -(τ : ℂ)) := by
      apply MvPolynomial.ringHom_ext
      · intro c
        simp
      · intro j
        change MvPolynomial.eval _ (HeckeEis.binarySubst ℂ
          (ModularGroup.T ^ N : SL(2, ℤ)) (MvPolynomial.X j)) = _
        rw [HeckeEis.binarySubst_X, hmatrix, hshift, UpperHalfPlane.coe_vadd]
        fin_cases j <;> simp [Fin.sum_univ_two]
    change MvPolynomial.eval _ (G ((ModularGroup.T ^ N) • τ)).val = _
    rw [htrans]
    exact congrArg (fun f : MvPolynomial (Fin 2) ℂ →+* ℂ => f (G τ).val) heval
  · let B : ℝ := ((n + 1 : ℕ) : ℝ) * (N + 2 : ℝ) ^ n * K
    have herr : Tendsto (fun y : ℝ => B * (1 + y) ^ (2 * n) * Real.exp (-a * y))
        atTop (𝓝 0) := by
      simpa only [mul_assoc, mul_zero] using (hpoly (2 * n)).const_mul B
    obtain ⟨Y₁, hY₁⟩ := eventually_atTop.mp (herr.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)))
    refine ⟨‖α‖ + 1, max (max 1 Y) Y₁, ?_⟩
    intro τ hx hxN hy
    have hy₀ : max 1 Y ≤ τ.im := (le_max_left _ _).trans hy
    have hy1 : 1 ≤ τ.im := (le_max_left _ _).trans hy₀
    have hpos : 0 ≤ 1 + τ.im := by linarith
    have hz : max 1 ‖(τ : ℂ)‖ ≤ (N + 2 : ℝ) * (1 + τ.im) := by
      apply max_le
      · nlinarith
      · have ht := Complex.norm_le_abs_re_add_abs_im (τ : ℂ)
        change ‖(τ : ℂ)‖ ≤ |τ.re| + |τ.im| at ht
        rw [abs_of_nonneg hx, abs_of_nonneg τ.im_pos.le] at ht
        nlinarith
    have hbound := p02_es_177ebb5a_tb_eval_bound n (G τ - A) (τ : ℂ)
      (K * (1 + τ.im) ^ n * Real.exp (-a * τ.im)) (by positivity)
      (hcoeff τ hx hxN hy₀)
    have hnorm : ‖q τ - α‖ ≤ B * (1 + τ.im) ^ (2 * n) * Real.exp (-a * τ.im) := by
      calc
        ‖q τ - α‖ = ‖MvPolynomial.eval
            (fun j : Fin 2 => if j = 0 then 1 else -(τ : ℂ)) (G τ - A).val‖ := by
          simp only [Submodule.coe_sub, map_sub, hevalA, q]
        _ ≤ ((n + 1 : ℕ) : ℝ) * (max 1 ‖(τ : ℂ)‖) ^ n *
            (K * (1 + τ.im) ^ n * Real.exp (-a * τ.im)) := hbound
        _ ≤ ((n + 1 : ℕ) : ℝ) * ((N + 2 : ℝ) * (1 + τ.im)) ^ n *
            (K * (1 + τ.im) ^ n * Real.exp (-a * τ.im)) := by gcongr
        _ = B * (1 + τ.im) ^ (2 * n) * Real.exp (-a * τ.im) := by
          rw [mul_pow, two_mul, pow_add]
          dsimp [B]
          ring
    calc
      ‖q τ‖ ≤ ‖q τ - α‖ + ‖α‖ := norm_le_norm_sub_add _ _
      _ ≤ 1 + ‖α‖ := by
        have := (hY₁ τ.im ((le_max_right _ _).trans hy)).le
        linarith
      _ = ‖α‖ + 1 := add_comm _ _


end Submission


theorem Submission.p02_es_177ebb5a_sm_all_cusps :
    ∀ (N : ℕ) [NeZero N] (n : ℕ)
      (f : CuspForm (CongruenceSubgroup.Gamma0 N) ((n : ℤ) + 2))
      (E : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n)),
      HeckeEis.IsEichlerIntegral n (fun τ => f τ) E →
      (∀ (γ : CongruenceSubgroup.Gamma0 N) (τ : UpperHalfPlane),
        E ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) • τ) =
          ((HeckeEis.binaryFormRepSL ℂ n).comp
            (CongruenceSubgroup.Gamma0 N).subtype) γ (E τ)) →
      ∀ c : OnePoint ℝ,
        IsCusp c ((CongruenceSubgroup.Gamma0 N).map
          (Matrix.SpecialLinearGroup.mapGL ℝ)) →
        OnePoint.IsBoundedAt c (fun τ : UpperHalfPlane =>
          MvPolynomial.eval (fun j : Fin 2 => if j = 0 then 1 else -(τ : ℂ))
            (E τ).val) (-(n : ℤ)) := by
  classical
  intro N _ n f E hE heq c hc
  have hcSL := (Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z
    ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ))).mp hc
  obtain ⟨σ, hσ⟩ := isCusp_SL2Z_iff'.mp hcSL
  let T : SL(2, ℤ) := ModularGroup.T ^ N
  let γ : SL(2, ℤ) := σ * T * σ⁻¹
  have hT : T ∈ CongruenceSubgroup.Gamma N := by
    simpa only [T, zpow_natCast, Int.natAbs_natCast] using
      CongruenceSubgroup.ModularGroup_T_pow_mem_Gamma (N : ℤ) (N : ℤ) (dvd_refl _)
  have hγ : γ ∈ CongruenceSubgroup.Gamma0 N := by
    have h := (CongruenceSubgroup.Gamma_normal N).conj_mem T hT σ
    exact (CongruenceSubgroup.Gamma_mem.mp h).2.2.1
  have hcomm : σ * T = γ * σ := by simp [γ, mul_assoc]
  let u : UpperHalfPlane → ℂ := SlashAction.map ((n : ℤ) + 2) σ (fun τ => f τ)
  let G : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n) :=
    fun τ => (HeckeEis.binaryFormRepSL ℂ n σ⁻¹) (E (σ • τ))
  have huinv : SlashAction.map ((n : ℤ) + 2) T u = u := by
    change ((fun τ => f τ) ∣[(n : ℤ) + 2] σ) ∣[(n : ℤ) + 2] T = _
    rw [← SlashAction.slash_mul, hcomm, SlashAction.slash_mul]
    have hfγ : (fun τ => f τ) ∣[(n : ℤ) + 2] γ = (fun τ => f τ) := by
      rw [ModularForm.SL_slash]
      exact SlashInvariantFormClass.slash_action_eq f _ ⟨γ, hγ, rfl⟩
    rw [hfγ]
  have hshift (τ : UpperHalfPlane) : T • τ = (N : ℝ) +ᵥ τ := by
    simpa only [T, zpow_natCast, Int.cast_natCast] using
      UpperHalfPlane.modular_T_zpow_smul τ (N : ℤ)
  have hmatrix : (T : Matrix (Fin 2) (Fin 2) ℤ) = !![1, (N : ℤ); 0, 1] := by
    simpa only [T, zpow_natCast] using ModularGroup.coe_T_zpow (N : ℤ)
  have huper (τ : UpperHalfPlane) : u ((N : ℝ) +ᵥ τ) = u τ := by
    have h := congrFun huinv τ
    simpa [ModularForm.SL_slash_apply, UpperHalfPlane.denom, hmatrix, hshift] using h
  have huper' : Function.Periodic (u ∘ UpperHalfPlane.ofComplex) (N : ℂ) := by
    intro w
    by_cases hw : 0 < w.im
    · have hw' : 0 < (w + (N : ℂ)).im := by simpa using hw
      simp only [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hw',
        UpperHalfPlane.ofComplex_apply_of_im_pos hw]
      convert huper ⟨w, hw⟩ using 2
      apply UpperHalfPlane.ext
      simp [UpperHalfPlane.coe_vadd, add_comm]
    · have hw' : (w + (N : ℂ)).im ≤ 0 := by simpa using le_of_not_gt hw
      simp only [Function.comp_apply]
      rw [UpperHalfPlane.ofComplex_apply_eq_of_im_nonpos hw' (le_of_not_gt hw)]
  have huhol : MDiff u := by
    simpa only [u, ModularForm.SL_slash] using
      (ModularFormClass.holo f).slash ((n : ℤ) + 2) (σ : GL (Fin 2) ℝ)
  have huzero : UpperHalfPlane.IsZeroAtImInfty u :=
    CuspFormClass.zero_at_infty_slash f σ
  have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have hdecay : ∃ a C Y : ℝ, 0 < a ∧ 0 ≤ C ∧ ∀ τ : UpperHalfPlane,
      Y ≤ τ.im → ‖u τ‖ ≤ C * Real.exp (-a * τ.im) := by
    have hbig := huzero.exp_decay_atImInfty hN huper' huhol huzero.isBoundedAtImInfty
    obtain ⟨C, hC, hbound⟩ := hbig.exists_nonneg
    obtain ⟨Y, hY⟩ := (UpperHalfPlane.atImInfty_mem _).mp hbound.bound
    refine ⟨2 * Real.pi / N, C, Y, by positivity, hC, ?_⟩
    intro τ hτ
    have hexp : -2 * Real.pi * τ.im / (N : ℝ) =
        -(2 * Real.pi / (N : ℝ)) * τ.im := by ring
    simpa only [Set.mem_ofPred_eq, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      hexp] using hY τ hτ
  have hG : HeckeEis.IsEichlerIntegral n u G :=
    Submission.p02_es_177ebb5a_sm_transformed_integral n (fun τ => f τ) E σ hE
  have hGtrans (τ : UpperHalfPlane) : G (T • τ) =
      (HeckeEis.binaryFormRepSL ℂ n T) (G τ) := by
    have hact : σ • (T • τ) = γ • (σ • τ) := by
      rw [← mul_smul, hcomm, mul_smul]
    change (HeckeEis.binaryFormRepSL ℂ n σ⁻¹) (E (σ • (T • τ))) = _
    rw [hact, heq ⟨γ, hγ⟩ (σ • τ)]
    change ((HeckeEis.binaryFormRepSL ℂ n σ⁻¹) *
      (HeckeEis.binaryFormRepSL ℂ n γ)) (E (σ • τ)) =
      ((HeckeEis.binaryFormRepSL ℂ n T) *
        (HeckeEis.binaryFormRepSL ℂ n σ⁻¹)) (E (σ • τ))
    rw [← map_mul, ← map_mul]
    simp [γ, mul_assoc]
  have hb := Submission.p02_es_177ebb5a_sm_translation_bound N n u G
    huhol.continuous hG hGtrans hdecay
  apply (OnePoint.isBoundedAt_iff_exists_SL2Z hcSL).mpr
  refine ⟨σ, hσ.symm, ?_⟩
  have hscalar : SlashAction.map (-(n : ℤ)) σ (fun τ : UpperHalfPlane =>
      MvPolynomial.eval (fun j : Fin 2 => if j = 0 then 1 else -(τ : ℂ)) (E τ).val) =
      (fun τ : UpperHalfPlane =>
        MvPolynomial.eval (fun j : Fin 2 => if j = 0 then 1 else -(τ : ℂ)) (G τ).val) :=
    funext (Submission.p02_es_177ebb5a_sm_slash n E σ)
  rwa [hscalar]

namespace Submission

theorem p02_es_177ebb5a_scalarization_modular
    (N : ℕ) [NeZero N] (n : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) ((n : ℤ) + 2))
    (E : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n))
    (hE : HeckeEis.IsEichlerIntegral n (fun τ => f τ) E)
    (hEquiv : ∀ (γ : CongruenceSubgroup.Gamma0 N) (τ : UpperHalfPlane),
      E ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) • τ) =
        ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype)
          γ (E τ)) :
    ∃ p : ModularForm (CongruenceSubgroup.Gamma0 N) (-(n : ℤ)),
      ∀ τ : UpperHalfPlane, p τ =
        MvPolynomial.eval (fun j : Fin 2 => if j = 0 then 1 else -(τ : ℂ)) (E τ).val := by
  refine ⟨{
    toFun := fun τ =>
      MvPolynomial.eval (fun j : Fin 2 => if j = 0 then 1 else -(τ : ℂ)) (E τ).val
    slash_action_eq' := ?_
    holo' := ?_
    bdd_at_cusps' := fun hc => p02_es_177ebb5a_sm_all_cusps N n f E hE hEquiv _ hc
  }, fun _ => rfl⟩
  · intro γ hγ
    obtain ⟨σ, hσ, rfl⟩ := hγ
    funext τ
    change (SlashAction.map (-(n : ℤ)) σ (fun z : UpperHalfPlane =>
      MvPolynomial.eval (fun j : Fin 2 => if j = 0 then 1 else -(z : ℂ)) (E z).val)) τ = _
    rw [p02_es_177ebb5a_sm_slash, hEquiv ⟨σ, hσ⟩ τ]
    congr 2
    change ((HeckeEis.binaryFormRepSL ℂ n σ⁻¹) *
      (HeckeEis.binaryFormRepSL ℂ n σ)) (E τ) = E τ
    rw [← map_mul, inv_mul_cancel, map_one]
    rfl
  · apply UpperHalfPlane.mdifferentiable_iff.mpr
    apply (p02_es_177ebb5a_sm_holomorphic n (fun τ => f τ) E hE).congr
    intro z hz
    simp [UpperHalfPlane.ofComplex_apply_of_im_pos hz]

theorem p02_es_177ebb5a_sd_jr_homogeneous_nilpotence
    (n : ℕ) (P : ↥(HeckeEis.BinaryForm ℂ n)) :
    ((fun p : MvPolynomial (Fin 2) ℂ => MvPolynomial.pderiv (1 : Fin 2) p)^[n + 1]
      P.val) = 0 := by
  classical
  let D : Module.End ℂ (MvPolynomial (Fin 2) ℂ) :=
    (MvPolynomial.pderiv (1 : Fin 2)).toLinearMap
  have hmon (k : ℕ) (d : Fin 2 →₀ ℕ) (a : ℂ) (hd : d 1 < k) :
      (D ^ k) (MvPolynomial.monomial d a) = 0 := by
    induction k generalizing d a with
    | zero => omega
    | succ k ih =>
      rw [pow_succ, Module.End.mul_apply]
      change (D ^ k) (MvPolynomial.pderiv 1 (MvPolynomial.monomial d a)) = 0
      rw [MvPolynomial.pderiv_monomial]
      by_cases hzero : d 1 = 0
      · simp [hzero]
      · apply ih
        simp only [Finsupp.tsub_apply, Finsupp.single_eq_same]
        omega
  change (D : MvPolynomial (Fin 2) ℂ → MvPolynomial (Fin 2) ℂ)^[n + 1] P.val = 0
  rw [← Module.End.pow_apply, ← P.val.support_sum_monomial_coeff, map_sum]
  apply Finset.sum_eq_zero
  intro d hd
  apply hmon
  have hdegree : d.degree = n := by
    simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using
      P.property (MvPolynomial.mem_support_iff.mp hd)
  exact lt_of_le_of_lt ((Finsupp.le_degree 1 d).trans_eq hdegree) (Nat.lt_succ_self n)
theorem p02_es_177ebb5a_sd_jr_linepow_eval :
    ∀ (n r : ℕ), r ≤ n → ∀ t : ℂ,
      MvPolynomial.eval (fun j : Fin 2 => if j = 0 then 1 else -t)
        ((fun p : MvPolynomial (Fin 2) ℂ => MvPolynomial.pderiv (1 : Fin 2) p)^[r]
          (HeckeEis.linePow n t).val) =
        (if r = n then (Nat.factorial n : ℂ) else 0) := by
  intro n r hr t
  let L : MvPolynomial (Fin 2) ℂ := MvPolynomial.C t * MvPolynomial.X 0 +
    MvPolynomial.X 1
  have hD : MvPolynomial.pderiv (1 : Fin 2) L = 1 := by
    simp [L]
  have hiter (s : ℕ) (hs : s ≤ n) :
      (fun p : MvPolynomial (Fin 2) ℂ => MvPolynomial.pderiv (1 : Fin 2) p)^[s]
        (L ^ n) = MvPolynomial.C (n.descFactorial s : ℂ) * L ^ (n - s) := by
    induction s with
    | zero => simp
    | succ s ih =>
      rw [Function.iterate_succ_apply', ih (by omega), MvPolynomial.pderiv_C_mul,
        MvPolynomial.pderiv_pow, hD, mul_one]
      simp only [Nat.descFactorial_succ, Nat.cast_mul, map_mul, map_natCast,
        Nat.sub_sub]
      ring
  have hEval : MvPolynomial.eval (fun j : Fin 2 => if j = 0 then 1 else -t) L = 0 := by
    simp [L]
  change MvPolynomial.eval _
    ((fun p : MvPolynomial (Fin 2) ℂ => MvPolynomial.pderiv (1 : Fin 2) p)^[r]
      (L ^ n)) = _
  rw [hiter r hr, map_mul, MvPolynomial.eval_C, map_pow, hEval]
  by_cases h : r = n
  · subst r
    simp [Nat.descFactorial_self]
  · have hnr : n - r ≠ 0 := by omega
    simp [h, zero_pow hnr]

end Submission
