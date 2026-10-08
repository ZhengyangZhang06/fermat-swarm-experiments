/-
Copyright 2026 Anthropic, PBC. Licensed under Apache-2.0; see LICENSE.
Source: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_WeierstrassCurve_galoisRep_ordinaryLineAt.lean
Modified: replaced the proof with sorry and removed P2M proof imports.
Requires the upstream Definitions modules and their dependencies.
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Definitions.Def_GaloisRep_Residual
attribute [-instance] WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly
attribute [-simp] compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
theorem WeierstrassCurve.galoisRep_ordinaryLineAt (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hΔ : W.Δ ≠ 0)
    (hW : W.IsSemistableModel)
    (hord : (p : ℤ) ∣ W.Δ ∨ ∃ i, 1 ≤ i ∧ i < (p ^ 2 - 1) / 2 ∧ ¬ (p : ℤ) ∣ (W.preΨ' p).coeff i)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p) :
    ∃ L : Submodule (ZMod p)
        (Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p),
      L ≠ ⊤ ∧ ∀ σ ∈ A.inertiaSubgroupIn ℚ,
        ∀ v : Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p,
          WeierstrassCurve.Affine.Point.galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ
            (W.map (Int.castRingHom ℚ)) p σ v - v ∈ L := by
  sorry

theorem Submission.p03_tu_lambert_summable_68cf3476 :
    ∀ (F : Type) [NormedField F] [CompleteSpace F],
      (∀ x y : F, ‖x + y‖ ≤ max ‖x‖ ‖y‖) →
      ∀ q : F, ‖q‖ < 1 → ∀ k : ℕ,
        Summable (fun d : ℕ =>
          ((d + 1 : ℕ) : F) ^ k * q ^ (d + 1) / (1 - q ^ (d + 1))) := by
  intro F _ _ hnonarch q hq k
  have hnat : ∀ m : ℕ, ‖(m : F)‖ ≤ 1 := by
    intro m
    induction m with
    | zero => simp
    | succ m hm =>
      rw [Nat.cast_succ]
      exact (hnonarch (m : F) 1).trans (max_le hm (by simp))
  have hden : ∀ d : ℕ, ‖1 - q ^ (d + 1)‖ = 1 := by
    intro d
    have hpow : ‖q ^ (d + 1)‖ < 1 := by
      rw [norm_pow]
      exact pow_lt_one₀ (norm_nonneg q) hq (Nat.succ_ne_zero d)
    apply le_antisymm
    · calc
        ‖1 - q ^ (d + 1)‖ ≤ max ‖(1 : F)‖ ‖-(q ^ (d + 1))‖ := by
          simpa only [sub_eq_add_neg] using hnonarch 1 (-(q ^ (d + 1)))
        _ ≤ 1 := max_le (by simp) (by simpa only [norm_neg] using hpow.le)
    · by_contra h
      have hlt : ‖1 - q ^ (d + 1)‖ < 1 := lt_of_not_ge h
      have hone := hnonarch (1 - q ^ (d + 1)) (q ^ (d + 1))
      rw [sub_add_cancel, norm_one] at hone
      exact (not_lt_of_ge hone) (max_lt_iff.mpr ⟨hlt, hpow⟩)
  have hgeom : Summable (fun d : ℕ => ‖q‖ ^ (d + 1)) :=
    (summable_nat_add_iff 1).2 (summable_geometric_of_lt_one (norm_nonneg q) hq)
  apply hgeom.of_norm_bounded
  intro d
  rw [norm_div, norm_mul, hden d, div_one, norm_pow, norm_pow]
  exact mul_le_of_le_one_left (pow_nonneg (norm_nonneg q) (d + 1))
    (pow_le_one₀ (norm_nonneg _) (hnat (d + 1)))
theorem Submission.p03_tu_euler_product_powers_68cf3476 :
    ∀ (F : Type) [NormedField F] [CompleteSpace F],
      (∀ x y : F, ‖x + y‖ ≤ max ‖x‖ ‖y‖) → ∀ q : F, ‖q‖ < 1 →
      Multipliable (fun d : ℕ => 1 - q ^ (d + 1)) ∧
      (∏' d : ℕ, (1 - q ^ (d + 1))) ≠ 0 ∧
      ∀ k : ℕ, Multipliable (fun d : ℕ => (1 - q ^ (d + 1)) ^ k) ∧
        (∏' d : ℕ, (1 - q ^ (d + 1)) ^ k) =
          (∏' d : ℕ, (1 - q ^ (d + 1))) ^ k ∧
        (∏' d : ℕ, (1 - q ^ (d + 1)) ^ k) ≠ 0 := by
  intro F _ _ hna q hq
  classical
  let a : ℕ → F := fun d => 1 - q ^ (d + 1)
  have hpow (d : ℕ) : ‖q ^ (d + 1)‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg q) hq (by omega)
  have ha (d : ℕ) : ‖a d‖ = 1 := by
    apply le_antisymm
    · simpa only [a, sub_eq_add_neg, norm_one, norm_neg, max_le_iff] using
        (hna 1 (-(q ^ (d + 1)))).trans
          (max_le (by simp) (by simpa using (hpow d).le))
    · by_contra h
      have hlt : ‖a d‖ < 1 := lt_of_not_ge h
      have h := hna (a d) (q ^ (d + 1))
      have heq : a d + q ^ (d + 1) = 1 := by dsimp [a]; ring
      rw [heq, norm_one] at h
      exact (not_lt_of_ge h) (max_lt hlt (hpow d))
  have hprod (s : Finset ℕ) : ‖∏ d ∈ s, a d‖ = 1 := by
    simp [norm_prod, ha]
  have htail (N : ℕ) (s : Finset ℕ) (hs : ∀ d ∈ s, N ≤ d) :
      ‖(∏ d ∈ s, a d) - 1‖ ≤ ‖q‖ ^ (N + 1) := by
    induction s using Finset.induction_on with
    | empty => simp [pow_nonneg (norm_nonneg q)]
    | @insert d s hd ih =>
      have hds : N ≤ d := hs d (Finset.mem_insert_self d s)
      have hss : ∀ i ∈ s, N ≤ i := fun i hi => hs i (Finset.mem_insert_of_mem hi)
      rw [Finset.prod_insert hd]
      have heq : a d * (∏ i ∈ s, a i) - 1 =
          (a d - 1) * (∏ i ∈ s, a i) + ((∏ i ∈ s, a i) - 1) := by ring
      rw [heq]
      apply (hna _ _).trans
      apply max_le _ (ih hss)
      rw [norm_mul, hprod, mul_one]
      have heq : a d - 1 = -(q ^ (d + 1)) := by dsimp [a]; ring
      rw [heq, norm_neg, norm_pow]
      exact pow_le_pow_of_le_one (norm_nonneg q) hq.le (Nat.add_le_add_right hds 1)
  have hm : Multipliable a := by
    apply multipliable_iff_cauchySeq_finset.mpr
    apply Metric.cauchySeq_iff'.mpr
    intro ε hε
    have ht := tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg q) hq
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (ht.eventually (gt_mem_nhds hε))
    refine ⟨Finset.range N, ?_⟩
    intro s hs
    have htail' := htail N (s \ Finset.range N) (by
      intro d hd
      exact Nat.le_of_not_lt (by simpa using (Finset.mem_sdiff.mp hd).2))
    have heq : (∏ d ∈ s, a d) - (∏ d ∈ Finset.range N, a d) =
        (∏ d ∈ Finset.range N, a d) * ((∏ d ∈ s \ Finset.range N, a d) - 1) := by
      rw [mul_sub, mul_one, mul_comm, Finset.prod_sdiff hs]
    rw [dist_eq_norm, heq, norm_mul, hprod, one_mul]
    exact htail'.trans_lt (hN (N + 1) (Nat.le_succ N))
  have hn : ‖∏' d, a d‖ = 1 := by
    have ht := (show Filter.Tendsto (fun s : Finset ℕ => ∏ d ∈ s, a d)
        Filter.atTop (nhds (∏' d, a d)) from hm.hasProd).norm
    simp only [hprod] at ht
    exact tendsto_nhds_unique ht tendsto_const_nhds
  have hz : (∏' d, a d) ≠ 0 := by
    intro hz
    rw [hz, norm_zero] at hn
    exact zero_ne_one hn
  refine ⟨hm, hz, ?_⟩
  intro k
  refine ⟨hm.pow k, hm.tprod_pow k, ?_⟩
  rw [hm.tprod_pow k]
  exact pow_ne_zero k hz
theorem Submission.p03_tu_bilateral_summable_68cf3476 :
    ∀ (F Ω : Type) [NormedField F] [CompleteSpace F] [NormedField Ω]
      [NormedAlgebra F Ω] [Algebra.IsAlgebraic F Ω],
      (∀ x y : Ω, ‖x + y‖ ≤ max ‖x‖ ‖y‖) →
      ∀ q : F, 0 < ‖q‖ → ‖q‖ < 1 →
      let qΩ : Ω := algebraMap F Ω q
      ∀ u : Ωˣ, (¬ ∃ m : ℤ, (u : Ω) = qΩ ^ m) →
        Summable (fun n : ℤ => qΩ ^ n * (u : Ω) / (1 - qΩ ^ n * (u : Ω)) ^ 2) ∧
        Summable (fun n : ℤ => (qΩ ^ n * (u : Ω)) ^ 2 /
          (1 - qΩ ^ n * (u : Ω)) ^ 3) := by
  intro F Ω _ _ _ _ _ hΩ q hq0 hq1 qΩ u _hu
  let : NontriviallyNormedField F :=
    NontriviallyNormedField.ofNormNeOne ⟨q, norm_pos_iff.mp hq0, ne_of_lt hq1⟩
  let E := IntermediateField.adjoin F ({(u : Ω)} : Set Ω)
  have : FiniteDimensional F E :=
    IntermediateField.adjoin.finiteDimensional
      (Algebra.IsAlgebraic.isAlgebraic (R := F) (u : Ω)).isIntegral
  have : CompleteSpace E := FiniteDimensional.complete F E
  let Q : E := algebraMap F E q
  let v : E := ⟨(u : Ω), IntermediateField.mem_adjoin_simple_self F (u : Ω)⟩
  have hQnorm : ‖Q‖ = ‖q‖ := norm_algebraMap' E q
  have hQ0 : Q ≠ 0 := norm_pos_iff.mp (hQnorm ▸ hq0)
  have hv0 : v ≠ 0 := by
    intro hv
    exact u.ne_zero (congrArg (fun x : E => (x : Ω)) hv)
  have hE : ∀ x y : E, ‖x + y‖ ≤ max ‖x‖ ‖y‖ := fun x y => hΩ x y
  have hsub : ∀ x y : E, ‖y‖ < ‖x‖ → ‖x - y‖ = ‖x‖ := by
    intro x y hxy
    have hle : ‖x - y‖ ≤ ‖x‖ := by
      simpa only [sub_eq_add_neg, norm_neg, max_eq_left hxy.le] using hE x (-y)
    have hrev : ‖x‖ ≤ max ‖x - y‖ ‖y‖ := by
      simpa only [sub_add_cancel] using hE (x - y) y
    exact le_antisymm hle ((le_max_iff.mp hrev).resolve_right (not_le.mpr hxy))
  let z : ℤ → E := fun n => Q ^ n * v
  have hgeom : Summable (fun n : ℕ => ‖Q‖ ^ n) :=
    summable_geometric_of_lt_one (norm_nonneg _) (hQnorm ▸ hq1)
  have hlim : Filter.Tendsto (fun n : ℕ => ‖Q‖ ^ n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) (hQnorm ▸ hq1)
  have hpos : ∀ᶠ n : ℕ in Filter.atTop, ‖z (n : ℤ)‖ < 1 := by
    have ht : Filter.Tendsto (fun n : ℕ => ‖Q‖ ^ n * ‖v‖)
        Filter.atTop (nhds 0) := by
      simpa using hlim.mul_const ‖v‖
    simpa only [z, norm_mul, zpow_natCast, norm_pow] using
      ht.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  have hneg_norm : ∀ n : ℕ, ‖z (-(n : ℤ))‖⁻¹ = ‖Q‖ ^ n * ‖v‖⁻¹ := by
    intro n
    simp only [z, norm_mul, zpow_neg, zpow_natCast, norm_inv, norm_pow,
      mul_inv_rev, inv_inv, mul_comm]
  have hneg : ∀ᶠ n : ℕ in Filter.atTop, 1 < ‖z (-(n : ℤ))‖ := by
    have ht : Filter.Tendsto (fun n : ℕ => ‖Q‖ ^ n * ‖v‖⁻¹)
        Filter.atTop (nhds 0) := by
      simpa using hlim.mul_const ‖v‖⁻¹
    filter_upwards [ht.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with n hn
    have hz0 : 0 < ‖z (-(n : ℤ))‖ :=
      norm_pos_iff.mpr (mul_ne_zero (zpow_ne_zero _ hQ0) hv0)
    exact (inv_lt_one₀ hz0).mp (by rwa [hneg_norm])
  have hpos1 : Summable (fun n : ℕ => z (n : ℤ) / (1 - z (n : ℤ)) ^ 2) := by
    apply (hgeom.mul_right ‖v‖).of_norm_bounded_eventually_nat
    filter_upwards [hpos] with n hn
    have hd : ‖1 - z (n : ℤ)‖ = 1 := by
      simpa only [norm_one] using hsub 1 (z (n : ℤ)) (by simpa only [norm_one] using hn)
    simp only [norm_div, norm_pow, hd, one_pow, div_one]
    simp only [z, norm_mul, zpow_natCast, norm_pow, le_refl]
  have hpos2 : Summable (fun n : ℕ => (z (n : ℤ)) ^ 2 / (1 - z (n : ℤ)) ^ 3) := by
    apply (hgeom.mul_right ‖v‖).of_norm_bounded_eventually_nat
    filter_upwards [hpos] with n hn
    have hd : ‖1 - z (n : ℤ)‖ = 1 := by
      simpa only [norm_one] using hsub 1 (z (n : ℤ)) (by simpa only [norm_one] using hn)
    rw [norm_div, norm_pow, norm_pow, hd, one_pow, div_one]
    calc
      ‖z (n : ℤ)‖ ^ 2 ≤ ‖z (n : ℤ)‖ := by
        nlinarith [norm_nonneg (z (n : ℤ))]
      _ = ‖Q‖ ^ n * ‖v‖ := by simp only [z, norm_mul, zpow_natCast, norm_pow]
  have hneg1 : Summable (fun n : ℕ => z (-(n : ℤ)) / (1 - z (-(n : ℤ))) ^ 2) := by
    apply (hgeom.mul_right ‖v‖⁻¹).of_norm_bounded_eventually_nat
    filter_upwards [hneg] with n hn
    have hd : ‖1 - z (-(n : ℤ))‖ = ‖z (-(n : ℤ))‖ := by
      rw [norm_sub_rev]
      exact hsub _ 1 (by simpa only [norm_one] using hn)
    rw [norm_div, norm_pow, hd, ← hneg_norm]
    have hz : ‖z (-(n : ℤ))‖ ≠ 0 := ne_of_gt (lt_trans zero_lt_one hn)
    exact le_of_eq (by field_simp)
  have hneg2 : Summable (fun n : ℕ => (z (-(n : ℤ))) ^ 2 / (1 - z (-(n : ℤ))) ^ 3) := by
    apply (hgeom.mul_right ‖v‖⁻¹).of_norm_bounded_eventually_nat
    filter_upwards [hneg] with n hn
    have hd : ‖1 - z (-(n : ℤ))‖ = ‖z (-(n : ℤ))‖ := by
      rw [norm_sub_rev]
      exact hsub _ 1 (by simpa only [norm_one] using hn)
    rw [norm_div, norm_pow, norm_pow, hd, ← hneg_norm]
    have hz : ‖z (-(n : ℤ))‖ ≠ 0 := ne_of_gt (lt_trans zero_lt_one hn)
    exact le_of_eq (by field_simp)
  have hs1 : Summable (fun n : ℤ => z n / (1 - z n) ^ 2) :=
    Summable.of_nat_of_neg hpos1 hneg1
  have hs2 : Summable (fun n : ℤ => (z n) ^ 2 / (1 - z n) ^ 3) :=
    Summable.of_nat_of_neg hpos2 hneg2
  constructor
  · simpa only [Function.comp_def, z, Q, v, qΩ, map_div₀, map_pow, map_sub, map_one,
      map_mul, map_zpow₀, IntermediateField.algebraMap_apply,
      IntermediateField.coe_algebraMap_apply] using
      hs1.map (algebraMap E Ω) continuous_subtype_val
  · simpa only [Function.comp_def, z, Q, v, qΩ, map_div₀, map_pow, map_sub, map_one,
      map_mul, map_zpow₀, IntermediateField.algebraMap_apply,
      IntermediateField.coe_algebraMap_apply] using
      hs2.map (algebraMap E Ω) continuous_subtype_val
