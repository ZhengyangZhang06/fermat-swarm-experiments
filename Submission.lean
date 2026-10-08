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
theorem Submission.p03_tu_algebraic_aut_isometry_68cf3476 :
    ∀ (F Ω : Type) [NormedField F] [CompleteSpace F] [NormedField Ω]
      [NormedAlgebra F Ω] [Algebra.IsAlgebraic F Ω],
      ∀ q : F, 0 < ‖q‖ → ‖q‖ < 1 →
      ∀ σ : Ω ≃ₐ[F] Ω, Isometry (fun x : Ω => σ x) := by
  intro F Ω _ _ _ _ _ q hq₀ hq₁
  let : NontriviallyNormedField F :=
    { ‹NormedField F› with
      non_trivial := ⟨q⁻¹, by simpa only [norm_inv] using (one_lt_inv₀ hq₀).2 hq₁⟩ }
  have hle (σ : Ω ≃ₐ[F] Ω) (x : Ω) : ‖σ x‖ ≤ ‖x‖ := by
    by_cases hx : x = 0
    · simp [hx]
    let E := IntermediateField.adjoin F ({x} : Set Ω)
    let : FiniteDimensional F E :=
      IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
    let L : E →ₗ[F] Ω := σ.toLinearMap.comp E.val.toLinearMap
    let T : E →L[F] Ω := ⟨L, L.continuous_of_finiteDimensional⟩
    let z : E := ⟨x, IntermediateField.mem_adjoin_simple_self F x⟩
    have hpow (n : ℕ) : ‖σ x‖ ^ n ≤ ‖T‖ * ‖x‖ ^ n := by
      have hb := T.le_opNorm (z ^ n)
      change ‖σ (x ^ n)‖ ≤ ‖T‖ * ‖x ^ n‖ at hb
      simpa only [map_pow, norm_pow] using hb
    have hratio (n : ℕ) : (‖σ x‖ / ‖x‖) ^ n ≤ ‖T‖ := by
      rw [div_pow]
      exact (div_le_iff₀ (pow_pos (norm_pos_iff.mpr hx) n)).2 (hpow n)
    by_contra h
    have hr : 1 < ‖σ x‖ / ‖x‖ :=
      (one_lt_div (norm_pos_iff.mpr hx)).2 (lt_of_not_ge h)
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ‖T‖ hr
    exact (not_lt_of_ge (hratio n)) hn
  intro σ
  have hnorm (x : Ω) : ‖σ x‖ = ‖x‖ := by
    apply le_antisymm (hle σ x)
    simpa only [AlgEquiv.symm_apply_apply] using hle σ.symm (σ x)
  apply isometry_iff_dist_eq.mpr
  intro x y
  rw [dist_eq_norm, dist_eq_norm, ← map_sub, hnorm]

theorem Submission.p03_tu_coordinate_symmetries_68cf3476 :
    ∀ (F Ω : Type) [NormedField F] [CompleteSpace F] [NormedField Ω]
      [NormedAlgebra F Ω] [Algebra.IsAlgebraic F Ω],
      (∀ x y : Ω, ‖x + y‖ ≤ max ‖x‖ ‖y‖) →
      ∀ q : F, 0 < ‖q‖ → ‖q‖ < 1 → ∀ c : F,
      let qΩ : Ω := algebraMap F Ω q
      let X : Ω → Ω := fun u =>
        (∑' n : ℤ, qΩ ^ n * u / (1 - qΩ ^ n * u) ^ 2) - 2 * algebraMap F Ω c
      let Y : Ω → Ω := fun u =>
        (∑' n : ℤ, (qΩ ^ n * u) ^ 2 / (1 - qΩ ^ n * u) ^ 3) + algebraMap F Ω c
      ∀ u : Ωˣ, (¬ ∃ m : ℤ, (u : Ω) = qΩ ^ m) →
        X (qΩ * (u : Ω)) = X (u : Ω) ∧
        Y (qΩ * (u : Ω)) = Y (u : Ω) ∧
        X ((u : Ω)⁻¹) = X (u : Ω) ∧
        Y ((u : Ω)⁻¹) = -Y (u : Ω) - X (u : Ω) ∧
        ∀ σ : Ω ≃ₐ[F] Ω,
          X (σ (u : Ω)) = σ (X (u : Ω)) ∧
          Y (σ (u : Ω)) = σ (Y (u : Ω)) := by
  intro F Ω _ _ _ _ _ hΩ q hq0 hq1 c qΩ X Y u hu
  let A : Ω → Ω := fun z => z / (1 - z) ^ 2
  let B : Ω → Ω := fun z => z ^ 2 / (1 - z) ^ 3
  have hQ0 : qΩ ≠ 0 := by
    apply norm_pos_iff.mp
    simpa only [qΩ, norm_algebraMap'] using hq0
  obtain ⟨hsA, hsB⟩ :=
    Submission.p03_tu_bilateral_summable_68cf3476 F Ω hΩ q hq0 hq1 u hu
  change Summable (fun n : ℤ => A (qΩ ^ n * (u : Ω))) at hsA
  change Summable (fun n : ℤ => B (qΩ ^ n * (u : Ω))) at hsB
  have hz0 (n : ℤ) : qΩ ^ n * (u : Ω) ≠ 0 :=
    mul_ne_zero (zpow_ne_zero n hQ0) u.ne_zero
  have hz1 (n : ℤ) : 1 - qΩ ^ n * (u : Ω) ≠ 0 := by
    intro h
    have hh : qΩ ^ n * (u : Ω) = 1 := (sub_eq_zero.mp h).symm
    apply hu
    refine ⟨-n, ?_⟩
    calc
      (u : Ω) = (qΩ ^ n)⁻¹ * (qΩ ^ n * (u : Ω)) := by
        rw [← mul_assoc, inv_mul_cancel₀ (zpow_ne_zero n hQ0), one_mul]
      _ = qΩ ^ (-n) := by rw [hh, mul_one, zpow_neg]
  have hinv (z : Ω) (hz : z ≠ 0) (hd : 1 - z ≠ 0) :
      A z⁻¹ = A z ∧ B z⁻¹ = -B z - A z := by
    have he : 1 - z⁻¹ = -(1 - z) / z := by
      field_simp
      ring
    dsimp only [A, B]
    rw [he]
    constructor
    · field_simp
    · field_simp
      ring
  have hshift (g : Ω → Ω) :
      (∑' n : ℤ, g (qΩ ^ n * (qΩ * (u : Ω)))) =
        ∑' n : ℤ, g (qΩ ^ n * (u : Ω)) := by
    calc
      _ = ∑' n : ℤ, g (qΩ ^ (n + 1) * (u : Ω)) := by
        apply tsum_congr
        intro n
        rw [zpow_add₀ hQ0, zpow_one, mul_assoc]
      _ = _ := (Equiv.addRight (1 : ℤ)).tsum_eq (fun n : ℤ => g (qΩ ^ n * (u : Ω)))
  have hAsumInv :
      (∑' n : ℤ, A (qΩ ^ n * (u : Ω)⁻¹)) =
        ∑' n : ℤ, A (qΩ ^ n * (u : Ω)) := by
    calc
      _ = ∑' n : ℤ, A (qΩ ^ (-n) * (u : Ω)⁻¹) :=
        (tsum_comp_neg (fun n : ℤ => A (qΩ ^ n * (u : Ω)⁻¹))).symm
      _ = _ := by
        apply tsum_congr
        intro n
        simpa only [zpow_neg, mul_inv_rev, mul_comm] using
          (hinv (qΩ ^ n * (u : Ω)) (hz0 n) (hz1 n)).1
  have hBsumInv :
      (∑' n : ℤ, B (qΩ ^ n * (u : Ω)⁻¹)) =
        -(∑' n : ℤ, B (qΩ ^ n * (u : Ω))) -
          ∑' n : ℤ, A (qΩ ^ n * (u : Ω)) := by
    calc
      _ = ∑' n : ℤ, B (qΩ ^ (-n) * (u : Ω)⁻¹) :=
        (tsum_comp_neg (fun n : ℤ => B (qΩ ^ n * (u : Ω)⁻¹))).symm
      _ = ∑' n : ℤ, (-B (qΩ ^ n * (u : Ω)) - A (qΩ ^ n * (u : Ω))) := by
        apply tsum_congr
        intro n
        simpa only [zpow_neg, mul_inv_rev, mul_comm] using
          (hinv (qΩ ^ n * (u : Ω)) (hz0 n) (hz1 n)).2
      _ = _ := by rw [hsB.neg.tsum_sub hsA, tsum_neg]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact congrArg (fun s : Ω => s - 2 * algebraMap F Ω c) (hshift A)
  · exact congrArg (fun s : Ω => s + algebraMap F Ω c) (hshift B)
  · exact congrArg (fun s : Ω => s - 2 * algebraMap F Ω c) hAsumInv
  · change (∑' n : ℤ, B (qΩ ^ n * (u : Ω)⁻¹)) + algebraMap F Ω c =
      -((∑' n : ℤ, B (qΩ ^ n * (u : Ω))) + algebraMap F Ω c) -
        ((∑' n : ℤ, A (qΩ ^ n * (u : Ω))) - 2 * algebraMap F Ω c)
    rw [hBsumInv]
    ring
  · intro σ
    have hσ : Continuous (fun x : Ω => σ x) :=
      (Submission.p03_tu_algebraic_aut_isometry_68cf3476 F Ω q hq0 hq1 σ).continuous
    have hσQ : σ qΩ = qΩ := σ.commutes q
    have hAsumMap :
        (∑' n : ℤ, A (qΩ ^ n * σ (u : Ω))) =
          σ (∑' n : ℤ, A (qΩ ^ n * (u : Ω))) := by
      rw [hsA.map_tsum σ hσ]
      apply tsum_congr
      intro n
      simp only [A, map_div₀, map_pow, map_sub, map_one, map_mul, map_zpow₀, hσQ]
    have hBsumMap :
        (∑' n : ℤ, B (qΩ ^ n * σ (u : Ω))) =
          σ (∑' n : ℤ, B (qΩ ^ n * (u : Ω))) := by
      rw [hsB.map_tsum σ hσ]
      apply tsum_congr
      intro n
      simp only [B, map_div₀, map_pow, map_sub, map_one, map_mul, map_zpow₀, hσQ]
    constructor
    · change (∑' n : ℤ, A (qΩ ^ n * σ (u : Ω))) - 2 * algebraMap F Ω c =
        σ ((∑' n : ℤ, A (qΩ ^ n * (u : Ω))) - 2 * algebraMap F Ω c)
      rw [hAsumMap, map_sub, map_mul, map_ofNat, σ.commutes]
    · change (∑' n : ℤ, B (qΩ ^ n * σ (u : Ω))) + algebraMap F Ω c =
        σ ((∑' n : ℤ, B (qΩ ^ n * (u : Ω))) + algebraMap F Ω c)
      rw [hBsumMap, map_add, σ.commutes]
