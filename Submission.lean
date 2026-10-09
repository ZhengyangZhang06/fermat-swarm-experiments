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


theorem Submission.p03_odd_prepsi_degree_lc_68cf3476
    (F : Type) [Field F] [CharZero F] [DecidableEq F]
    (W : WeierstrassCurve F) (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n) :
    (W.preΨ' n).natDegree = (n ^ 2 - 1) / 2 ∧
      (W.preΨ' n).leadingCoeff = (n : F) := by
  -- Local specialization of DivisionPolynomial/Degree.lean at the pinned mathlib
  -- revision db584cd6d46c92f209a44c0f1c829460d327499d (David Kurniadi Angdinata,
  -- Apache 2.0). Its public formulas are not exported by the frozen imports.
  have degree₂ : W.Ψ₂Sq.natDegree ≤ 3 := by
    rw [Ψ₂Sq]
    compute_degree
  have coeff₂ : W.Ψ₂Sq.coeff 3 = 4 := by
    rw [Ψ₂Sq]
    compute_degree!
  have degree₃ : W.Ψ₃.natDegree ≤ 4 := by
    rw [Ψ₃]
    compute_degree
  have coeff₃ : W.Ψ₃.coeff 4 = 3 := by
    rw [Ψ₃]
    compute_degree!
  have degree₄ : W.preΨ₄.natDegree ≤ 6 := by
    rw [preΨ₄]
    compute_degree
  have coeff₄ : W.preΨ₄.coeff 6 = 2 := by
    rw [preΨ₄]
    compute_degree!
  let expDegree (k : ℕ) : ℕ := (k ^ 2 - if Even k then 4 else 1) / 2
  have expDegree_cast {k : ℕ} (hk : k ≠ 0) :
      2 * (expDegree k : ℤ) = k ^ 2 - if Even k then 4 else 1 := by
    rcases k.even_or_odd' with ⟨k, rfl | rfl⟩
    · rcases k with _ | k
      · contradiction
      push_cast [expDegree, show (2 * (k + 1)) ^ 2 = 2 * (2 * k * (k + 2)) + 4 by ring1,
        even_two_mul, Nat.add_sub_cancel, Nat.mul_div_cancel_left _ two_pos]
      ring1
    · push_cast [expDegree, show (2 * k + 1) ^ 2 = 2 * (2 * k * (k + 1)) + 1 by ring1,
        k.not_even_two_mul_add_one, Nat.add_sub_cancel, Nat.mul_div_cancel_left _ two_pos]
      ring1
  have expDegree_rec (m : ℕ) :
      (expDegree (2 * (m + 3)) =
        2 * expDegree (m + 2) + expDegree (m + 3) + expDegree (m + 5) ∧
      expDegree (2 * (m + 3)) =
        expDegree (m + 1) + expDegree (m + 3) + 2 * expDegree (m + 4)) ∧
      (expDegree (2 * (m + 2) + 1) =
        expDegree (m + 4) + 3 * expDegree (m + 2) + (if Even m then 2 * 3 else 0) ∧
      expDegree (2 * (m + 2) + 1) =
        expDegree (m + 1) + 3 * expDegree (m + 3) + (if Even m then 0 else 2 * 3)) := by
    push_cast [← @Nat.cast_inj ℤ,
      ← mul_left_cancel_iff_of_pos (b := (expDegree _ : ℤ)) two_pos,
      mul_add, mul_left_comm (2 : ℤ)]
    repeat rw [expDegree_cast <| by lia]
    push_cast [Nat.even_add_one, ite_not, even_two_mul]
    constructor <;> constructor <;> split_ifs <;> ring1
  let expCoeff (k : ℕ) : ℤ := if Even k then k / 2 else k
  have expCoeff_cast (k : ℕ) :
      (expCoeff k : ℚ) = if Even k then (k / 2 : ℚ) else k := by
    rcases k.even_or_odd' with ⟨k, rfl | rfl⟩ <;> simp [expCoeff, k.not_even_two_mul_add_one]
  have expCoeff_rec (m : ℕ) :
      (expCoeff (2 * (m + 3)) =
        expCoeff (m + 2) ^ 2 * expCoeff (m + 3) * expCoeff (m + 5) -
          expCoeff (m + 1) * expCoeff (m + 3) * expCoeff (m + 4) ^ 2) ∧
      (expCoeff (2 * (m + 2) + 1) =
        expCoeff (m + 4) * expCoeff (m + 2) ^ 3 * (if Even m then 4 ^ 2 else 1) -
          expCoeff (m + 1) * expCoeff (m + 3) ^ 3 * (if Even m then 1 else 4 ^ 2)) := by
    push_cast [← @Int.cast_inj ℚ, expCoeff_cast, even_two_mul, m.not_even_two_mul_add_one,
      Nat.even_add_one, ite_not]
    constructor <;> split_ifs <;> ring1
  have degree_coeff (k : ℕ) :
      (W.preΨ' k).natDegree ≤ expDegree k ∧
        (W.preΨ' k).coeff (expDegree k) = (expCoeff k : F) := by
    let dm {i j : ℕ} {p q : Polynomial F} :
        p.natDegree ≤ i → q.natDegree ≤ j → (p * q).natDegree ≤ i + j :=
      Polynomial.natDegree_mul_le_of_le
    let dp {i j : ℕ} {p : Polynomial F} :
        p.natDegree ≤ i → (p ^ j).natDegree ≤ j * i :=
      Polynomial.natDegree_pow_le_of_le j
    let cm {i j : ℕ} {p q : Polynomial F} :
        p.natDegree ≤ i → q.natDegree ≤ j → (p * q).coeff (i + j) = p.coeff i * q.coeff j :=
      Polynomial.coeff_mul_add_eq_of_natDegree_le
    let cp {i j : ℕ} {p : Polynomial F} :
        p.natDegree ≤ j → (p ^ i).coeff (i * j) = p.coeff j ^ i :=
      Polynomial.coeff_pow_of_natDegree_le
    induction k using normEDSRec with
    | zero => simpa only [preΨ'_zero] using ⟨Polynomial.natDegree_zero.le, Int.cast_zero.symm⟩
    | one => simpa only [preΨ'_one] using
        ⟨Polynomial.natDegree_one.le, Polynomial.coeff_one_zero.trans Int.cast_one.symm⟩
    | two => simpa only [preΨ'_two] using
        ⟨Polynomial.natDegree_one.le, Polynomial.coeff_one_zero.trans Int.cast_one.symm⟩
    | three => simpa only [preΨ'_three] using ⟨degree₃, coeff₃ ▸ Int.cast_three.symm⟩
    | four => simpa only [preΨ'_four] using ⟨degree₄, coeff₄ ▸ Int.cast_two.symm⟩
    | even m h₁ h₂ h₃ h₄ h₅ =>
      constructor
      · nth_rw 1 [preΨ'_even, ← max_self <| expDegree _,
          (expDegree_rec m).1.1, (expDegree_rec m).1.2]
        exact Polynomial.natDegree_sub_le_of_le
          (dm (dm (dp h₂.1) h₃.1) h₅.1) (dm (dm h₁.1 h₃.1) (dp h₄.1))
      · nth_rw 1 [preΨ'_even, Polynomial.coeff_sub, (expDegree_rec m).1.1,
          cm (dm (dp h₂.1) h₃.1) h₅.1, cm (dp h₂.1) h₃.1, cp h₂.1,
          h₂.2, h₃.2, h₅.2, (expDegree_rec m).1.2,
          cm (dm h₁.1 h₃.1) (dp h₄.1), cm h₁.1 h₃.1, h₁.2, cp h₄.1,
          h₃.2, h₄.2, (expCoeff_rec m).1]
        norm_cast
    | odd m h₁ h₂ h₃ h₄ =>
      rw [preΨ'_odd]
      constructor
      · nth_rw 1 [← max_self <| expDegree _, (expDegree_rec m).2.1, (expDegree_rec m).2.2]
        refine Polynomial.natDegree_sub_le_of_le
          (dm (dm h₄.1 (dp h₂.1)) ?_) (dm (dm h₁.1 (dp h₃.1)) ?_) <;>
          split_ifs <;> simp only [Polynomial.natDegree_one.le, dp degree₂]
      · nth_rw 1 [Polynomial.coeff_sub, (expDegree_rec m).2.1, cm (dm h₄.1 (dp h₂.1)),
          cm h₄.1 (dp h₂.1), h₄.2, cp h₂.1, h₂.2, apply_ite₂ Polynomial.coeff,
          cp degree₂, coeff₂, Polynomial.coeff_one_zero, (expDegree_rec m).2.2,
          cm (dm h₁.1 (dp h₃.1)), cm h₁.1 (dp h₃.1), h₁.2, cp h₃.1, h₃.2,
          apply_ite₂ Polynomial.coeff, cp degree₂, Polynomial.coeff_one_zero,
          coeff₂, (expCoeff_rec m).2]
        · norm_cast
        all_goals split_ifs <;> simp only [Polynomial.natDegree_one.le, dp degree₂]
  have hn0 : n ≠ 0 := ne_of_gt (lt_of_lt_of_le (by decide : 0 < 3) hn)
  have hnF : (n : F) ≠ 0 := Nat.cast_ne_zero.mpr hn0
  have hneven : ¬ Even n := Nat.not_even_iff_odd.mpr hodd
  have hdegree : (W.preΨ' n).natDegree ≤ (n ^ 2 - 1) / 2 := by
    simpa only [expDegree, if_neg hneven] using (degree_coeff n).1
  have hcoeff : (W.preΨ' n).coeff ((n ^ 2 - 1) / 2) = (n : F) := by
    simpa only [expDegree, expCoeff, if_neg hneven, Int.cast_natCast] using (degree_coeff n).2
  have hdegree_eq : (W.preΨ' n).natDegree = (n ^ 2 - 1) / 2 :=
    Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hdegree (hcoeff ▸ hnF)
  exact ⟨hdegree_eq, by rw [Polynomial.leadingCoeff, hdegree_eq, hcoeff]⟩
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


theorem Submission.p03_eds_recurrence_unique_68cf3476_d3 :
    ∀ (R : Type) [CommRing R] [IsDomain R] (h : R), h ≠ 0 →
      ∀ f g : ℕ → R,
        (∀ n : ℕ, n ≤ 4 → f n = g n) →
        (∀ r : ℕ, 2 ≤ r →
          f (2 * r + 1) = f (r + 2) * f r ^ 3 - f (r - 1) * f (r + 1) ^ 3) →
        (∀ r : ℕ, 3 ≤ r →
          h * f (2 * r) =
            f r * (f (r + 2) * f (r - 1) ^ 2 - f (r - 2) * f (r + 1) ^ 2)) →
        (∀ r : ℕ, 2 ≤ r →
          g (2 * r + 1) = g (r + 2) * g r ^ 3 - g (r - 1) * g (r + 1) ^ 3) →
        (∀ r : ℕ, 3 ≤ r →
          h * g (2 * r) =
            g r * (g (r + 2) * g (r - 1) ^ 2 - g (r - 2) * g (r + 1) ^ 2)) →
        ∀ n : ℕ, f n = g n := by
  intro R _ _ h hh f g hinit hfodd hfeven hgodd hgeven n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n ≤ 4
    · exact hinit n hn
    · rcases n.even_or_odd' with ⟨r, rfl | rfl⟩
      · have hr : 3 ≤ r := by omega
        apply mul_left_cancel₀ hh
        rw [hfeven r hr, hgeven r hr,
          ih r (by omega), ih (r + 2) (by omega), ih (r - 1) (by omega),
          ih (r - 2) (by omega), ih (r + 1) (by omega)]
      · have hr : 2 ≤ r := by omega
        rw [hfodd r hr, hgodd r hr,
          ih (r + 2) (by omega), ih r (by omega),
          ih (r - 1) (by omega), ih (r + 1) (by omega)]

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
theorem Submission.p03_eds_canonical_even_recurrence_68cf3476_d4 :
    ∀ (k : Type) [Field k] [CharZero k] [DecidableEq k] (W : WeierstrassCurve k),
      let q := WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine
      let h := q W.ψ₂
      let F : ℕ → W.toAffine.CoordinateRing :=
        fun n => q (Polynomial.C (W.preΨ' n)) * (if Even n then h else 1)
      ∀ r : ℕ, 3 ≤ r →
        h * F (2 * r) =
          F r * (F (r + 2) * F (r - 1) ^ 2 - F (r - 2) * F (r + 1) ^ 2) := by
  intro k _ _ _ W q h F r hr
  let a : ℕ → W.toAffine.CoordinateRing := fun n => q (Polynomial.C (W.preΨ' n))
  have hi₁ : r - 3 + 1 = r - 2 := by omega
  have hi₂ : r - 3 + 2 = r - 1 := by omega
  have hi₃ : r - 3 + 3 = r := by omega
  have hi₄ : r - 3 + 4 = r + 1 := by omega
  have hi₅ : r - 3 + 5 = r + 2 := by omega
  -- Pinned mathlib DivisionPolynomial/Basic.lean, revision
  -- db584cd6d46c92f209a44c0f1c829460d327499d, supplies preΨ'_even.
  have hrec := congrArg (fun p : Polynomial k => q (Polynomial.C p))
    (W.preΨ'_even (r - 3))
  simp only [hi₁, hi₂, hi₃, hi₄, hi₅, map_sub, map_mul, map_pow] at hrec
  change a (2 * r) =
    a (r - 1) ^ 2 * a r * a (r + 2) - a (r - 2) * a r * a (r + 1) ^ 2 at hrec
  have hsub₁ : Even (r - 1) ↔ ¬Even r := by
    rw [Nat.even_sub (by omega : 1 ≤ r)]
    simp
  have hsub₂ : Even (r - 2) ↔ Even r := by
    rw [Nat.even_sub (by omega : 2 ≤ r)]
    simp
  have hadd₂ : Even (r + 2) ↔ Even r := by simp [Nat.even_add]
  change h * (a (2 * r) * (if Even (2 * r) then h else 1)) =
    (a r * (if Even r then h else 1)) *
      ((a (r + 2) * (if Even (r + 2) then h else 1)) *
          (a (r - 1) * (if Even (r - 1) then h else 1)) ^ 2 -
        (a (r - 2) * (if Even (r - 2) then h else 1)) *
          (a (r + 1) * (if Even (r + 1) then h else 1)) ^ 2)
  rw [if_pos (even_two_mul r), hrec]
  by_cases he : Even r <;>
    simp only [hsub₁, hsub₂, hadd₂, Nat.even_add_one, he, not_true_eq_false,
      not_false_eq_true, ite_true, ite_false, mul_one] <;> ring

theorem Submission.p03_eds_canonical_odd_recurrence_68cf3476_d4 :
    ∀ (k : Type) [Field k] [CharZero k] [DecidableEq k] (W : WeierstrassCurve k),
      let q := WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine
      let h := q W.ψ₂
      let F : ℕ → W.toAffine.CoordinateRing :=
        fun n => q (Polynomial.C (W.preΨ' n)) * (if Even n then h else 1)
      ∀ r : ℕ, 2 ≤ r →
        F (2 * r + 1) = F (r + 2) * F r ^ 3 - F (r - 1) * F (r + 1) ^ 3 := by
  intro k _ _ _ W q h F r hr
  have hs : h ^ 2 = q (Polynomial.C W.Ψ₂Sq) := CoordinateRing.mk_ψ₂_sq W
  have hfour : h ^ 4 = q (Polynomial.C W.Ψ₂Sq) ^ 2 := by
    rw [show 4 = 2 * 2 by rfl, pow_mul, hs]
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 2 := ⟨r - 2, by omega⟩
  have hrec := congrArg (fun p : Polynomial k => q (Polynomial.C p)) (W.preΨ'_odd m)
  have hsub : m + 2 - 1 = m + 1 := by omega
  by_cases he : Even m
  · simp only [if_pos he, map_sub, map_mul, map_pow, mul_one] at hrec
    simp only [F, hsub, Nat.add_assoc]
    simp [Nat.even_add, he, show Even (4 : ℕ) by decide,
      show ¬ Even (3 : ℕ) by decide]
    rw [hrec, ← hfour]
    ring
  · simp only [if_neg he, map_sub, map_mul, map_pow, mul_one] at hrec
    simp only [F, hsub, Nat.add_assoc]
    simp [Nat.even_add, he, show Even (4 : ℕ) by decide,
      show ¬ Even (3 : ℕ) by decide]
    rw [hrec, ← hfour]
    ring
theorem Submission.p03_eds_two_torsion_four_sum_68cf3476_d5 :
    ∀ (G : Type) [AddCommGroup G] [DecidableEq G] (T : Finset G),
      (∀ x : G, x ∈ T ↔ (2 : ℕ) • x = 0) → T.card = 4 →
        T.sum (fun x => x) = 0 := by
  intro G _ _ T hT hcard
  have hzero : (0 : G) ∈ T := (hT 0).2 (smul_zero 2)
  obtain ⟨u, hu, hu_not⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({0} : Finset G)) (t := T) (by simp [hcard])
  have hu0 : u ≠ 0 := by simpa only [Finset.mem_singleton] using hu_not
  obtain ⟨v, hv, hv_not⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({0, u} : Finset G)) (t := T)
    (lt_of_le_of_lt Finset.card_le_two (by omega))
  have hv_ne : v ≠ 0 ∧ v ≠ u := by
    simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hv_not
  have huu : u + u = 0 := by simpa only [two_nsmul] using (hT u).1 hu
  have hvv : v + v = 0 := by simpa only [two_nsmul] using (hT v).1 hv
  have huv_mem : u + v ∈ T := by
    apply (hT (u + v)).2
    rw [smul_add, (hT u).1 hu, (hT v).1 hv, add_zero]
  have huv0 : u + v ≠ 0 := by
    intro h
    apply hv_ne.2
    calc
      v = u + (u + v) := by rw [← add_assoc, huu, zero_add]
      _ = u := by rw [h, add_zero]
  have huv_u : u + v ≠ u := by
    intro h
    exact hv_ne.1 (add_left_cancel (h.trans (add_zero u).symm))
  have huv_v : u + v ≠ v := by
    intro h
    exact hu0 (add_right_cancel (h.trans (zero_add v).symm))
  have hset : ({u + v, v, u, 0} : Finset G) = T := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact huv_mem
      · exact hv
      · exact hu
      · exact hzero
    · simp [hcard, Finset.card_insert_of_notMem, huv_v, huv_u, huv0,
        hv_ne.2, hv_ne.1, hu0]
  calc
    T.sum (fun x => x) = (u + v) + (v + u) := by
      rw [← hset]
      simp [huv_v, huv_u, huv0, hv_ne.2, hv_ne.1, hu0]
    _ = (u + u) + (v + v) := by abel
    _ = 0 := by rw [huu, hvv, add_zero]
theorem Submission.p03_eds_negation_fixed_sum_68cf3476_d5 :
    ∀ (G : Type) [AddCommGroup G] [DecidableEq G] (S : Finset G),
      (∀ x ∈ S, -x ∈ S) →
        S.sum (fun x => x) = (S.filter (fun x => (2 : ℕ) • x = 0)).sum (fun x => x) := by
  intro G _ _ S
  induction S using Finset.strongInduction with | H S ih => ?_
  intro hS
  by_cases hfixed : ∀ x ∈ S, (2 : ℕ) • x = 0
  · rw [Finset.filter_eq_self.mpr hfixed]
  push Not at hfixed
  obtain ⟨a, ha, ha2⟩ := hfixed
  have hna : -a ∈ S := hS a ha
  have hne : a ≠ -a := by
    intro h
    apply ha2
    simpa only [two_nsmul] using (eq_neg_iff_add_eq_zero.mp h)
  have hna2 : (2 : ℕ) • (-a) ≠ 0 := by
    intro h
    apply ha2
    simpa only [smul_neg, neg_neg, _root_.neg_zero] using congrArg Neg.neg h
  let R := S \ {a, -a}
  have hpair : ({a, -a} : Finset G) ⊆ S := by
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨ha, hna⟩
  have hRlt : R ⊂ S :=
    Finset.sdiff_ssubset hpair (by simp)
  have hR : ∀ x ∈ R, -x ∈ R := by
    intro x hx
    rcases Finset.mem_sdiff.mp hx with ⟨hxS, hxpair⟩
    have hxne : x ≠ a ∧ x ≠ -a := by simpa using hxpair
    apply Finset.mem_sdiff.mpr
    refine ⟨hS x hxS, ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    constructor
    · intro h
      exact hxne.2 (by simpa only [neg_neg] using congrArg Neg.neg h)
    · intro h
      exact hxne.1 (neg_injective h)
  have hfilter : R.filter (fun x => (2 : ℕ) • x = 0) =
      S.filter (fun x => (2 : ℕ) • x = 0) := by
    ext x
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hx, hx2⟩
      exact ⟨Finset.sdiff_subset hx, hx2⟩
    · rintro ⟨hx, hx2⟩
      refine ⟨Finset.mem_sdiff.mpr ⟨hx, ?_⟩, hx2⟩
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => ha2 (h ▸ hx2), fun h => hna2 (h ▸ hx2)⟩
  have hsum : S.sum (fun x => x) = R.sum (fun x => x) := by
    rw [← Finset.sum_sdiff hpair]
    simp only [Finset.sum_pair hne, add_neg_cancel, add_zero, R]
  rw [hsum, ih R hRlt hR, hfilter]
theorem Submission.p03_tkc_two_torsion_card_68cf3476_d5
    (k : Type) [Field k] [CharZero k] [IsAlgClosed k] [DecidableEq k]
    (W : WeierstrassCurve k) (hΔ : W.Δ ≠ 0) :
    Nat.card {P : W.toAffine.Point // (2 : ℕ) • P = 0} = 4 := by
  classical
  -- Pinned mathlib: Cubic.card_roots_of_discr_ne_zero and
  -- WeierstrassCurve.twoTorsionPolynomial_discr count the three affine roots.
  let s := W.twoTorsionPolynomial.roots.toFinset
  have ha : W.twoTorsionPolynomial.a ≠ 0 := by
    change (4 : k) ≠ 0
    norm_num
  have hd : W.twoTorsionPolynomial.discr ≠ 0 := by
    rw [W.twoTorsionPolynomial_discr]
    exact mul_ne_zero (by norm_num) hΔ
  have hs : s.card = 3 := by
    simpa [Cubic.map, s] using
      (Cubic.card_roots_of_discr_ne_zero (φ := RingHom.id k) ha
        (IsAlgClosed.splits _) hd)
  have hroot (x : k) : x ∈ s ↔
      4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ = 0 := by
    rw [Multiset.mem_toFinset, Cubic.mem_roots_iff (Cubic.ne_zero_of_a_ne_zero ha)]
    rfl
  let y₀ : k → k := fun x => -(W.a₁ * x + W.a₃) / 2
  have heq (x : k) : W.toAffine.Equation x (y₀ x) ↔ x ∈ s := by
    rw [hroot, equation_iff']
    dsimp [y₀, b₂, b₄, b₆]
    constructor
    · intro h
      linear_combination -4 * h
    · intro h
      linear_combination -(1 / 4 : k) * h
  have htwo (x y : k) (h : W.toAffine.Nonsingular x y) :
      (2 : ℕ) • (Point.some x y h) = 0 ↔ y = y₀ x := by
    rw [two_nsmul, add_eq_zero_iff_eq_neg, neg_some, Point.some.injEq]
    simp only [true_and, negY]
    dsimp [y₀]
    constructor
    · intro hy
      linear_combination (1 / 2 : k) * hy
    · intro hy
      linear_combination 2 * hy
  let e : {xy : k × k // ∃ h : W.toAffine.Nonsingular xy.1 xy.2,
      (2 : ℕ) • Point.some xy.1 xy.2 h = 0} ≃ s :=
    { toFun := fun xy => ⟨xy.val.1, by
        obtain ⟨h, ht⟩ := xy.property
        have hy := (htwo _ _ h).mp ht
        exact (heq _).mp (hy ▸ h.1)⟩
      invFun := fun x => ⟨(x.val, y₀ x.val), by
        have h := (W.toAffine.equation_iff_nonsingular_of_Δ_ne_zero hΔ).mp
          ((heq _).mpr x.property)
        exact ⟨h, (htwo _ _ h).mpr rfl⟩⟩
      left_inv := by
        intro xy
        apply Subtype.ext
        apply Prod.ext
        · rfl
        · exact ((htwo _ _ xy.property.choose).mp xy.property.choose_spec).symm
      right_inv := by intro x; rfl }
  have e₀ := nonsingularPointEquivSubtype
    (p := fun P : W.toAffine.Point => (2 : ℕ) • P = 0)
    (show (2 : ℕ) • (Point.zero : W.toAffine.Point) = 0 by exact nsmul_zero 2)
  rw [Nat.card_congr (e₀.trans e.optionCongr)]
  change Nat.card (Option s) = 4
  rw [Nat.card_eq_fintype_card, Fintype.card_option, Fintype.card_coe, hs]

theorem Submission.p03_eds_canonical_recurrences_68cf3476_d3 :
    ∀ (k : Type) [Field k] [CharZero k] [DecidableEq k] (W : WeierstrassCurve k),
      let q := WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine
      let h := q W.ψ₂
      let F : ℕ → W.toAffine.CoordinateRing :=
        fun n => q (Polynomial.C (W.preΨ' n)) * (if Even n then h else 1)
      F 0 = 0 ∧ F 1 = 1 ∧ F 2 = h ∧ F 3 = q (Polynomial.C W.Ψ₃) ∧
        F 4 = h * q (Polynomial.C W.preΨ₄) ∧
        (∀ r : ℕ, 2 ≤ r →
          F (2 * r + 1) = F (r + 2) * F r ^ 3 - F (r - 1) * F (r + 1) ^ 3) ∧
        (∀ r : ℕ, 3 ≤ r →
          h * F (2 * r) =
            F r * (F (r + 2) * F (r - 1) ^ 2 - F (r - 2) * F (r + 1) ^ 2)) := by
  intro k _ _ _ W
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_,
    Submission.p03_eds_canonical_odd_recurrence_68cf3476_d4 k W,
    Submission.p03_eds_canonical_even_recurrence_68cf3476_d4 k W⟩
  · simp only [preΨ'_zero, _root_.map_zero, zero_mul]
  · simp only [preΨ'_one, map_one, Nat.not_even_one, if_false, one_mul]
  · simp only [preΨ'_two, map_one, even_two, if_true, one_mul]
  · simp only [preΨ'_three, show ¬ Even (3 : ℕ) by decide, if_false, mul_one]
  · simp only [preΨ'_four, show Even (4 : ℕ) by decide, if_true, mul_comm]
