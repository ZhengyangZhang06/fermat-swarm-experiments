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

theorem Submission.p03_ptf_positive_nsmul_nonzero_c5b7b5ed_d6 :
    ∀ (k : Type) [Field k] [CharZero k] [IsAlgClosed k] [DecidableEq k]
      (W : WeierstrassCurve k), W.Δ ≠ 0 → ∀ n : ℕ, 0 < n →
        ∃ P : W.toAffine.Point, n • P ≠ 0 := by
  intro k _ _ _ _ W hΔ
  classical
  have root (p : Polynomial k) (m : ℕ) (hm : 0 < m) (hc : p.coeff m ≠ 0) :
      ∃ x : k, p.eval x = 0 := by
    apply IsAlgClosed.exists_root p
    intro hd
    apply hc
    apply Polynomial.coeff_eq_zero_of_degree_lt
    rw [hd]
    exact WithBot.coe_lt_coe.mpr hm
  have point (x : k) : ∃ y : k, W.toAffine.Nonsingular x y := by
    let p : Polynomial k := Polynomial.X ^ 2 +
      Polynomial.C (W.a₁ * x + W.a₃) * Polynomial.X -
      Polynomial.C (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)
    have hc : p.coeff 2 = 1 := by dsimp [p]; compute_degree!
    obtain ⟨y, hy⟩ := root p 2 (by omega) (by rw [hc]; exact one_ne_zero)
    refine ⟨y, (equation_iff_nonsingular_of_Δ_ne_zero hΔ).mp ?_⟩
    rw [equation_iff]
    simp only [p, Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] at hy
    linear_combination hy
  have disc (x y : k) (h : W.toAffine.Nonsingular x y) :
      (2 * y + W.a₁ * x + W.a₃) ^ 2 =
        4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ := by
    have he := (equation_iff x y).mp h.1
    simp only [b₂, b₄, b₆]
    linear_combination 4 * he
  have torsion : ∃ T : W.toAffine.Point, T ≠ 0 ∧ 2 • T = 0 := by
    let p : Polynomial k := Polynomial.C 4 * Polynomial.X ^ 3 +
      Polynomial.C W.b₂ * Polynomial.X ^ 2 +
      Polynomial.C (2 * W.b₄) * Polynomial.X + Polynomial.C W.b₆
    have hc : p.coeff 3 = 4 := by dsimp [p]; compute_degree!
    obtain ⟨x, hx⟩ := root p 3 (by omega) (by rw [hc]; norm_num)
    obtain ⟨y, hxy⟩ := point x
    simp only [p, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C] at hx
    have ht : 2 * y + W.a₁ * x + W.a₃ = 0 := by
      apply eq_zero_of_pow_eq_zero (n := 2)
      apply pow_eq_zero (n := 2)
      exact (disc x y hxy).trans hx
    have hy : y = W.toAffine.negY x y := by
      dsimp only [negY]
      linear_combination ht
    refine ⟨some x y hxy, some_ne_zero hxy, ?_⟩
    rw [two_nsmul, add_self_of_Y_eq hy]
  have half (P : W.toAffine.Point) :
      ∃ Q : W.toAffine.Point, 2 • Q = P ∨ 2 • Q = -P := by
    cases P with
    | zero =>
      refine ⟨0, Or.inl ?_⟩
      change (2 : ℕ) • (0 : W.toAffine.Point) = 0
      exact nsmul_zero 2
    | zero => exact ⟨0, Or.inl (by simp [zero_def])⟩
    | some u v huv =>
      let p : Polynomial k := Polynomial.X ^ 4 -
        Polynomial.C W.b₄ * Polynomial.X ^ 2 -
        Polynomial.C (2 * W.b₆) * Polynomial.X - Polynomial.C W.b₈ -
        Polynomial.C u * (Polynomial.C 4 * Polynomial.X ^ 3 +
          Polynomial.C W.b₂ * Polynomial.X ^ 2 +
          Polynomial.C (2 * W.b₄) * Polynomial.X + Polynomial.C W.b₆)
      have hc : p.coeff 4 = 1 := by dsimp [p]; compute_degree!
      obtain ⟨x, hx⟩ := root p 4 (by omega) (by rw [hc]; exact one_ne_zero)
      obtain ⟨y, hxy⟩ := point x
      have he := (equation_iff x y).mp hxy.1
      simp only [p, Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, b₂, b₄, b₆, b₈] at hx
      let t := 2 * y + W.a₁ * x + W.a₃
      let z := 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y
      have hz : z ^ 2 + W.a₁ * z * t - (W.a₂ + 2 * x + u) * t ^ 2 = 0 := by
        dsimp [z, t]
        linear_combination hx - (W.a₁ ^ 2 + 4 * W.a₂ + 8 * x + 4 * u) * he
      have ht : t ≠ 0 := by
        intro ht
        have hz0 : z = 0 := by
          apply eq_zero_of_pow_eq_zero (n := 2)
          apply pow_eq_zero (n := 2)
          simpa only [ht, mul_zero, zero_pow (by omega : 2 ≠ 0), add_zero,
            sub_zero] using hz
        rcases ((nonsingular_iff' x y).mp hxy).2 with h | h
        · apply h
          dsimp [z] at hz0
          linear_combination -hz0
        · exact h ht
      have hy : y ≠ W.toAffine.negY x y := by
        intro hy
        apply ht
        dsimp only [t, negY] at *
        linear_combination hy
      have hx' : W.toAffine.addX x x (W.toAffine.slope x x y y) = u := by
        have htdef : y - W.toAffine.negY x y = t := by
          dsimp [negY, t]
          ring
        rw [slope_of_Y_ne rfl hy, addX, htdef]
        rw [slope_of_Y_ne rfl hy, addX]
        change (z / t) ^ 2 + W.a₁ * (z / t) - W.a₂ - x - x = u
        have hmul : ((z / t) ^ 2 + W.a₁ * (z / t) - W.a₂ - x - x - u) *
            t ^ 2 = 0 := by
          calc
            _ = z ^ 2 + W.a₁ * z * t - (W.a₂ + 2 * x + u) * t ^ 2 := by
              field_simp [ht]
              ring
              field_simp
              <;> ring
            _ = 0 := hz
        exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_right (pow_ne_zero 2 ht))
      refine ⟨some x y hxy, ?_⟩
      rw [two_nsmul, add_self_of_Y_ne hy]
      exact X_eq_iff.mp hx'
  obtain ⟨T, hT, hT2⟩ := torsion
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
    · obtain ⟨P, hP⟩ := ih m (by omega) (by omega)
      obtain ⟨Q, hQ | hQ⟩ := half P
      · refine ⟨Q, ?_⟩
        simpa only [mul_nsmul, hQ] using hP
      · refine ⟨Q, ?_⟩
        simpa only [mul_nsmul, hQ, smul_neg, neg_ne_zero] using hP
    · refine ⟨T, ?_⟩
      simpa only [add_nsmul, mul_nsmul, hT2, nsmul_zero, one_nsmul,
        zero_add] using hT
theorem Submission.p03_ptf_finite_kernel_of_nsmul_nonzero_c5b7b5ed_d6 :
    ∀ (k : Type) [Field k] [IsAlgClosed k] [DecidableEq k] (W : WeierstrassCurve k),
      W.Δ ≠ 0 → ∀ n : ℕ, (∃ P : W.toAffine.Point, n • P ≠ 0) →
        Finite {P : W.toAffine.Point // n • P = 0} := by
  intro k _ _ _ W _hΔ n ⟨Q, hQ⟩
  classical
  rcases Q with _ | ⟨x₀, y₀, h₀⟩
  · exact False.elim (hQ (nsmul_zero n))
  -- Use the affine coordinate ring to make the finite-fiber argument explicit.
  -- The basis, norm, and addition formulas below are from pinned mathlib
  -- db584cd6d46c92f209a44c0f1c829460d327499d, EllipticCurve/Affine/Point.lean.
  let G := W.toAffine.Point
  let A := W.toAffine.CoordinateRing
  let : Module.Finite (Polynomial k) A := Module.Finite.of_basis (CoordinateRing.basis W.toAffine)
  let ev : G → A →+* k := fun P => match P with
    | .zero => AdjoinRoot.evalEval h₀.1
    | .some x y h => AdjoinRoot.evalEval h.1
  have ev_mk (x y : k) (h : W.toAffine.Nonsingular x y)
      (p : Polynomial (Polynomial k)) :
      ev (.some x y h) (CoordinateRing.mk W.toAffine p) = p.evalEval x y := by
    exact AdjoinRoot.evalEval_mk h.1 p
  have ev_basis (x y : k) (h : W.toAffine.Nonsingular x y) (p q : Polynomial k) :
      ev (.some x y h) (p • (1 : A) + q • CoordinateRing.mk W.toAffine Polynomial.X) =
        p.eval x + q.eval x * y := by
    rw [CoordinateRing.smul p (1 : A), CoordinateRing.smul q]
    simp only [map_add, map_mul, mul_one, ev_mk x y h,
      Polynomial.evalEval_C, Polynomial.evalEval_X]
  have hxf (x : k) : Set.Finite {P : G | P.xRep 0 = x} := by
    by_cases h : ∃ y, W.toAffine.Nonsingular x y
    · obtain ⟨y, hy⟩ := h
      apply (((Set.finite_singleton (-.some x y hy)).insert (.some x y hy)).insert 0).subset
      intro P hp
      cases P with
      | zero => simp [← zero_def]
      | some u v hv =>
        have hu : u = x := hp
        rcases (X_eq_iff (h₁ := hv) (h₂ := hy)).mp hu with he | he
        · exact Or.inr (Or.inl he)
        · exact Or.inr (Or.inr he)
    · apply (Set.finite_singleton (0 : G)).subset
      intro P hp
      cases P with
      | zero => rfl
      | some u v hv => exact (h ⟨v, (show u = x from hp) ▸ hv⟩).elim
  have ev_nonzero (a : A) (ha : a ≠ 0) : ∀ᶠ P in Filter.cofinite, ev P a ≠ 0 := by
    have hn : Algebra.norm (Polynomial k) a ≠ 0 := Algebra.norm_ne_zero_iff.mpr ha
    have hf := (Polynomial.finite_setOfPred_isRoot hn).biUnion (fun x _ => hxf x)
    apply Filter.eventually_cofinite.mpr
    apply ((Set.finite_singleton (0 : G)).union hf).subset
    intro P hp
    change ¬ ev P a ≠ 0 at hp
    simp only [not_not] at hp
    cases P with
    | zero => exact Or.inl rfl
    | some x y h =>
      apply Or.inr
      apply Set.mem_iUnion₂.mpr
      refine ⟨x, ?_, rfl⟩
      obtain ⟨p, q, he⟩ := CoordinateRing.exists_smul_basis_eq a
      rw [← he, ev_basis x y h p q] at hp
      change (Algebra.norm (Polynomial k) a).eval x = 0
      rw [← he, CoordinateRing.norm_smul_basis]
      simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_mul,
        Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X]
      have heq := (equation_iff x y).mp h.1
      linear_combination (p.eval x - q.eval x * y - q.eval x * (W.a₁ * x + W.a₃)) * hp +
        q.eval x ^ 2 * heq
  -- Rational coordinate functions are defined away from a finite set.
  let Good : (G → k) → Prop := fun f =>
    ∃ a b : A, b ≠ 0 ∧ ∀ᶠ P in Filter.cofinite, f P = ev P a / ev P b
  have good_ev (a : A) : Good (fun P => ev P a) := by
    refine ⟨a, 1, one_ne_zero, ?_⟩
    filter_upwards [] with P
    simp
  have good_congr {f g : G → k} (hf : Good f)
      (hfg : ∀ᶠ P in Filter.cofinite, f P = g P) : Good g := by
    obtain ⟨a, b, hb, hh⟩ := hf
    refine ⟨a, b, hb, ?_⟩
    filter_upwards [hfg, hh] with P hP hi
    exact hP.symm.trans hi
  have good_const (c : k) : Good (fun _ => c) := by
    apply good_congr (good_ev (algebraMap k A c))
    filter_upwards [] with P
    cases P <;>
      simp [ev, A, AdjoinRoot.evalEval, AdjoinRoot.algebraMap_eq', AdjoinRoot.lift_of]
  have good_add {f g : G → k} (hf : Good f) (hg : Good g) :
      Good (fun P => f P + g P) := by
    obtain ⟨a, b, hb, hh⟩ := hf
    obtain ⟨c, d, hd, hi⟩ := hg
    refine ⟨a * d + c * b, b * d, mul_ne_zero hb hd, ?_⟩
    filter_upwards [hh, hi, ev_nonzero b hb, ev_nonzero d hd] with P hP iP hbP hdP
    rw [hP, iP, map_add, map_mul, map_mul, map_mul]
    simpa only [mul_comm] using div_add_div (ev P a) (ev P c) hbP hdP
  have good_neg {f : G → k} (hf : Good f) : Good (fun P => -f P) := by
    obtain ⟨a, b, hb, hh⟩ := hf
    refine ⟨-a, b, hb, ?_⟩
    filter_upwards [hh] with P hP
    simp only [hP, map_neg, neg_div]
  have good_sub {f g : G → k} (hf : Good f) (hg : Good g) :
      Good (fun P => f P - g P) := by
    simpa only [sub_eq_add_neg] using good_add hf (good_neg hg)
  have good_mul {f g : G → k} (hf : Good f) (hg : Good g) :
      Good (fun P => f P * g P) := by
    obtain ⟨a, b, hb, hh⟩ := hf
    obtain ⟨c, d, hd, hi⟩ := hg
    refine ⟨a * c, b * d, mul_ne_zero hb hd, ?_⟩
    filter_upwards [hh, hi] with P hP iP
    simp only [hP, iP, map_mul, div_mul_div_comm]
  have good_inv {f : G → k} (hf : Good f) : Good (fun P => (f P)⁻¹) := by
    obtain ⟨a, b, hb, hh⟩ := hf
    by_cases ha : a = 0
    · apply good_congr (good_const 0)
      filter_upwards [hh] with P hP
      simp [hP, ha]
    · refine ⟨b, a, ha, ?_⟩
      filter_upwards [hh] with P hP
      simp only [hP, inv_div]
  have good_div {f g : G → k} (hf : Good f) (hg : Good g) :
      Good (fun P => f P / g P) := by
    simpa only [div_eq_mul_inv] using good_mul hf (good_inv hg)
  have good_pow {f : G → k} (hf : Good f) (m : ℕ) : Good (fun P => f P ^ m) := by
    induction m with
    | zero => simpa only [pow_zero] using good_const 1
    | succ m ih => simpa only [pow_succ] using good_mul ih hf
  have good_dichotomy {f : G → k} (hf : Good f) :
      (∀ᶠ P in Filter.cofinite, f P = 0) ∨ (∀ᶠ P in Filter.cofinite, f P ≠ 0) := by
    obtain ⟨a, b, hb, hh⟩ := hf
    by_cases ha : a = 0
    · left
      filter_upwards [hh] with P hP
      simp [hP, ha]
    · right
      filter_upwards [hh, ev_nonzero a ha, ev_nonzero b hb] with P hP haP hbP
      exact hP ▸ div_ne_zero haP hbP
  have good_eq {f g : G → k} (hf : Good f) (hg : Good g) :
      (∀ᶠ P in Filter.cofinite, f P = g P) ∨
      (∀ᶠ P in Filter.cofinite, f P ≠ g P) := by
    simpa only [sub_eq_zero, sub_ne_zero] using good_dichotomy (good_sub hf hg)
  have good_ite {f g a b : G → k} (hf : Good f) (hg : Good g)
      (ha : Good a) (hb : Good b) : Good (fun P => if f P = g P then a P else b P) := by
    rcases good_eq hf hg with h | h
    · apply good_congr ha
      filter_upwards [h] with P hP
      simp [hP]
    · apply good_congr hb
      filter_upwards [h] with P hP
      simp [hP]
  -- The point formulas are either zero or affine away from a finite set.
  let GoodPoint : (G → G) → Prop := fun f =>
    (∀ᶠ P in Filter.cofinite, f P = 0) ∨
      ∃ x y : G → k, Good x ∧ Good y ∧
        ∀ᶠ P in Filter.cofinite, ∃ h : W.toAffine.Nonsingular (x P) (y P),
          f P = .some (x P) (y P) h
  have goodPoint_congr {f g : G → G} (hf : GoodPoint f)
      (hh : ∀ᶠ P in Filter.cofinite, f P = g P) : GoodPoint g := by
    rcases hf with hf | ⟨x, y, hx, hy, h⟩
    · left
      filter_upwards [hh, hf] with P hP hi
      exact hP.symm.trans hi
    · right
      refine ⟨x, y, hx, hy, ?_⟩
      filter_upwards [hh, h] with P hP ⟨h, he⟩
      exact ⟨h, hP.symm.trans he⟩
  have goodPoint_id : GoodPoint (fun P => P) := by
    let x : G → k := fun P => ev P (CoordinateRing.mk W.toAffine (Polynomial.C Polynomial.X))
    let y : G → k := fun P => ev P (CoordinateRing.mk W.toAffine Polynomial.X)
    refine Or.inr ⟨x, y, good_ev _, good_ev _, ?_⟩
    filter_upwards [Filter.eventually_cofinite_ne (0 : G)] with P hP
    cases P with
    | zero => exact (hP rfl).elim
    | some u v h =>
      have hx : x (.some u v h) = u := by simp only [x, ev_mk u v h, Polynomial.evalEval_C, Polynomial.eval_X]
      have hy : y (.some u v h) = v := by simp only [y, ev_mk u v h, Polynomial.evalEval_X]
      simp only [hx, hy]
      exact ⟨h, trivial⟩
  have goodPoint_add {f g : G → G} (hf : GoodPoint f) (hg : GoodPoint g) :
      GoodPoint (fun P => f P + g P) := by
    rcases hf with hf | ⟨x₁, y₁, hx₁, hy₁, hf⟩
    · apply goodPoint_congr hg
      filter_upwards [hf] with P hP
      simp [hP]
    rcases hg with hg | ⟨x₂, y₂, hx₂, hy₂, hg⟩
    · apply goodPoint_congr (Or.inr ⟨x₁, y₁, hx₁, hy₁, hf⟩)
      filter_upwards [hg] with P hP
      simp [hP]
    have hneg (x y : G → k) (hx : Good x) (hy : Good y) :
        Good (fun P => W.toAffine.negY (x P) (y P)) := by
      exact good_sub (good_sub (good_neg hy) (good_mul (good_const W.a₁) hx))
        (good_const W.a₃)
    have hcase : (∀ᶠ P in Filter.cofinite,
        x₁ P = x₂ P ∧ y₁ P = W.toAffine.negY (x₂ P) (y₂ P)) ∨
        (∀ᶠ P in Filter.cofinite,
        ¬(x₁ P = x₂ P ∧ y₁ P = W.toAffine.negY (x₂ P) (y₂ P))) := by
      rcases good_eq hx₁ hx₂ with h | h
      · rcases good_eq hy₁ (hneg x₂ y₂ hx₂ hy₂) with h' | h'
        · exact Or.inl (h.and h')
        · right
          filter_upwards [h'] with P hP
          exact fun hh => hP hh.2
      · right
        filter_upwards [h] with P hP
        exact fun hh => hP hh.1
    rcases hcase with hc | hc
    · left
      filter_upwards [hf, hg, hc] with P ⟨h₁, he₁⟩ ⟨h₂, he₂⟩ hP
      rw [he₁, he₂,  add_of_Y_eq hP.1 hP.2]
    · let s : G → k := fun P => W.toAffine.slope (x₁ P) (x₂ P) (y₁ P) (y₂ P)
      have hs : Good s := by
        apply good_ite hx₁ hx₂
        · apply good_ite hy₁ (hneg x₂ y₂ hx₂ hy₂) (good_const 0)
          exact good_div
            (good_sub (good_add
              (good_add (good_mul (good_const 3) (good_pow hx₁ 2))
                (good_mul (good_const (2 * W.a₂)) hx₁)) (good_const W.a₄))
              (good_mul (good_const W.a₁) hy₁))
            (good_sub hy₁ (hneg x₁ y₁ hx₁ hy₁))
        · exact good_div (good_sub hy₁ hy₂) (good_sub hx₁ hx₂)
      let x : G → k := fun P => W.toAffine.addX (x₁ P) (x₂ P) (s P)
      let y : G → k := fun P => W.toAffine.addY (x₁ P) (x₂ P) (y₁ P) (s P)
      have hx : Good x :=
        good_sub (good_sub (good_sub (good_add (good_pow hs 2)
          (good_mul (good_const W.a₁) hs)) (good_const W.a₂)) hx₁) hx₂
      have hy : Good y :=
        hneg x (fun P => s P * (x P - x₁ P) + y₁ P) hx
          (good_add (good_mul hs (good_sub hx hx₁)) hy₁)
      refine Or.inr ⟨x, y, hx, hy, ?_⟩
      filter_upwards [hf, hg, hc] with P ⟨h₁, he₁⟩ ⟨h₂, he₂⟩ hP
      exact ⟨nonsingular_add h₁ h₂ hP, by rw [he₁, he₂, add_some hP]⟩
  have goodPoint_nsmul (m : ℕ) : GoodPoint (fun P => m • P) := by
    induction m with
    | zero => exact Or.inl (Filter.Eventually.of_forall (fun P => zero_nsmul P))
    | succ m ih =>
      simpa only [succ_nsmul] using goodPoint_add ih goodPoint_id
  -- A subgroup with finite complement in an infinite group is the whole group.
  -- Translation by the witness excludes that possibility for this kernel.
  rcases goodPoint_nsmul n with hz | ⟨x,y,hx,hy,hh⟩
  · cases finite_or_infinite G with
    | inl h => exact inferInstance
    | inr h =>
      have ht : Filter.Tendsto (fun P : G => P + .some x₀ y₀ h₀)
          Filter.cofinite Filter.cofinite :=
        (show Function.Injective (fun P : G => P + .some x₀ y₀ h₀) from
          fun _ _ hh => add_right_cancel hh).tendsto_cofinite
      obtain ⟨P, hP, hPQ⟩ := (hz.and (ht.eventually hz)).exists
      apply False.elim
      apply hQ
      simpa only [nsmul_add, hP, zero_add] using hPQ
  · have hne : ∀ᶠ P : G in Filter.cofinite, n • P ≠ 0 := by
      filter_upwards [hh] with P ⟨h, he⟩
      rw [he]
      exact some_ne_zero h
    exact (show Set.Finite {P : G | n • P = 0} from
      by simpa only [Filter.eventually_cofinite, not_not] using hne).to_subtype


theorem Submission.p03_tkc_positive_torsion_finite_68cf3476_d5 :
    ∀ (k : Type) [Field k] [CharZero k] [IsAlgClosed k] [DecidableEq k]
      (W : WeierstrassCurve k), W.Δ ≠ 0 → ∀ n : ℕ, 0 < n →
        Finite {P : W.toAffine.Point // n • P = 0} := by
  intro k _ _ _ _ W hΔ n hn
  exact Submission.p03_ptf_finite_kernel_of_nsmul_nonzero_c5b7b5ed_d6 k W hΔ n
    (Submission.p03_ptf_positive_nsmul_nonzero_c5b7b5ed_d6 k W hΔ n hn)

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
        simpa only [mul_nsmul, hQ, nsmul_neg, neg_ne_zero] using hP
    · refine ⟨T, ?_⟩
      simpa only [add_nsmul, mul_nsmul, hT2, nsmul_zero, one_nsmul,
        zero_add] using hT
