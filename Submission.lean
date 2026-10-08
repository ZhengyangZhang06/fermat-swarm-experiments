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
