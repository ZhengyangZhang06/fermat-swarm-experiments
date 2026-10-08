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

namespace Submission

theorem p03_odd_prepsi_torsion_68cf3476 :
    ∀ (F : Type) [Field F] [CharZero F] [DecidableEq F] (W : WeierstrassCurve F),
      W.Δ ≠ 0 → ∀ (n : ℕ), 3 ≤ n → Odd n →
      ∀ (x y : F) (h : W.toAffine.Nonsingular x y),
        n • WeierstrassCurve.Affine.Point.some x y h = 0 ↔ (W.preΨ' n).eval x = 0 := by
  intro F _ _ _ W hΔ n hn hnodd x y h
  classical
  let ι : F →+* AlgebraicClosure F := algebraMap F (AlgebraicClosure F)
  let V : WeierstrassCurve (AlgebraicClosure F) := W.map ι
  have hV : V.Δ ≠ 0 := by
    simpa only [V, WeierstrassCurve.map_Δ] using
      (map_ne_zero_iff ι ι.injective).2 hΔ
  have hQ : V.toAffine.Nonsingular (ι x) (ι y) :=
    (W.toAffine.map_nonsingular ι.injective x y).2 h
  -- The two child interfaces give the odd division polynomial in the point ideal.
  obtain ⟨f, hf, htorsion⟩ :=
    Submission.p03_torsion_eds_exists_68cf3476_d2 (AlgebraicClosure F) V hV
  have hidentify :=
    Submission.p03_torsion_eds_identification_68cf3476_d2
      (AlgebraicClosure F) V f hf n
  rw [if_neg (Nat.not_even_iff_odd.mpr hnodd), mul_one] at hidentify
  have hideal :
      WeierstrassCurve.Affine.CoordinateRing.mk V.toAffine
          (Polynomial.C (V.preΨ' n)) ∈
        WeierstrassCurve.Affine.CoordinateRing.XYIdeal V.toAffine (ι x)
          (Polynomial.C (ι y)) ↔ (V.preΨ' n).eval (ι x) = 0 := by
    let e : V.toAffine.CoordinateRing →+* AlgebraicClosure F :=
      AdjoinRoot.evalEval hQ.1
    have hker :
        WeierstrassCurve.Affine.CoordinateRing.XYIdeal V.toAffine (ι x)
          (Polynomial.C (ι y)) ≤ RingHom.ker e := by
      rw [WeierstrassCurve.Affine.CoordinateRing.XYIdeal, Ideal.span_le]
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · change AdjoinRoot.evalEval hQ.1
          (AdjoinRoot.mk V.toAffine.polynomial
            (Polynomial.C (Polynomial.X - Polynomial.C (ι x)))) = 0
        rw [AdjoinRoot.evalEval_mk]
        simp [Polynomial.evalEval]
      · change AdjoinRoot.evalEval hQ.1
          (AdjoinRoot.mk V.toAffine.polynomial
            (Polynomial.X - Polynomial.C (Polynomial.C (ι y)))) = 0
        rw [AdjoinRoot.evalEval_mk]
        simp [Polynomial.evalEval]
    constructor
    · intro hm
      have he := hker hm
      change e (WeierstrassCurve.Affine.CoordinateRing.mk V.toAffine
        (Polynomial.C (V.preΨ' n))) = 0 at he
      simpa only [e, WeierstrassCurve.Affine.CoordinateRing.mk,
        AdjoinRoot.evalEval_mk, Polynomial.evalEval_C] using he
    · intro he
      obtain ⟨g, hg⟩ := (Polynomial.dvd_iff_isRoot.mpr he :
        Polynomial.X - Polynomial.C (ι x) ∣ V.preΨ' n)
      rw [hg, Polynomial.C_mul, map_mul]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_insert _ _))
  have hclosure :
      n • WeierstrassCurve.Affine.Point.some (ι x) (ι y) hQ = 0 ↔
        (V.preΨ' n).eval (ι x) = 0 := by
    rw [← htorsion n (by omega) (ι x) (ι y) hQ, hidentify]
    exact hideal
  -- Both torsion and polynomial vanishing descend through the field inclusion.
  let φ : W.toAffine.Point →+ V.toAffine.Point :=
    WeierstrassCurve.Affine.Point.map (W' := W.toAffine)
      (Algebra.ofId F (AlgebraicClosure F))
  have hφ : Function.Injective φ :=
    WeierstrassCurve.Affine.Point.map_injective
      (W' := W.toAffine) (Algebra.ofId F (AlgebraicClosure F))
  have hdescent : n • WeierstrassCurve.Affine.Point.some x y h = 0 ↔
      n • WeierstrassCurve.Affine.Point.some (ι x) (ι y) hQ = 0 := by
    change n • WeierstrassCurve.Affine.Point.some x y h = 0 ↔
      n • φ (WeierstrassCurve.Affine.Point.some x y h) = 0
    rw [← map_nsmul φ, ← map_zero φ]
    exact hφ.eq_iff.symm
  refine hdescent.trans (hclosure.trans ?_)
  dsimp only [V]
  rw [WeierstrassCurve.map_preΨ', Polynomial.eval_map_apply]
  exact map_eq_zero_iff ι ι.injective

end Submission

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
