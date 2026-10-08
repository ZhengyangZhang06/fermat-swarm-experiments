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
