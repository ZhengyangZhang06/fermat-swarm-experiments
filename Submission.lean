/-
Copyright 2026 Anthropic, PBC. Licensed under Apache-2.0; see LICENSE.
Source: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_AlgebraicCurve_hasPrincipalDivisors_of_transcendental.lean
Modified: replaced the proof with sorry and removed P2M proof imports.
Requires the upstream Definitions modules and their dependencies.
-/

import Definitions.Def_AlgebraicCurve_PlacesOverDVR
attribute [-instance] AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy
attribute [-simp] AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul
attribute [-simp] AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Quotient.Basic

open AlgebraicCurve
theorem AlgebraicCurve.hasPrincipalDivisors_of_transcendental (K : Type*) [Field K] [CharZero K] {F : Type*} [Field F]
    [Algebra K F] (x : F) (hx : Transcendental K x)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F] : HasPrincipalDivisors K F := by
  sorry

namespace Submission

/-- The uniformizer exponent of a nonzero scalar is both its quotient length and its place order. -/
theorem p06_9e0f5043ff_dlen_scalar_quotient
    (K E : Type*) [Field K] [Field E] [Algebra K E]
    (v : AlgebraicCurve.Place K E) (a : v.toValuationSubring) (ha : a ≠ 0) :
    ∃ n : ℕ,
      Module.length v.toValuationSubring
        (v.toValuationSubring ⧸ Ideal.span ({a} : Set v.toValuationSubring)) = (n : ℕ∞) ∧
      v.ord (algebraMap v.toValuationSubring E a) = (n : ℤ) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ
  refine ⟨n, ?_, ?_⟩
  · rw [Ideal.span_singleton_mul_left_unit u.isUnit, ← Ideal.span_singleton_pow,
      ← hπ.maximalIdeal_eq]
    exact IsDiscreteValuationRing.length_quotient_pow_maximalIdeal v.toValuationSubring n
  · change v.ord (((u : v.toValuationSubring) : E) * (π : E) ^ n) = (n : ℤ)
    simpa only [zpow_natCast] using v.ord_unit_smul_zpow u hπ (n : ℤ)
/-- A finite family in a DVR with a nonzero entry has a nonzero member dividing every entry.
Choose a member of minimum uniformizer exponent among the nonzero entries. Unit factors
do not affect divisibility, and the minimum power divides every other power. -/
theorem p06_9e0f5043ff_dmd_finite_family_dividing_member
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (ι : Type*) [Fintype ι] (a : ι → A) (ha : ∃ i, a i ≠ 0) :
    ∃ i, a i ≠ 0 ∧ ∀ j, a i ∣ a j := by
  classical
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  let S := {i : ι // a i ≠ 0}
  have hfactor : ∀ i : S, ∃ (n : ℕ) (u : Aˣ), a i = u * π ^ n :=
    fun i => IsDiscreteValuationRing.eq_unit_mul_pow_irreducible i.property hπ
  choose e u he using hfactor
  have hS : (Finset.univ : Finset S).Nonempty := by
    obtain ⟨i, hi⟩ := ha
    exact ⟨⟨i, hi⟩, Finset.mem_univ _⟩
  -- Minimize the uniformizer exponent among the nonzero entries.
  obtain ⟨i, _, hmin⟩ := Finset.exists_min_image Finset.univ e hS
  refine ⟨i.val, i.property, ?_⟩
  intro j
  by_cases hj : a j = 0
  · rw [hj]
    exact dvd_zero _
  · rw [he i, he ⟨j, hj⟩, Units.mul_left_dvd, Units.dvd_mul_left]
    exact pow_dvd_pow π (hmin ⟨j, hj⟩ (Finset.mem_univ _))
/-- Clear the first column below a divisible pivot by a unit that preserves the first row. -/
theorem p06_9e0f5043ff_sdp_clear_first_column
    (R : Type*) [CommRing R] (m : ℕ)
    (B : Matrix (Fin (m + 1)) (Fin (m + 1)) R)
    (h : ∀ i : Fin m, B 0 0 ∣ B i.succ 0) :
    ∃ U : Matrix (Fin (m + 1)) (Fin (m + 1)) R,
      IsUnit U ∧ (∀ j : Fin (m + 1), (U * B) 0 j = B 0 j) ∧
        (∀ i : Fin m, (U * B) i.succ 0 = 0) := by
  classical
  choose a ha using h
  -- Extend the chosen coefficients by zero so the first row is unchanged.
  let c : Fin (m + 1) → R := Fin.cases 0 a
  let N : Matrix (Fin (m + 1)) (Fin (m + 1)) R :=
    Matrix.of fun i j => if j = 0 then c i else 0
  have hmul (M : Matrix (Fin (m + 1)) (Fin (m + 1)) R)
      (i j : Fin (m + 1)) : (N * M) i j = c i * M 0 j := by
    simp [Matrix.mul_apply, N]
  have hsq : N * N = 0 := by
    ext i j
    simp [hmul, N, c]
  -- Since N² = 0, the clearing matrix 1 - N has two-sided inverse 1 + N.
  refine ⟨1 - N, ?_, ?_, ?_⟩
  · refine ⟨⟨1 - N, 1 + N, ?_, ?_⟩, rfl⟩
    · simp [sub_mul, mul_add, hsq]
    · simp [mul_sub, add_mul, hsq]
  · intro j
    simp [sub_mul, hmul, c]
  · intro i
    simp [sub_mul, hmul, c, ha i, mul_comm]
/-- Clear the first row by an invertible column operation, preserving the trailing block.
The correction matrix squares to zero, so `1 - M` has the explicit inverse `1 + M`.
Divisibility supplies the coefficients without requiring the pivot to be nonzero or a unit. -/
theorem p06_9e0f5043ff_sdp_clear_first_row :
    ∀ (R : Type*) [CommRing R] (m : ℕ)
      (H : Matrix (Fin (m + 1)) (Fin (m + 1)) R),
      (∀ i : Fin m, H i.succ 0 = 0) →
      (∀ j : Fin m, H 0 0 ∣ H 0 j.succ) →
      ∃ V : Matrix (Fin (m + 1)) (Fin (m + 1)) R,
        IsUnit V ∧ H * V = Matrix.of (fun i j =>
          Fin.cases (Fin.cases (H 0 0) (fun _ => 0) j)
            (fun i' => Fin.cases 0 (fun j' => H i'.succ j'.succ) j) i) := by
  classical
  intro R _ m H hcol hdiv
  choose b hb using hdiv
  let M : Matrix (Fin (m + 1)) (Fin (m + 1)) R :=
    Matrix.of (fun i j => Fin.cases (Fin.cases 0 b j) (fun _ => 0) i)
  have hM0 (i : Fin (m + 1)) : M i 0 = 0 := by
    refine Fin.cases ?_ (fun _ => ?_) i <;> rfl
  have hMs (i : Fin m) (j : Fin (m + 1)) : M i.succ j = 0 := rfl
  have hMM : M * M = 0 := by
    ext i j
    simp [Matrix.mul_apply, Fin.sum_univ_succ, hM0, hMs]
  have hHM (i j : Fin (m + 1)) :
      (H * M) i j = H i 0 * Fin.cases 0 b j := by
    simp [Matrix.mul_apply, Fin.sum_univ_succ, M]
  refine ⟨1 - M, ?_, ?_⟩
  · refine ⟨⟨1 - M, 1 + M, ?_, ?_⟩, rfl⟩
    · simp [sub_mul, mul_add, hMM]
    · simp [mul_sub, add_mul, hMM]
  · rw [mul_sub, mul_one]
    ext i j
    refine Fin.cases ?_ (fun i' => ?_) i <;>
      refine Fin.cases ?_ (fun j' => ?_) j <;>
      simp [Matrix.sub_apply, hHM, hcol, hb]

end Submission


namespace Submission

/-- Split off an entry dividing every matrix entry using invertible row and column operations.
Swap the pivot into position `(0, 0)`, then apply the approved column and row clearing lemmas.
The pivot need not be nonzero, and the trailing block may have size zero. -/
theorem p06_9e0f5043ff_dmd_split_divisible_pivot
    (R : Type*) [CommRing R] (m : ℕ)
    (D : Matrix (Fin (m + 1)) (Fin (m + 1)) R) (r c : Fin (m + 1))
    (hdiv : ∀ i j, D r c ∣ D i j) :
    ∃ (P Q : Matrix (Fin (m + 1)) (Fin (m + 1)) R)
      (C : Matrix (Fin m) (Fin m) R),
      IsUnit P ∧ IsUnit Q ∧
        P * D * Q = Matrix.of (fun i j =>
          Fin.cases (Fin.cases (D r c) (fun _ => 0) j)
            (fun i' => Fin.cases 0 (fun j' => C i' j') j) i) := by
  classical
  -- Move the chosen pivot to the upper-left corner using two involutions.
  let σ := Equiv.swap (0 : Fin (m + 1)) r
  let τ := Equiv.swap (0 : Fin (m + 1)) c
  let S : Matrix (Fin (m + 1)) (Fin (m + 1)) R :=
    (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) R).submatrix σ (Equiv.refl _)
  let T : Matrix (Fin (m + 1)) (Fin (m + 1)) R :=
    (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) R).submatrix (Equiv.refl _) τ
  have hSS : S * S = 1 := by
    dsimp only [S]
    rw [Matrix.one_submatrix_mul]
    ext i j
    exact congrArg (fun k => (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) R) k j)
      (Equiv.swap_apply_self 0 r i)
  have hTT : T * T = 1 := by
    dsimp only [T]
    rw [Matrix.mul_submatrix_one]
    ext i j
    exact congrArg (fun k => (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) R) i k)
      (Equiv.swap_apply_self 0 c j)
  have hS : IsUnit S := ⟨⟨S, S, hSS, hSS⟩, rfl⟩
  have hT : IsUnit T := ⟨⟨T, T, hTT, hTT⟩, rfl⟩
  let B := S * D * T
  have hB : B = D.submatrix σ τ := by
    dsimp only [B, S, T]
    rw [Matrix.one_submatrix_mul, Matrix.mul_submatrix_one]
    rfl
  have hB00 : B 0 0 = D r c := by
    simp [hB, Matrix.submatrix, σ, τ]
  have hdivB : ∀ i j, B 0 0 ∣ B i j := by
    intro i j
    rw [hB00, hB]
    exact hdiv _ _
  -- The first operation preserves row zero, so its divisibility also survives.
  obtain ⟨U, hU, hrow, hcol⟩ :=
    p06_9e0f5043ff_sdp_clear_first_column R m B (fun i => hdivB i.succ 0)
  obtain ⟨V, hV, hblock⟩ :=
    p06_9e0f5043ff_sdp_clear_first_row R m (U * B) hcol (by
      intro j
      rw [hrow 0, hrow j.succ]
      exact hdivB 0 j.succ)
  refine ⟨U * S, T * V, Matrix.of (fun i j => (U * B) i.succ j.succ),
    hU.mul hS, hT.mul hV, ?_⟩
  calc
    (U * S) * D * (T * V) = (U * B) * V := by
      simp only [B, mul_assoc]
    _ = _ := by
      simpa only [hrow 0, hB00, Matrix.of_apply] using hblock

end Submission


namespace Submission

/-- Diagonalization over a DVR, with no divisibility ordering on the diagonal. -/
theorem p06_9e0f5043ff_dlen_matrix_diagonalization
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (m : ℕ) (D : Matrix (Fin m) (Fin m) A) (hD : D.det ≠ 0) :
    ∃ (P Q : Matrix (Fin m) (Fin m) A) (d : Fin m → A),
      IsUnit P ∧ IsUnit Q ∧ (∀ i, d i ≠ 0) ∧ P * D * Q = Matrix.diagonal d := by
  classical
  induction m with
  | zero =>
      refine ⟨1, 1, Fin.elim0, isUnit_one, isUnit_one, ?_, ?_⟩
      · intro i
        exact Fin.elim0 i
      · ext i
        exact Fin.elim0 i
  | succ m ih =>
      -- The children select a dividing pivot and isolate its one-by-one block.
      have hentry : ∃ ij : Fin (m + 1) × Fin (m + 1), D ij.1 ij.2 ≠ 0 := by
        by_contra! h
        have hz : D = 0 := by
          ext i j
          exact h (i, j)
        exact hD (by simp [hz])
      obtain ⟨⟨r, c⟩, hp, hdiv⟩ :=
        p06_9e0f5043ff_dmd_finite_family_dividing_member A
          (Fin (m + 1) × Fin (m + 1)) (fun ij => D ij.1 ij.2) hentry
      obtain ⟨P₀, Q₀, C, hP₀, hQ₀, hsplit⟩ :=
        p06_9e0f5043ff_dmd_split_divisible_pivot A m D r c
          (fun i j => hdiv (i, j))
      let block (a : A) (B : Matrix (Fin m) (Fin m) A) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) A :=
        Matrix.of (fun i j =>
          Fin.cases (Fin.cases a (fun _ => 0) j)
            (fun i' => Fin.cases 0 (fun j' => B i' j') j) i)
      have hdet (a : A) (B : Matrix (Fin m) (Fin m) A) :
          (block a B).det = a * B.det := by
        rw [Matrix.det_succ_row_zero]
        simp [block, Fin.sum_univ_succ, Matrix.submatrix,
          show Matrix.of (fun i j => B i j) = B from rfl]
      have hmul (a b : A) (B E : Matrix (Fin m) (Fin m) A) :
          block a B * block b E = block (a * b) (B * E) := by
        ext i j
        refine Fin.cases ?_ (fun i => ?_) i <;>
          refine Fin.cases ?_ (fun j => ?_) j <;>
          simp [block, Matrix.mul_apply, Fin.sum_univ_succ]
      have hdiag (a : A) (d : Fin m → A) :
          block a (Matrix.diagonal d) = Matrix.diagonal (Fin.cases a d) := by
        ext i j
        refine Fin.cases ?_ (fun i => ?_) i <;>
          refine Fin.cases ?_ (fun j => ?_) j <;>
          simp [block, Matrix.diagonal, eq_comm]
      change P₀ * D * Q₀ = block (D r c) C at hsplit
      -- Nonvanishing of the determinant passes to the remaining block.
      have hsplit_det : (block (D r c) C).det ≠ 0 := by
        rw [← hsplit, Matrix.det_mul, Matrix.det_mul]
        exact mul_ne_zero
          (mul_ne_zero ((Matrix.isUnit_iff_isUnit_det P₀).mp hP₀).ne_zero hD)
          ((Matrix.isUnit_iff_isUnit_det Q₀).mp hQ₀).ne_zero
      have hC : C.det ≠ 0 := by
        intro hz
        apply hsplit_det
        rw [hdet, hz, mul_zero]
      obtain ⟨P', Q', d', hP', hQ', hd', heq⟩ := ih C hC
      have hunit (B : Matrix (Fin m) (Fin m) A) (hB : IsUnit B) :
          IsUnit (block 1 B) := by
        apply (Matrix.isUnit_iff_isUnit_det _).mpr
        rw [hdet, one_mul]
        exact (Matrix.isUnit_iff_isUnit_det B).mp hB
      refine ⟨block 1 P' * P₀, Q₀ * block 1 Q', Fin.cases (D r c) d',
        (hunit P' hP').mul hP₀, hQ₀.mul (hunit Q' hQ'), ?_, ?_⟩
      · intro i
        exact Fin.cases hp (fun j => hd' j) i
      · calc
          block 1 P' * P₀ * D * (Q₀ * block 1 Q') =
              block 1 P' * (P₀ * D * Q₀) * block 1 Q' := by
                simp only [mul_assoc]
          _ = block 1 P' * block (D r c) C * block 1 Q' := by rw [hsplit]
          _ = block (D r c) (P' * C * Q') := by rw [hmul, hmul, one_mul, mul_one]
          _ = Matrix.diagonal (Fin.cases (D r c) d') := by rw [heq, hdiag]

end Submission

namespace Submission

/-- Left and right multiplication by unit matrices preserve the cokernel up to linear equivalence. -/
theorem p06_9e0f5043ff_dmc_cokernel_units :
    ∀ (R : Type*) [CommRing R] (m : ℕ) (D P Q : Matrix (Fin m) (Fin m) R),
      IsUnit P → IsUnit Q →
        Nonempty (((Fin m → R) ⧸ LinearMap.range (Matrix.mulVecLin D)) ≃ₗ[R]
          ((Fin m → R) ⧸ LinearMap.range (Matrix.mulVecLin (P * D * Q)))) := by
  intro R _ m D P Q hP hQ
  let eP := Matrix.toLinearEquiv' P hP.invertible
  let eQ := Matrix.toLinearEquiv' Q hQ.invertible
  -- Descend P and its inverse once P maps range(D) onto range(P * D * Q).
  refine ⟨Submodule.Quotient.equiv _ _ eP ?_⟩
  -- P(range D) = range (P * D), and surjectivity of Q gives range (P * D * Q).
  change (LinearMap.range D.mulVecLin).map P.mulVecLin =
    LinearMap.range (P * D * Q).mulVecLin
  rw [← LinearMap.range_comp, ← Matrix.mulVecLin_mul, Matrix.mulVecLin_mul (P * D) Q]
  exact (eQ.range_comp _).symm
/-- The cokernel of a diagonal matrix is the product of its coordinate principal quotients. -/
theorem p06_9e0f5043ff_dmc_diagonal_quotient
    (R : Type*) [CommRing R] (m : ℕ) (d : Fin m → R) :
    Nonempty (((Fin m → R) ⧸ LinearMap.range (Matrix.mulVecLin (Matrix.diagonal d)))
      ≃ₗ[R] ((i : Fin m) → R ⧸ Ideal.span ({d i} : Set R))) := by
  classical
  -- Reduce each coordinate modulo the corresponding principal ideal.
  let C : (Fin m → R) →ₗ[R] ((i : Fin m) → R ⧸ Ideal.span ({d i} : Set R)) :=
    LinearMap.pi fun i => (Ideal.span ({d i} : Set R)).mkQ.comp (LinearMap.proj i)
  have hker : LinearMap.ker C = LinearMap.range (Matrix.mulVecLin (Matrix.diagonal d)) := by
    ext y
    simp only [LinearMap.mem_ker, LinearMap.mem_range]
    constructor
    · intro hy
      have hyi : ∀ i, d i ∣ y i := by
        intro i
        apply Ideal.mem_span_singleton.mp
        apply (Submodule.Quotient.mk_eq_zero _).mp
        exact congrFun hy i
      choose z hz using hyi
      exact ⟨z, funext fun i => (Matrix.mulVec_diagonal d z i).trans (hz i).symm⟩
    · rintro ⟨z, rfl⟩
      funext i
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      exact Ideal.mem_span_singleton.mpr ⟨z i, Matrix.mulVec_diagonal d z i⟩
  have hsurj : Function.Surjective C := by
    intro w
    choose y hy using fun i => (Ideal.span ({d i} : Set R)).mkQ_surjective (w i)
    exact ⟨y, funext hy⟩
  -- The first isomorphism theorem supplies the induced bijection and its linear inverse.
  exact ⟨(Submodule.quotEquivOfEq _ _ hker.symm).trans (C.quotKerEquivOfSurjective hsurj)⟩

end Submission


namespace Submission

theorem p06_9e0f5043ff_dlen_diagonal_cokernel
    (R : Type*) [CommRing R] (m : ℕ) (D P Q : Matrix (Fin m) (Fin m) R)
    (d : Fin m → R) (hP : IsUnit P) (hQ : IsUnit Q)
    (hdiag : P * D * Q = Matrix.diagonal d) :
    Nonempty (((Fin m → R) ⧸ LinearMap.range (Matrix.mulVecLin D)) ≃ₗ[R]
      ((i : Fin m) → R ⧸ Ideal.span ({d i} : Set R))) := by
  obtain ⟨eUnits⟩ := Submission.p06_9e0f5043ff_dmc_cokernel_units R m D P Q hP hQ
  rw [hdiag] at eUnits
  obtain ⟨eDiagonal⟩ := Submission.p06_9e0f5043ff_dmc_diagonal_quotient R m d
  exact ⟨eUnits.trans eDiagonal⟩

/-- Over a place DVR, the cokernel length equals the order of the determinant. -/
theorem p06_9e0f5043ff_lno_dvr_determinant_length
    (K E : Type*) [Field K] [Field E] [Algebra K E]
    (v : AlgebraicCurve.Place K E) (M : Type*) [AddCommGroup M]
    [Module v.toValuationSubring M] [Module.Free v.toValuationSubring M]
    [Module.Finite v.toValuationSubring M] (T : M →ₗ[v.toValuationSubring] M)
    (hT : LinearMap.det T ≠ 0) :
    ∃ n : ℕ, Module.length v.toValuationSubring (M ⧸ LinearMap.range T) = (n : ℕ∞) ∧
      v.ord (algebraMap v.toValuationSubring E (LinearMap.det T)) = (n : ℤ) := by
  classical
  let A := v.toValuationSubring
  let m := Module.finrank A M
  let b := Module.finBasis A M
  let D := LinearMap.toMatrix b b T
  have hD : D.det ≠ 0 := by simpa [D] using hT
  obtain ⟨P, Q, d, hP, hQ, hd, hdiag⟩ :=
    p06_9e0f5043ff_dlen_matrix_diagonalization A m D hD
  obtain ⟨c⟩ := p06_9e0f5043ff_dlen_diagonal_cokernel A m D P Q d hP hQ hdiag
  choose a hlength hord using fun i => p06_9e0f5043ff_dlen_scalar_quotient K E v (d i) (hd i)
  have hcoord (x : M) : Matrix.mulVecLin D (b.equivFun x) = b.equivFun (T x) := by
    exact LinearMap.toMatrix_mulVec_repr b b T x
  have hrange : (LinearMap.range T).map b.equivFun.toLinearMap =
      LinearMap.range (Matrix.mulVecLin D) := by
    ext y
    constructor
    · rintro ⟨z, ⟨x, rfl⟩, rfl⟩
      exact ⟨b.equivFun x, hcoord x⟩
    · rintro ⟨x, rfl⟩
      refine ⟨T (b.equivFun.symm x), ⟨b.equivFun.symm x, rfl⟩, ?_⟩
      change b.equivFun (T (b.equivFun.symm x)) = Matrix.mulVecLin D x
      rw [← hcoord, LinearEquiv.apply_symm_apply]
  let e := Submodule.Quotient.equiv (LinearMap.range T)
    (LinearMap.range (Matrix.mulVecLin D)) b.equivFun hrange
  refine ⟨∑ i, a i, ?_, ?_⟩
  · rw [(e.trans c).length_eq, Module.length_pi_of_fintype]
    rw [Nat.cast_sum]
    exact Finset.sum_congr rfl (fun i _ => hlength i)
  · have hcoe (x : A) (hx : x ≠ 0) : algebraMap A E x ≠ 0 := by
      exact fun h => hx (Subtype.ext h)
    have hunit (x : A) (hx : IsUnit x) : v.ord (algebraMap A E x) = 0 := by
      obtain ⟨u, rfl⟩ := hx
      exact v.ord_coe_unit u
    have hPdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
    have hQdet : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).mp hQ
    have hdet : P.det * D.det * Q.det = ∏ i, d i := by
      simpa only [Matrix.det_mul, Matrix.det_diagonal] using congrArg Matrix.det hdiag
    have hprod : ∀ s : Finset (Fin m),
        v.ord (algebraMap A E (∏ i ∈ s, d i)) = ∑ i ∈ s, (a i : ℤ) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | @insert i s hi ih =>
        rw [Finset.prod_insert hi, map_mul,
          v.ord_mul (hcoe _ (hd i))
            (hcoe _ (Finset.prod_ne_zero_iff.mpr (fun j _ => hd j))),
          hord i, ih, Finset.sum_insert hi]
    have horder := congrArg (fun x : A => v.ord (algebraMap A E x)) hdet
    rw [map_mul, map_mul,
      v.ord_mul (mul_ne_zero (hcoe _ hPdet.ne_zero) (hcoe _ hD))
        (hcoe _ hQdet.ne_zero),
      v.ord_mul (hcoe _ hPdet.ne_zero) (hcoe _ hD),
      hunit _ hPdet, hunit _ hQdet, zero_add, add_zero, hprod] at horder
    simpa only [D, LinearMap.det_toMatrix, Nat.cast_sum] using horder

end Submission


namespace Submission

theorem p06_9e0f5043ff_lno_integral_norm_length
    (K E L : Type*) [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra K L] [Algebra E L] [IsScalarTower K E L]
    [FiniteDimensional E L] [Algebra.IsSeparable E L]
    (v : AlgebraicCurve.Place K E) (b : AlgebraicCurve.Place.integralClosureAt L v)
    (hb : b ≠ 0) :
    ∃ n : ℕ,
      Module.length v.toValuationSubring
        (AlgebraicCurve.Place.integralClosureAt L v ⧸
          Ideal.span ({b} : Set (AlgebraicCurve.Place.integralClosureAt L v))) = (n : ℕ∞) ∧
      v.ord (Algebra.norm E
        (algebraMap (AlgebraicCurve.Place.integralClosureAt L v) L b)) = (n : ℤ) := by
  classical
  let A := v.toValuationSubring
  let B := AlgebraicCurve.Place.integralClosureAt L v
  have : Module.Free A B := inferInstance
  have : IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors A)) L :=
    IsIntegralClosure.isLocalization A E L B
  -- Extending an integral basis to the fraction field identifies the two norms.
  have hnorm : Algebra.norm E (algebraMap B L b) =
      algebraMap A E (LinearMap.det (LinearMap.mul A B b)) := by
    let e := Module.finBasis A B
    have hmatrix : (algebraMap A E).mapMatrix (Algebra.leftMulMatrix e b) =
        Algebra.leftMulMatrix (e.localizationLocalization E (nonZeroDivisors A) L)
          (algebraMap B L b) := by
      ext i j
      simp only [Matrix.map_apply, RingHom.mapMatrix_apply,
        Algebra.leftMulMatrix_eq_repr_mul, ← map_mul,
        Module.Basis.localizationLocalization_apply,
        Module.Basis.localizationLocalization_repr_algebraMap]
    change Algebra.norm E (algebraMap B L b) = algebraMap A E (Algebra.norm A b)
    rw [Algebra.norm_eq_matrix_det (e.localizationLocalization E (nonZeroDivisors A) L),
      Algebra.norm_eq_matrix_det e, RingHom.map_det, hmatrix]
  have hbL : algebraMap B L b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective B L)).mpr hb
  have hdet : LinearMap.det (LinearMap.mul A B b) ≠ 0 := by
    intro hzero
    have hnorm0 : Algebra.norm E (algebraMap B L b) = 0 := by
      rw [hnorm, hzero, map_zero]
    exact hbL (Algebra.norm_eq_zero_iff.mp hnorm0)
  obtain ⟨n, hlength, hord⟩ :=
    Submission.p06_9e0f5043ff_lno_dvr_determinant_length K E v B
      (LinearMap.mul A B b) hdet
  refine ⟨n, ?_, ?_⟩
  · rw [Ideal.range_mul] at hlength
    exact (Submodule.Quotient.restrictScalarsEquiv A (Ideal.span {b})).length_eq.symm.trans
      hlength
  · rw [hnorm]
    exact hord

end Submission

namespace Submission

/-- Compute the length over `A` by summing the residue factors of a composition series over `B`.
The sum is in `ℕ∞`, so the factors need not have finite length over `A`.
Apply `Module.length_eq_add_of_exact` after restricting scalars, then induct on the
number of factors using `Fin.sum_univ_castSucc`, including the empty series. -/
theorem p06_9e0f5043ff_wll_length_sum_factors
    (A B M : Type*) [CommRing A] [CommRing B] [IsDedekindDomain B] [Algebra A B]
    [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
    (s : CompositionSeries (Submodule B M))
    (p : Fin s.length → IsDedekindDomain.HeightOneSpectrum B)
    (hhead : s.head = ⊥) (hlast : s.last = ⊤)
    (hfactors : ∀ i : Fin s.length,
      Nonempty ((↥(s i.succ) ⧸ (s i.castSucc).comap (s i.succ).subtype) ≃ₗ[B]
        (B ⧸ (p i).asIdeal))) :
    Module.length A M =
      Finset.sum Finset.univ (fun i : Fin s.length => Module.length A (B ⧸ (p i).asIdeal)) := by
  -- Restrict each short exact sequence and its factor equivalence to A.
  have hstep (i : Fin s.length) :
      Module.length A (s i.succ) =
        Module.length A (s i.castSucc) + Module.length A (B ⧸ (p i).asIdeal) := by
    obtain ⟨e⟩ := hfactors i
    let N := (s i.castSucc).comap (s i.succ).subtype
    have h := Module.length_eq_add_of_exact
      (N.subtype.restrictScalars A) (N.mkQ.restrictScalars A)
      N.subtype_injective N.mkQ_surjective (LinearMap.exact_subtype_mkQ N)
    rw [(Submodule.comapSubtypeEquivOfLe (s.lt_succ i).le).restrictScalars A |>.length_eq,
      (e.restrictScalars A).length_eq] at h
    exact h
  -- Sum by induction in ℕ∞; cancellation would require extra finiteness.
  have hsum : ∀ (n : ℕ) (f : Fin (n + 1) → ℕ∞) (g : Fin n → ℕ∞),
      (∀ i, f i.succ = f i.castSucc + g i) →
      f (Fin.last n) = f 0 + ∑ i, g i := by
    intro n
    induction n with
    | zero =>
      intro f g h
      simp
    | succ n ih =>
      intro f g h
      change f (Fin.last n).succ = _
      rw [h (Fin.last n), ih (fun i => f i.castSucc) (fun i => g i.castSucc)
        (fun i => h i.castSucc), Fin.sum_univ_castSucc, add_assoc, Fin.castSucc_zero]
  -- Identify the zero and top endpoints with the zero module and M.
  have h := hsum s.length (fun i => Module.length A (s i))
    (fun i => Module.length A (B ⧸ (p i).asIdeal)) hstep
  change Module.length A s.last = Module.length A s.head + _ at h
  rw [hhead, hlast, Module.length_eq_zero (R := A) (M := (⊥ : Submodule B M)), zero_add] at h
  rw [← (Submodule.topEquiv (R := B) (M := M)).restrictScalars A |>.length_eq]
  exact h

end Submission

namespace Submission

/-- A principal quotient of finite `A`-length has a `B`-composition series whose factors
are residue modules at height-one primes. The element `b` annihilates every factor,
so `b ≠ 0` rules out the zero ideal in the simple-module classification. -/
theorem p06_9e0f5043ff_wll_residue_composition_series :
    ∀ (A B : Type*) [CommRing A] [CommRing B] [IsDedekindDomain B] [Algebra A B]
      (b : B), b ≠ 0 → ∀ n : ℕ,
      Module.length A (B ⧸ Ideal.span ({b} : Set B)) = (n : ℕ∞) →
      ∃ s : CompositionSeries (Submodule B (B ⧸ Ideal.span ({b} : Set B))),
        s.head = ⊥ ∧ s.last = ⊤ ∧
        ∃ p : Fin s.length → IsDedekindDomain.HeightOneSpectrum B,
          ∀ i : Fin s.length,
            Nonempty ((↥(s i.succ) ⧸ (s i.castSucc).comap (s i.succ).subtype) ≃ₗ[B]
              (B ⧸ (p i).asIdeal)) := by
  intro A B _ _ _ _ b hb n hn
  classical
  let C := B ⧸ Ideal.span ({b} : Set B)
  -- Restricting scalars embeds the B-submodule lattice into the A-submodule lattice.
  have hfinite : IsFiniteLength A C := Module.length_ne_top_iff.mp (by
    rw [hn]
    exact ENat.natCast_ne_top n)
  obtain ⟨hnoeth, hart⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp hfinite
  have : IsNoetherian B C := isNoetherian_of_tower A hnoeth
  have : IsArtinian B C := isArtinian_of_tower A hart
  obtain ⟨s, hs_head, hs_last⟩ := exists_compositionSeries_of_isNoetherian_isArtinian B C
  refine ⟨s, hs_head, hs_last, ?_⟩
  -- The same nonzero element annihilates C and every subquotient of C.
  have hbC : b ∈ Module.annihilator B C := by
    rw [Ideal.annihilator_quotient]
    exact Ideal.subset_span (Set.mem_singleton b)
  have factors : ∀ i : Fin s.length, ∃ p : IsDedekindDomain.HeightOneSpectrum B,
      Nonempty ((↥(s i.succ) ⧸ (s i.castSucc).comap (s i.succ).subtype) ≃ₗ[B]
        (B ⧸ p.asIdeal)) := by
    intro i
    let N := (s i.castSucc).comap (s i.succ).subtype
    -- A covering step has a simple quotient, hence is a maximal-ideal quotient.
    have hsimple : IsSimpleModule B (↥(s i.succ) ⧸ N) :=
      (covBy_iff_quot_is_simple (s.step i).le).mp (s.step i)
    obtain ⟨m, hm, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp hsimple
    have hbN : b ∈ Module.annihilator B (s i.succ) :=
      (s i.succ).subtype.annihilator_le_of_injective (Submodule.injective_subtype _) hbC
    have hbS : b ∈ Module.annihilator B (↥(s i.succ) ⧸ N) :=
      N.mkQ.annihilator_le_of_surjective N.mkQ_surjective hbN
    have hbm : b ∈ m := by
      rwa [e.annihilator_eq, Ideal.annihilator_quotient] at hbS
    -- Containing b excludes the zero ideal, giving a height-one prime.
    have hm_ne : m ≠ ⊥ := by
      intro hm_bot
      exact hb (by simpa [hm_bot] using hbm)
    exact ⟨⟨m, hm.isPrime, hm_ne⟩, ⟨e⟩⟩
  choose p hp using factors
  exact ⟨p, hp⟩

end Submission

namespace Submission

/-- A residue module localized at a height-one prime is simple at its own prime
and is the zero module at every distinct height-one prime.

At its own prime, the localization equivalence over `B` transfers simplicity of
the residue field. Every nonzero element then also generates the module over the
localized ring, since the original scalars act through its canonical algebra map. -/
theorem p06_9e0f5043ff_llm_localized_residue_factors
    (B : Type*) [CommRing B] [IsDedekindDomain B]
    (p q : IsDedekindDomain.HeightOneSpectrum B) :
    (p = q → IsSimpleModule (Localization.AtPrime q.asIdeal)
      (LocalizedModule q.asIdeal.primeCompl (B ⧸ p.asIdeal))) ∧
    (p ≠ q → Subsingleton (LocalizedModule q.asIdeal.primeCompl (B ⧸ p.asIdeal))) := by
  constructor
  · rintro rfl
    -- At the same prime, every denominator acts invertibly on the residue field.
    let k := B ⧸ p.asIdeal
    let : Field k := Ideal.Quotient.field p.asIdeal
    let T := p.asIdeal.primeCompl
    have : IsLocalizedModule T (LinearMap.id : k →ₗ[B] k) := by
      refine ⟨?_, fun m ↦ ⟨(m, 1), by simp⟩, fun h ↦ ⟨1, by simpa using h⟩⟩
      intro s
      rw [Module.End.isUnit_iff]
      change Function.Bijective (fun m : k ↦ (s : B) • m)
      have hs : (Ideal.Quotient.mk p.asIdeal (s : B) : k) ≠ 0 :=
        fun h ↦ s.property ((Ideal.Quotient.eq_zero_iff_mem).mp h)
      simpa only [Algebra.smul_def, k, Ideal.Quotient.algebraMap_eq] using
        mulLeft_bijective₀ (Ideal.Quotient.mk p.asIdeal (s : B)) hs
    have : IsSimpleModule B k :=
      isSimpleModule_iff_isCoatom.mpr (Ideal.isMaximal_def.mp p.isMaximal)
    -- The localization equivalence preserves simplicity over B; enlarging scalars
    -- preserves the fact that each nonzero element generates the whole module.
    have : IsSimpleModule B (LocalizedModule T k) :=
      IsSimpleModule.congr
        (IsLocalizedModule.linearEquiv T (LocalizedModule.mkLinearMap T k) LinearMap.id)
    refine isSimpleModule_iff_toSpanSingleton_surjective.mpr
      ⟨IsSimpleModule.nontrivial B _, ?_⟩
    intro x hx y
    obtain ⟨b, hb⟩ := IsSimpleModule.toSpanSingleton_surjective B hx y
    exact ⟨algebraMap B (Localization.AtPrime p.asIdeal) b, by
      simpa only [LinearMap.toSpanSingleton_apply, algebraMap_smul] using hb⟩
  · intro hpq
    -- A distinct maximal ideal contains an annihilator outside the localization prime.
    have hnot : ¬p.asIdeal ≤ q.asIdeal := by
      intro h
      exact hpq (IsDedekindDomain.HeightOneSpectrum.asIdeal_injective
        (p.isMaximal.eq_of_le q.isPrime.ne_top h))
    obtain ⟨t, htp, htq⟩ := SetLike.not_le_iff_exists.mp hnot
    apply LocalizedModule.subsingleton_iff.mpr
    intro m
    refine ⟨t, htq, ?_⟩
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem.mpr htp, zero_mul]
open scoped BigOperators

/-- Length after localization is the sum of the localized successive quotient lengths.
The equality is in `ℕ∞`; the proof uses addition only and needs no finite-length hypothesis. -/
theorem p06_9e0f5043ff_llm_localized_series_sum
    (B M : Type*) [CommRing B] [AddCommGroup M] [Module B M]
    (T : Submonoid B) (s : CompositionSeries (Submodule B M))
    (hhead : s.head = ⊥) (hlast : s.last = ⊤) :
    Module.length (Localization T) (LocalizedModule T M) =
      Finset.sum Finset.univ (fun i : Fin s.length =>
        Module.length (Localization T)
          (LocalizedModule T (↥(s i.succ) ⧸ (s i.castSucc).comap (s i.succ).subtype))) := by
  -- Localize each short exact sequence of successive terms.
  have hstep (i : Fin s.length) :
      Module.length (Localization T) (LocalizedModule T (s i.succ)) =
        Module.length (Localization T) (LocalizedModule T (s i.castSucc)) +
          Module.length (Localization T)
            (LocalizedModule T (↥(s i.succ) ⧸ (s i.castSucc).comap (s i.succ).subtype)) := by
    let hle : s i.castSucc ≤ s i.succ := s.strictMono.monotone (Fin.castSucc_le_succ i)
    let f := Submodule.inclusion hle
    let g := ((s i.castSucc).comap (s i.succ).subtype).mkQ
    have hex : Function.Exact f g := by
      rw [LinearMap.exact_iff, Submodule.ker_mkQ, Submodule.range_inclusion]
    -- The localized maps are linear over `Localization T`. Clear a denominator
    -- to lift each localized kernel element through the original exact sequence.
    refine Module.length_eq_add_of_exact (LocalizedModule.map T f) (LocalizedModule.map T g)
      (LocalizedModule.map_injective T f (Submodule.inclusion_injective hle))
      (LocalizedModule.map_surjective T g (Submodule.mkQ_surjective _)) ?_
    intro y
    constructor
    · refine LocalizedModule.induction_on (fun m u hy => ?_) y
      rw [LocalizedModule.map_mk, ← LocalizedModule.zero_mk (1 : T),
        LocalizedModule.mk_eq, one_smul, smul_zero] at hy
      obtain ⟨a, haT, ha⟩ := Subtype.exists.1 hy
      rw [smul_zero, Submonoid.mk_smul, ← map_smul, hex (a • m)] at ha
      obtain ⟨x, hx⟩ := ha
      use LocalizedModule.mk x (⟨a, haT⟩ * u)
      rw [LocalizedModule.map_mk, hx,
        ← LocalizedModule.mk_cancel_common_left ⟨a, haT⟩ u m, Submonoid.mk_smul]
    · rintro ⟨x, hx⟩
      revert hx
      refine LocalizedModule.induction_on (fun m u hx => ?_) x
      rw [← hx, LocalizedModule.map_mk, LocalizedModule.map_mk,
        (hex (f m)).2 ⟨m, rfl⟩, LocalizedModule.zero_mk]
  -- Add the recurrences without subtracting or cancelling infinite lengths.
  have hsum : ∀ (n : ℕ) (l : Fin (n + 1) → ℕ∞) (q : Fin n → ℕ∞),
      (∀ i, l i.succ = l i.castSucc + q i) →
        l (Fin.last n) = l 0 + ∑ i, q i := by
    intro n
    induction n with
    | zero => intro l q h; simp
    | succ n ih =>
      intro l q h
      rw [← Fin.succ_last, h (Fin.last n), Fin.sum_univ_castSucc]
      have hprefix := ih (fun i => l i.castSucc) (fun i => q i.castSucc)
        (fun i => by simpa only [Fin.succ_castSucc] using h i.castSucc)
      rw [hprefix, Fin.castSucc_zero, add_assoc]
  have hzero : Module.length (Localization T) (LocalizedModule T (s 0)) = 0 := by
    change Module.length (Localization T) (LocalizedModule T s.head) = 0
    rw [hhead]
    exact Module.length_eq_zero
  have htop : Module.length (Localization T) (LocalizedModule T (s (Fin.last s.length))) =
      Module.length (Localization T) (LocalizedModule T M) := by
    change Module.length (Localization T) (LocalizedModule T s.last) = _
    rw [hlast]
    exact (IsLocalizedModule.mapEquiv T (LocalizedModule.mkLinearMap T (⊤ : Submodule B M))
      (LocalizedModule.mkLinearMap T M) (Localization T) (Submodule.topEquiv)).length_eq
  have h := hsum s.length
    (fun i => Module.length (Localization T) (LocalizedModule T (s i)))
    (fun i => Module.length (Localization T)
      (LocalizedModule T (↥(s i.succ) ⧸ (s i.castSucc).comap (s i.succ).subtype))) hstep
  simpa only [htop, hzero, zero_add] using h

end Submission


namespace Submission

/-- Localizing the given composition factors counts exactly the factors at `q`. -/
theorem p06_9e0f5043ff_wll_local_length_multiplicity
    (B : Type*) [CommRing B] [IsDedekindDomain B] (b : B)
    (s : CompositionSeries (Submodule B (B ⧸ Ideal.span ({b} : Set B))))
    (p : Fin s.length → IsDedekindDomain.HeightOneSpectrum B)
    (hhead : s.head = ⊥) (hlast : s.last = ⊤)
    (hfactors : ∀ i : Fin s.length,
      Nonempty ((↥(s i.succ) ⧸ (s i.castSucc).comap (s i.succ).subtype) ≃ₗ[B]
        (B ⧸ (p i).asIdeal)))
    (q : IsDedekindDomain.HeightOneSpectrum B) :
    Module.length (Localization.AtPrime q.asIdeal)
      (Localization.AtPrime q.asIdeal ⧸ Ideal.span
        ({algebraMap B (Localization.AtPrime q.asIdeal) b} :
          Set (Localization.AtPrime q.asIdeal))) =
      (Nat.card {i : Fin s.length // p i = q} : ℕ∞) := by
  classical
  let T := q.asIdeal.primeCompl
  let R := Localization.AtPrime q.asIdeal
  let I : Ideal B := Ideal.span ({b} : Set B)
  let f : B →ₗ[B] R := Algebra.linearMap B R
  -- The canonical localized quotient is the quotient by the image of `b`.
  have hI : I.localized' R T f = Ideal.span ({algebraMap B R b} : Set R) := by
    simpa only [I, Ideal.span, f, Set.image_singleton, Algebra.linearMap_apply] using
      (Submodule.localized'_span R T f ({b} : Set B))
  let e := (IsLocalizedModule.linearEquiv T (I.toLocalizedQuotient' R T f)
    (LocalizedModule.mkLinearMap T (B ⧸ I))).extendScalarsOfIsLocalization T R
  have hquot : Module.length R (R ⧸ Ideal.span ({algebraMap B R b} : Set R)) =
      Module.length R (LocalizedModule T (B ⧸ I)) := by
    rw [← hI]
    exact e.length_eq
  calc
    Module.length R (R ⧸ Ideal.span ({algebraMap B R b} : Set R)) =
        Module.length R (LocalizedModule T (B ⧸ I)) := hquot
    _ = ∑ i : Fin s.length, Module.length R
        (LocalizedModule T (↥(s i.succ) ⧸ (s i.castSucc).comap (s i.succ).subtype)) :=
      p06_9e0f5043ff_llm_localized_series_sum B (B ⧸ I) T s hhead hlast
    _ = ∑ i : Fin s.length, (if p i = q then (1 : ℕ∞) else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      let ei := IsLocalizedModule.mapEquiv T (LocalizedModule.mkLinearMap T _)
        (LocalizedModule.mkLinearMap T _) R (hfactors i).some
      rw [ei.length_eq]
      by_cases hi : p i = q
      · have := (p06_9e0f5043ff_llm_localized_residue_factors B (p i) q).1 hi
        simp only [if_pos hi, Module.length_eq_one]
      · have := (p06_9e0f5043ff_llm_localized_residue_factors B (p i) q).2 hi
        simp only [if_neg hi, Module.length_eq_zero]
    _ = (Nat.card {i : Fin s.length // p i = q} : ℕ∞) := by
      simp [Nat.card_eq_fintype_card, Fintype.card_subtype]

end Submission

namespace Submission

/-- Regroup residue composition factors by their height-one primes and substitute
the localized lengths, which count those factors. All sums remain in `ℕ∞`. -/
theorem p06_9e0f5043ff_ifl_weighted_local_lengths
    (A B : Type*) [CommRing A] [CommRing B] [IsDedekindDomain B] [Algebra A B]
    [Fintype (IsDedekindDomain.HeightOneSpectrum B)] (b : B) (hb : b ≠ 0)
    (n : ℕ) (hn : Module.length A (B ⧸ Ideal.span ({b} : Set B)) = (n : ℕ∞)) :
    Finset.sum Finset.univ (fun q : IsDedekindDomain.HeightOneSpectrum B =>
      Module.length A (B ⧸ q.asIdeal) *
        Module.length (Localization.AtPrime q.asIdeal)
          (Localization.AtPrime q.asIdeal ⧸
            Ideal.span ({algebraMap B (Localization.AtPrime q.asIdeal) b} :
              Set (Localization.AtPrime q.asIdeal)))) = (n : ℕ∞) := by
  classical
  obtain ⟨s, hs₀, hs₁, p, hp⟩ :=
    Submission.p06_9e0f5043ff_wll_residue_composition_series A B b hb n hn
  have hsum := Submission.p06_9e0f5043ff_wll_length_sum_factors
    A B (B ⧸ Ideal.span ({b} : Set B)) s p hs₀ hs₁ hp
  have hlocal := Submission.p06_9e0f5043ff_wll_local_length_multiplicity
    B b s p hs₀ hs₁ hp
  simp_rw [hlocal]
  calc
    _ = Finset.sum Finset.univ (fun q : IsDedekindDomain.HeightOneSpectrum B =>
        Finset.sum Finset.univ (fun _i : {i : Fin s.length // p i = q} =>
          Module.length A (B ⧸ q.asIdeal))) := by
      apply Finset.sum_congr rfl
      intro q _
      simp only [Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card,
        nsmul_eq_mul, mul_comm]
    _ = Finset.sum Finset.univ (fun i : Fin s.length =>
        Module.length A (B ⧸ (p i).asIdeal)) :=
      Fintype.sum_fiberwise' p (fun q => Module.length A (B ⧸ q.asIdeal))
    _ = (n : ℕ∞) := hsum.symm.trans hn
open IsDedekindDomain IsLocalRing AlgebraicCurve.Place

theorem p06_9e0f5043ff_ifl_residue_length_inertia
    (K E L : Type*) [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra K L] [Algebra E L] [IsScalarTower K E L]
    [FiniteDimensional E L] [Algebra.IsSeparable E L]
    (v : AlgebraicCurve.Place K E) (w : AlgebraicCurve.Place K L)
    (hw : w.restrict E = v) :
    Module.length v.toValuationSubring
      (integralClosureAt L v ⧸ (fiberCenter L v hw).asIdeal) =
        (w.inertiaDeg E : ℕ∞) := by
  classical
  subst v
  let A := (w.restrict E).toValuationSubring
  let B := integralClosureAt L (w.restrict E)
  let q := (fiberCenter L (w.restrict E) rfl).asIdeal
  -- The fiber center is the inverse image of the maximal ideal of O_w.
  let f : B →+* w.toValuationSubring :=
    (algebraMap B L).codRestrict w.toValuationSubring.toSubring
      (forall_mem_of_restrict_eq rfl)
  let g : B ⧸ q →+* w.ResidueField :=
    Ideal.Quotient.lift q ((residue _).comp f) (by
      intro b hb
      exact (Ideal.Quotient.eq_zero_iff_mem).mpr hb)
  have : q.IsMaximal := (fiberCenter L (w.restrict E) rfl).isMaximal
  let : Field (B ⧸ q) := Ideal.Quotient.field q
  have hg : Function.Surjective g := by
    -- Every element of O_w is a fraction with denominator outside the fiber center.
    intro y
    obtain ⟨x, rfl⟩ := residue_surjective (R := w.toValuationSubring) y
    have hx := x.property
    simp only [toValuationSubring_eq_of_restrict_eq (w := w) (v := w.restrict E) rfl] at hx
    obtain ⟨a, s, hs, hxs⟩ := hx
    have hs' : g (Ideal.Quotient.mk q s) ≠ 0 := by
      intro h
      have hmem : f s ∈ maximalIdeal w.toValuationSubring :=
        (Ideal.Quotient.eq_zero_iff_mem).mp h
      exact hs hmem
    refine ⟨Ideal.Quotient.mk q a / Ideal.Quotient.mk q s, ?_⟩
    rw [map_div₀, div_eq_iff hs']
    change residue _ (f a) = residue _ x * residue _ (f s)
    rw [← map_mul]
    apply congrArg (residue _)
    apply Subtype.ext
    change algebraMap B L a = (x : L) * algebraMap B L s
    rw [hxs]
    have hs0 : algebraMap B L s ≠ 0 := by
      intro h
      apply hs'
      change residue _ (f s) = 0
      have : f s = 0 := Subtype.ext h
      rw [this, map_zero]
    simpa only [div_eq_mul_inv] using (div_mul_cancel₀ (algebraMap B L a) hs0).symm
  let e := RingEquiv.ofBijective g ⟨g.injective, hg⟩
  -- Use exactly the residue-field scalar action defining the inertia degree.
  let : Algebra A w.ResidueField :=
    ((restrictResidueMap E w).comp (residue A)).toAlgebra
  have : IsScalarTower A (w.restrict E).ResidueField w.ResidueField :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let eA : (B ⧸ q) ≃ₐ[A] w.ResidueField :=
    { e with
      commutes' := by
        intro a
        change residue _ (f (algebraMap A B a)) =
          restrictResidueMap E w (residue A a)
        rw [restrictResidueMap_residue]
        apply congrArg (residue _)
        exact Subtype.ext rfl }
  have : Module.Finite A w.ResidueField :=
    Module.Finite.of_surjective eA.toLinearMap eA.surjective
  have : FiniteDimensional (w.restrict E).ResidueField w.ResidueField :=
    Module.Finite.of_restrictScalars_finite A (w.restrict E).ResidueField w.ResidueField
  -- Surjectivity of the residue map identifies the two submodule lattices.
  calc
    Module.length A (B ⧸ q) = Module.length A w.ResidueField := eA.toLinearEquiv.length_eq
    _ = Module.length (w.restrict E).ResidueField w.ResidueField :=
      Module.length_eq_of_surjective (residue_surjective (R := A))
    _ = (w.inertiaDeg E : ℕ∞) := Module.length_eq_finrank _ _

end Submission

namespace Submission

open AlgebraicCurve IsDedekindDomain

/-- The localized principal quotient and its corresponding place have the same
nonnegative order, witnessed by the exponent of a uniformizer. -/
theorem p06_9e0f5043ff_ifl_local_length_order
    (K E L : Type*) [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra K L] [Algebra E L] [IsScalarTower K E L]
    [FiniteDimensional E L] [Algebra.IsSeparable E L]
    (v : Place K E) (q : HeightOneSpectrum (Place.integralClosureAt L v))
    (R : Type*) [CommRing R] [IsDomain R]
    [Algebra (Place.integralClosureAt L v) R] [IsLocalization.AtPrime R q.asIdeal]
    (b : Place.integralClosureAt L v) (hb : b ≠ 0) :
    ∃ m : ℕ,
      Module.length R (R ⧸ Ideal.span
        ({algebraMap (Place.integralClosureAt L v) R b} : Set R)) = (m : ℕ∞) ∧
      (Place.placeOfPrime q).ord
        (algebraMap (Place.integralClosureAt L v) L b) = (m : ℤ) := by
  let B := Place.integralClosureAt L v
  let w := Place.placeOfPrime q
  let O := HeightOneSpectrum.valuationSubringAtPrime L q
  let : IsDiscreteValuationRing R :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain B q.ne_bot R
  let e : R ≃ₐ[B] O := IsLocalization.algEquiv q.asIdeal.primeCompl R O
  have hbR : algebraMap B R b ≠ 0 :=
    (map_ne_zero_iff (algebraMap B R)
      (IsLocalization.injective R q.asIdeal.primeCompl_le_nonZeroDivisors)).mpr hb
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨m, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hbR hπ
  refine ⟨m, ?_, ?_⟩
  -- The pinned Mathlib/RingTheory/DiscreteValuationRing/Basic.lean theorem
  -- combines Module.length_quotient with coheight_pow_maximalIdeal to compute
  -- the coheight of the uniformizer-power ideal, including when m = 0.
  · rw [hu, Ideal.span_singleton_mul_left_unit u.isUnit,
      ← Ideal.span_singleton_pow, ← hπ.maximalIdeal_eq]
    exact IsDiscreteValuationRing.length_quotient_pow_maximalIdeal R m
  · let u' : w.toValuationSubringˣ := Units.map e.toMonoidHom u
    have hπ' : Irreducible (e π : w.toValuationSubring) := hπ.map e.toMulEquiv
    -- The localization equivalence preserves the image of the original element.
    have he : ((e (algebraMap B R b) : O) : L) = algebraMap B L b := by
      change algebraMap O L (e (algebraMap B R b)) = _
      rw [e.commutes, ← IsScalarTower.algebraMap_apply B O L]
    have hcoe : algebraMap B L b =
        ((u' : w.toValuationSubring) : L) * ((e π : O) : L) ^ (m : ℤ) := by
      have h := congrArg (fun x : R => ((e x : O) : L)) hu
      rw [he] at h
      simpa [u', zpow_natCast] using h
    rw [hcoe]
    exact w.ord_unit_smul_zpow u' hπ' (m : ℤ)

/-- Reindex the weighted local quotient lengths by the places above `v`. -/
theorem p06_9e0f5043ff_lno_integral_fiber_length
    (K E L : Type*) [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra K L] [Algebra E L] [IsScalarTower K E L]
    [FiniteDimensional E L] [Algebra.IsSeparable E L]
    (v : AlgebraicCurve.Place K E) (b : AlgebraicCurve.Place.integralClosureAt L v)
    (hb : b ≠ 0) (n : ℕ)
    (hn : Module.length v.toValuationSubring
      (AlgebraicCurve.Place.integralClosureAt L v ⧸
        Ideal.span ({b} : Set (AlgebraicCurve.Place.integralClosureAt L v))) = (n : ℕ∞)) :
    Finset.sum (v.fiberOver L) (fun w => (w.inertiaDeg E : ℤ) *
      w.ord (algebraMap (AlgebraicCurve.Place.integralClosureAt L v) L b)) = (n : ℤ) := by
  classical
  let B := Place.integralClosureAt L v
  let Q := IsDedekindDomain.HeightOneSpectrum B
  let : Fintype {w : Place K L // w.restrict E = v} :=
    (Place.finite_setOf_restrict_eq (F' := L) v).fintype
  let : Fintype Q := Fintype.ofEquiv _ (Place.fiberEquiv L v)
  -- Choose the finite local lengths supplied by the local order formula.
  choose m hm_length hm_order using fun q : Q =>
    p06_9e0f5043ff_ifl_local_length_order K E L v q
      (Localization.AtPrime q.asIdeal) b hb
  have hresidue (q : Q) : Module.length v.toValuationSubring (B ⧸ q.asIdeal) =
      ((Place.placeOfPrime q).inertiaDeg E : ℕ∞) := by
    have h :=
      p06_9e0f5043ff_ifl_residue_length_inertia K E L v
        (Place.placeOfPrime q) (Place.restrict_placeOfPrime q)
    rw [Place.fiberCenter_placeOfPrime] at h
    exact h
  -- All summands are finite, so the weighted length identity descends to ℕ.
  have hsum_nat : Finset.sum Finset.univ
      (fun q : Q => (Place.placeOfPrime q).inertiaDeg E * m q) = n := by
    have hweighted :=
      p06_9e0f5043ff_ifl_weighted_local_lengths v.toValuationSubring B b hb n hn
    apply ENat.natCast_inj.mp
    rw [← hweighted, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro q _
    rw [Nat.cast_mul, hresidue q, hm_length q]
  have hsum_int : Finset.sum Finset.univ (fun q : Q =>
      ((Place.placeOfPrime q).inertiaDeg E : ℤ) * (m q : ℤ)) = (n : ℤ) := by
    exact_mod_cast hsum_nat
  -- Reindex by the canonical correspondence between places and prime ideals.
  calc
    Finset.sum (v.fiberOver L) (fun w => (w.inertiaDeg E : ℤ) *
        w.ord (algebraMap B L b)) =
        Finset.sum Finset.univ (fun q : Q =>
          ((Place.placeOfPrime q).inertiaDeg E : ℤ) * (m q : ℤ)) := by
      refine Finset.sum_bij
        (fun w hw => Place.fiberCenter L v ((Place.mem_fiberOver v).mp hw))
        (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
      · intro w hw w' hw' h
        exact Place.eq_of_fiberCenter_eq
          ((Place.mem_fiberOver v).mp hw) ((Place.mem_fiberOver v).mp hw') h
      · intro q _
        exact ⟨Place.placeOfPrime q,
          (Place.mem_fiberOver v).mpr (Place.restrict_placeOfPrime q),
          Place.fiberCenter_placeOfPrime q⟩
      · intro w hw
        have hplace : Place.placeOfPrime
            (Place.fiberCenter L v ((Place.mem_fiberOver v).mp hw)) = w :=
          congrArg Subtype.val ((Place.fiberEquiv L v).symm_apply_apply
            ⟨w, (Place.mem_fiberOver v).mp hw⟩)
        rw [← hm_order _, hplace]
    _ = (n : ℤ) := hsum_int

end Submission

namespace Submission

/-- Extend the integral norm-order identity to the fraction field of the integral closure. -/
theorem p06_9e0f5043ff_local_norm_order
    (K E L : Type*) [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra K L] [Algebra E L] [IsScalarTower K E L]
    [FiniteDimensional E L] [Algebra.IsSeparable E L]
    (v : AlgebraicCurve.Place K E) (f : L) (hf : f ≠ 0) :
    v.ord (Algebra.norm E f) = Finset.sum (v.fiberOver L)
      (fun w => (w.inertiaDeg E : ℤ) * w.ord f) := by
  classical
  let B := AlgebraicCurve.Place.integralClosureAt L v
  have hintegral (b : B) (hb : b ≠ 0) :
      v.ord (Algebra.norm E (algebraMap B L b)) =
        Finset.sum (v.fiberOver L)
          (fun w => (w.inertiaDeg E : ℤ) * w.ord (algebraMap B L b)) := by
    obtain ⟨n, hlength, hord⟩ :=
      p06_9e0f5043ff_lno_integral_norm_length K E L v b hb
    exact hord.trans (p06_9e0f5043ff_lno_integral_fiber_length K E L v b hb n hlength).symm
  obtain ⟨b, c, hc, hfrac⟩ := IsFractionRing.div_surjective B f
  have hcL : algebraMap B L c ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hc
  have hbL : algebraMap B L b ≠ 0 := by
    intro hb0
    apply hf
    rw [← hfrac, hb0, zero_div]
  have hb : b ≠ 0 := fun h => hbL (by rw [h, map_zero])
  have hcB : c ≠ 0 := fun h => hcL (by rw [h, map_zero])
  have hord (w : AlgebraicCurve.Place K L) :
      w.ord (algebraMap B L b / algebraMap B L c) =
        w.ord (algebraMap B L b) - w.ord (algebraMap B L c) := by
    rw [div_eq_mul_inv, w.ord_mul hbL (inv_ne_zero hcL), w.ord_inv, sub_eq_add_neg]
  calc
    v.ord (Algebra.norm E f) =
        v.ord (Algebra.norm E (algebraMap B L b)) -
          v.ord (Algebra.norm E (algebraMap B L c)) := by
      rw [← hfrac, div_eq_mul_inv, map_mul, Algebra.norm_inv,
        v.ord_mul (Algebra.norm_ne_zero_iff.mpr hbL)
          (inv_ne_zero (Algebra.norm_ne_zero_iff.mpr hcL)),
        v.ord_inv, sub_eq_add_neg]
    _ = Finset.sum (v.fiberOver L)
          (fun w => (w.inertiaDeg E : ℤ) * w.ord (algebraMap B L b)) -
        Finset.sum (v.fiberOver L)
          (fun w => (w.inertiaDeg E : ℤ) * w.ord (algebraMap B L c)) := by
      rw [hintegral b hb, hintegral c hcB]
    _ = Finset.sum (v.fiberOver L) (fun w => (w.inertiaDeg E : ℤ) * w.ord f) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro w _
      rw [← hfrac, hord, mul_sub]

end Submission
