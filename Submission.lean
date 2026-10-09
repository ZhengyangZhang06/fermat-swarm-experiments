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
