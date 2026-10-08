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

open AlgebraicCurve
theorem AlgebraicCurve.hasPrincipalDivisors_of_transcendental (K : Type*) [Field K] [CharZero K] {F : Type*} [Field F]
    [Algebra K F] (x : F) (hx : Transcendental K x)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F] : HasPrincipalDivisors K F := by
  sorry

namespace Submission

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
