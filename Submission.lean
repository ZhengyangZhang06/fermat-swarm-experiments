/-
Copyright 2026 Anthropic, PBC. Licensed under Apache-2.0; see LICENSE.
Source: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_CuspForm_gamma0_weight_two_eq_zero_of_genusFormula_eq_zero.lean
Modified: replaced the proof with sorry and removed P2M proof imports.
Requires the upstream Definitions modules and their dependencies.
-/

import Mathlib
import Definitions.Def_ModularCurve_GenusNumerics
attribute [-instance] HeckeEis.instFiniteIndexHeckeUpper ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite
attribute [-simp] ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one ModularCurve.Period.jConjMat_apply_zero_one ModularCurve.Period.jConjSL_coe ModularCurve.Period.jConjMat_apply_one_zero ModularCurve.Period.jConjMat_apply_one_one ModularCurve.Period.jConjGamma0_coe ModularCurve.Period.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_zero HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.CuspSpace.cuspDenomAux_infty
attribute [-simp] ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one

set_option autoImplicit false

theorem CuspForm.gamma0_weight_two_eq_zero_of_genusFormula_eq_zero (N : ℕ) [NeZero N]
    (hg : ModularCurve.genusFormula N = 0) (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) : f = 0 := by
  sorry


theorem Submission.p10_17ae7b7d_pde_decay_zero :
    ∀ (w : ℝ) (g A : ℂ → ℂ), 0 < w → ContinuousAt A 0 →
      (∀ z : ℂ, 0 < z.im →
        g z = A (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * z / (w : ℂ)))) →
      (∀ ε : ℝ, 0 < ε → ∃ Y : ℝ, ∀ z : ℂ,
        0 < z.im → Y ≤ z.im → ‖g z‖ ≤ ε) → A 0 = 0 := by
  intro w g A hw hA hfactor hdecay
  have hbound : ∀ ε : ℝ, 0 < ε →
      ∃ r : ℝ, 0 < r ∧ ∀ q : ℂ, q ≠ 0 → ‖q‖ < r → ‖A q‖ ≤ ε := by
    intro ε hε
    obtain ⟨Y, hY⟩ := hdecay ε hε
    refine ⟨Real.exp (-2 * Real.pi * max 1 Y / w), Real.exp_pos _, ?_⟩
    intro q hq hqr
    let z := Function.Periodic.invQParam w q
    have heq : Function.Periodic.qParam w z = q :=
      Function.Periodic.qParam_right_inv hw.ne' hq
    have him : max 1 Y < z.im :=
      (Function.Periodic.norm_qParam_lt_iff hw (max 1 Y) z).mp (by rwa [heq])
    have hz : 0 < z.im := lt_trans (lt_of_lt_of_le zero_lt_one (le_max_left 1 Y)) him
    have hgz : g z = A q := by
      have h := hfactor z hz
      change g z = A (Function.Periodic.qParam w z) at h
      rwa [heq] at h
    rw [← hgz]
    exact hY z hz (le_trans (le_max_right 1 Y) him.le)
  by_contra hzero
  have ha : 0 < ‖A 0‖ := norm_pos_iff.mpr hzero
  have hε : 0 < ‖A 0‖ / 3 := by positivity
  obtain ⟨r, hr, hbound⟩ := hbound (‖A 0‖ / 3) hε
  obtain ⟨δ, hδ, hclose⟩ := Metric.continuousAt_iff.mp hA (‖A 0‖ / 3) hε
  let q : ℂ := (min r δ / 2 : ℝ)
  have hqpos : 0 < min r δ / 2 := half_pos (lt_min hr hδ)
  have hqnorm : ‖q‖ = min r δ / 2 := Complex.norm_of_nonneg hqpos.le
  have hqr : ‖q‖ < r := by
    rw [hqnorm]
    linarith [min_le_left r δ]
  have hqδ : ‖q‖ < δ := by
    rw [hqnorm]
    linarith [min_le_right r δ]
  have hqne : q ≠ 0 := norm_pos_iff.mp (by rwa [hqnorm])
  have hsmall : ‖A q‖ ≤ ‖A 0‖ / 3 := hbound q hqne hqr
  have hnear : ‖A q - A 0‖ < ‖A 0‖ / 3 := by
    simpa only [dist_eq_norm] using hclose (by simpa only [dist_zero_right] using hqδ)
  have htriangle : ‖A 0‖ ≤ ‖A q - A 0‖ + ‖A q‖ := by
    calc
      ‖A 0‖ = ‖(A 0 - A q) + A q‖ := by rw [sub_add_cancel]
      _ ≤ ‖A 0 - A q‖ + ‖A q‖ := norm_add_le _ _
      _ = ‖A q - A 0‖ + ‖A q‖ := by rw [norm_sub_rev]
  linarith


theorem Submission.p10_17ae7b7d_efp_inverse_coset_eq_iff :
    ∀ (N : ℕ) [NeZero N] (A B : Matrix.SpecialLinearGroup (Fin 2) ℤ),
      (QuotientGroup.mk (A⁻¹) :
        (Matrix.SpecialLinearGroup (Fin 2) ℤ) ⧸ CongruenceSubgroup.Gamma0 N) =
          QuotientGroup.mk (B⁻¹) ↔
        ∃ u : (ZMod N)ˣ,
          (B 1 0 : ZMod N) = (u : ZMod N) * (A 1 0 : ZMod N) ∧
          (B 1 1 : ZMod N) = (u : ZMod N) * (A 1 1 : ZMod N) := by
  intro N _ A B
  constructor
  · intro h
    let E := B * A⁻¹
    have hE : E ∈ CongruenceSubgroup.Gamma0 N := by
      simpa only [inv_inv] using (QuotientGroup.eq.mp h.symm)
    have hzero : (E 1 0 : ZMod N) = 0 := CongruenceSubgroup.Gamma0_mem.mp hE
    have hdet : (E 0 0 : ZMod N) * (E 1 1 : ZMod N) -
        (E 0 1 : ZMod N) * (E 1 0 : ZMod N) = 1 := by
      have h := E.det_coe
      rw [Matrix.det_fin_two] at h
      simpa only [Int.cast_sub, Int.cast_mul, Int.cast_one] using
        congrArg (fun z : ℤ => (z : ZMod N)) h
    have hunit : (E 1 1 : ZMod N) * (E 0 0 : ZMod N) = 1 := by
      rw [hzero, mul_zero, sub_zero] at hdet
      simpa only [mul_comm] using hdet
    let u : (ZMod N)ˣ := Units.mkOfMulEqOne (E 1 1 : ZMod N) (E 0 0 : ZMod N) hunit
    have hBA : E * A = B := by
      dsimp [E]
      rw [mul_assoc, inv_mul_cancel, mul_one]
    have hrow (j : Fin 2) : (B 1 j : ZMod N) = (E 1 1 : ZMod N) * (A 1 j : ZMod N) := by
      have h := congrArg (fun C : Matrix.SpecialLinearGroup (Fin 2) ℤ =>
        (C 1 j : ZMod N)) hBA
      change (((E.1 * A.1) 1 j : ℤ) : ZMod N) = (B 1 j : ZMod N) at h
      simp only [Matrix.mul_apply, Fin.sum_univ_two, Int.cast_add, Int.cast_mul] at h
      change (E 1 0 : ZMod N) * (A 0 j : ZMod N) +
        (E 1 1 : ZMod N) * (A 1 j : ZMod N) = (B 1 j : ZMod N) at h
      simpa only [hzero, zero_mul, zero_add] using h.symm
    exact ⟨u, hrow 0, hrow 1⟩
  · rintro ⟨u, hc, hd⟩
    apply Eq.symm
    apply QuotientGroup.eq.mpr
    rw [inv_inv]
    apply CongruenceSubgroup.Gamma0_mem.mpr
    change (((B.1 * (A⁻¹).1) 1 0 : ℤ) : ZMod N) = 0
    rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    change ((B 1 0 * A 1 1 + B 1 1 * -(A 1 0) : ℤ) : ZMod N) = 0
    push_cast
    rw [hc, hd]
    ring
theorem Submission.p10_17ae7b7d_efp_unimodular_eigenrow_iff :
    ∀ (R : Type) [CommRing R] (k r s : R),
      (∃ x y : R, x * r + y * s = 1) →
      ((∃ u : Rˣ, s = (u : R) * r ∧ k * s - r = (u : R) * s) ↔
        IsUnit r ∧ ∃! t : R, s = r * t ∧ t ^ 2 - k * t + 1 = 0) := by
  intro R _ k r s ⟨x, y, hxy⟩
  constructor
  · rintro ⟨u, hs, heigen⟩
    have hinv : (x + y * (u : R)) * r = 1 := by
      calc
        (x + y * (u : R)) * r = x * r + y * s := by rw [hs]; ring
        _ = 1 := hxy
    have hr : IsUnit r := isUnit_iff_exists.mpr
      ⟨x + y * (u : R), by rw [mul_comm]; exact hinv, hinv⟩
    refine ⟨hr, (u : R), ⟨?_, ?_⟩, ?_⟩
    · exact hs.trans (mul_comm _ _)
    · apply hr.mul_left_cancel
      calc
        r * ((u : R) ^ 2 - k * (u : R) + 1) =
            (u : R) * s - (k * s - r) := by rw [hs]; ring
        _ = r * 0 := by rw [heigen, sub_self, mul_zero]
    · intro t ht
      apply hr.mul_left_cancel
      calc
        r * t = s := ht.1.symm
        _ = r * (u : R) := hs.trans (mul_comm _ _)
  · rintro ⟨_, t, ⟨hs, hpoly⟩, _⟩
    have hinv : t * (k - t) = 1 := by
      calc
        t * (k - t) = 1 - (t ^ 2 - k * t + 1) := by ring
        _ = 1 := by rw [hpoly, sub_zero]
    let u : Rˣ := ⟨t, k - t, hinv, by rw [mul_comm]; exact hinv⟩
    refine ⟨u, ?_, ?_⟩
    · change s = t * r
      exact hs.trans (mul_comm _ _)
    · change k * s - r = t * s
      calc
        k * s - r = t * s - r * (t ^ 2 - k * t + 1) := by rw [hs]; ring
        _ = t * s := by rw [hpoly, mul_zero, sub_zero]
theorem Submission.p10_17ae7b7d_cc_lift_unimodular_row :
    ∀ (N : ℕ) [NeZero N] (r s : ZMod N),
      (∃ x y : ZMod N, x * r + y * s = 1) →
      ∃ A : Matrix.SpecialLinearGroup (Fin 2) ℤ,
        (A 1 0 : ZMod N) = r ∧ (A 1 1 : ZMod N) = s := by
  intro N _ r s h
  classical
  by_cases hN : N = 1
  · subst N
    exact ⟨1, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  let D : ℕ := if s.val = 0 then N else s.val
  have hD : D ≠ 0 := by
    dsimp [D]
    split_ifs with hs
    · exact NeZero.ne N
    · exact hs
  have hDs : (D : ZMod N) = s := by
    dsimp [D]
    split_ifs with hs
    · have hs' : s = 0 := by
        simpa using congrArg (fun k : ℕ => (k : ZMod N)) hs
      simp [hs']
    · exact ZMod.natCast_zmod_val s
  let P := D.primeFactors.filter (fun p => ¬ p ∣ N)
  let M := ∏ p ∈ P, p
  have hNM : N.Coprime M := by
    apply Nat.coprime_prod_right_iff.mpr
    intro p hp
    obtain ⟨hpD, hpN⟩ := Finset.mem_filter.mp hp
    exact ((Nat.prime_of_mem_primeFactors hpD).coprime_iff_not_dvd.mpr hpN).symm
  obtain ⟨C, hCN, hCM⟩ := Nat.chineseRemainder hNM r.val 1
  have hCr : (C : ZMod N) = r := by
    rw [← ZMod.natCast_zmod_val r]
    exact (ZMod.natCast_eq_natCast_iff C r.val N).mpr hCN
  have hCD : C.Coprime D := by
    apply Nat.coprime_of_dvd'
    intro p hp hpC hpD
    by_cases hpN : p ∣ N
    · let f : ZMod N →+* ZMod p := ZMod.castHom hpN (ZMod p)
      have hrp : f r = 0 := by
        rw [← hCr, map_natCast]
        exact (ZMod.natCast_eq_zero_iff C p).mpr hpC
      have hsp : f s = 0 := by
        rw [← hDs, map_natCast]
        exact (ZMod.natCast_eq_zero_iff D p).mpr hpD
      obtain ⟨x, y, hxy⟩ := h
      have hz := congrArg f hxy
      simp only [map_add, map_mul, map_one, hrp, hsp, mul_zero, add_zero] at hz
      exact (ZMod.natCast_eq_zero_iff 1 p).mp (by simpa using hz.symm)
    · have hpP : p ∈ P := Finset.mem_filter.mpr ⟨hp.mem_primeFactors hpD hD, hpN⟩
      have hpM : p ∣ M := Finset.dvd_prod_of_mem (fun q : ℕ => q) hpP
      exact (hCM.dvd_iff hpM).mp hpC
  obtain ⟨A, hAC, hAD⟩ := hCD.isCoprime.exists_SL2_row (1 : Fin 2)
  refine ⟨A, ?_, ?_⟩
  · simpa only [hAC, Int.cast_natCast] using hCr
  · simpa only [hAD, Int.cast_natCast] using hDs


/-- Count elliptic fixed cosets by their unique normalized bottom rows. -/
theorem Submission.p10_17ae7b7d_cc_elliptic_fixed_points :
    ∀ (N : ℕ) [NeZero N],
      let Q := (Matrix.SpecialLinearGroup (Fin 2) ℤ) ⧸ CongruenceSubgroup.Gamma0 N
      Nat.card {q : Q // ModularGroup.S • q = q} = ModularCurve.nuTwo N ∧
        Nat.card {q : Q // (ModularGroup.S * ModularGroup.T) • q = q} =
          ModularCurve.nuThree N := by
  intro N _
  classical
  let G := Matrix.SpecialLinearGroup (Fin 2) ℤ
  let Q := G ⧸ CongruenceSubgroup.Gamma0 N
  let R := ZMod N
  -- Choose integral lifts of the normalized unimodular rows (1,t).
  have hlift (t : R) : ∃ A : G, (A 1 0 : R) = 1 ∧ (A 1 1 : R) = t :=
    Submission.p10_17ae7b7d_cc_lift_unimodular_row N 1 t ⟨1, 0, by simp⟩
  choose L hL₀ hL₁ using hlift
  let f (t : R) : Q := QuotientGroup.mk (L t)⁻¹
  have hf_inj : Function.Injective f := by
    intro t t' h
    obtain ⟨u, hu, ht⟩ :=
      (Submission.p10_17ae7b7d_efp_inverse_coset_eq_iff N (L t) (L t')).mp h
    rw [hL₀, hL₀, mul_one] at hu
    rw [hL₁, hL₁, ← hu, one_mul] at ht
    exact ht.symm
  -- Inversion turns right multiplication on rows into inverse left action.
  have hcount (B : G) (k : R)
      (hB : ∀ A : G, ((A * B) 1 0 : R) = (A 1 1 : R) ∧
        ((A * B) 1 1 : R) = k * (A 1 1 : R) - (A 1 0 : R)) :
      Nat.card {q : Q // B • q = q} = Nat.card {t : R // t ^ 2 - k * t + 1 = 0} := by
    have hnorm (A : G) :
        B • (QuotientGroup.mk A⁻¹ : Q) = QuotientGroup.mk A⁻¹ ↔
          IsUnit (A 1 0 : R) ∧
            ∃! t : R, (A 1 1 : R) = (A 1 0 : R) * t ∧ t ^ 2 - k * t + 1 = 0 := by
      have hrow : ∃ x y : R, x * (A 1 0 : R) + y * (A 1 1 : R) = 1 := by
        obtain ⟨x, y, hxy⟩ := A.isCoprime_row 1
        refine ⟨(x : R), (y : R), ?_⟩
        have h := congrArg (Int.castRingHom R) hxy
        simpa only [map_add, map_mul, map_one, Int.coe_castRingHom] using h
      rw [smul_eq_iff_eq_inv_smul]
      change (QuotientGroup.mk A⁻¹ : Q) = QuotientGroup.mk (B⁻¹ * A⁻¹) ↔ _
      rw [← mul_inv_rev, Submission.p10_17ae7b7d_efp_inverse_coset_eq_iff N A (A * B)]
      simp only [(hB A).1, (hB A).2]
      exact Submission.p10_17ae7b7d_efp_unimodular_eigenrow_iff R k _ _ hrow
    have hf_fixed (t : R) (ht : t ^ 2 - k * t + 1 = 0) : B • f t = f t := by
      apply (hnorm (L t)).mpr
      rw [hL₀, hL₁]
      refine ⟨isUnit_one, t, ⟨by simp, ht⟩, ?_⟩
      intro y hy
      simpa only [one_mul] using hy.1.symm
    let g : {t : R // t ^ 2 - k * t + 1 = 0} → {q : Q // B • q = q} :=
      fun t => ⟨f t, hf_fixed t t.property⟩
    apply (Nat.card_eq_of_bijective g ?_).symm
    constructor
    · intro t t' h
      exact Subtype.ext (hf_inj (congrArg Subtype.val h))
    · intro q
      obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective q.val
      let A : G := a⁻¹
      have hA : (QuotientGroup.mk A⁻¹ : Q) = q.val := by
        change (QuotientGroup.mk (a⁻¹)⁻¹ : Q) = q.val
        rw [inv_inv]
        exact ha
      have hfixed : B • (QuotientGroup.mk A⁻¹ : Q) = QuotientGroup.mk A⁻¹ := by
        rw [hA]
        exact q.property
      obtain ⟨⟨u, hu⟩, t, ⟨hst, ht⟩, _⟩ := (hnorm A).mp hfixed
      refine ⟨⟨t, ht⟩, Subtype.ext ?_⟩
      change f t = q.val
      rw [← hA]
      apply (Submission.p10_17ae7b7d_efp_inverse_coset_eq_iff N (L t) A).mpr
      refine ⟨u, ?_, ?_⟩
      · rw [hL₀, mul_one]
        exact hu.symm
      · rw [hL₁, hu]
        exact hst
  constructor
  · have h := hcount ModularGroup.S 0 (by
      intro A
      change ((A.1 * ModularGroup.S.1) 1 0 : R) = (A 1 1 : R) ∧
        ((A.1 * ModularGroup.S.1) 1 1 : R) = 0 * (A 1 1 : R) - (A 1 0 : R)
      simp [Matrix.mul_apply, Fin.sum_univ_two, ModularGroup.S, R])
    simpa only [zero_mul, sub_zero, ModularCurve.nuTwo] using h
  · have h := hcount (ModularGroup.S * ModularGroup.T) 1 (by
      intro A
      change ((A.1 * (ModularGroup.S.1 * ModularGroup.T.1)) 1 0 : R) = (A 1 1 : R) ∧
        ((A.1 * (ModularGroup.S.1 * ModularGroup.T.1)) 1 1 : R) =
          1 * (A 1 1 : R) - (A 1 0 : R)
      simp [Matrix.mul_apply, Fin.sum_univ_two, ModularGroup.S, ModularGroup.T,
        R, sub_eq_add_neg, add_comm])
    apply h.trans
    unfold ModularCurve.nuThree
    -- Negation changes t² - t + 1 into the defining polynomial for nuThree.
    apply Nat.card_congr
    refine
      { toFun := fun t => ⟨-t.val, ?_⟩
        invFun := fun x => ⟨-x.val, ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · calc
        (-t.val) ^ 2 + -t.val + 1 = t.val ^ 2 - 1 * t.val + 1 := by ring
        _ = 0 := t.property
    · calc
        (-x.val) ^ 2 - 1 * -x.val + 1 = x.val ^ 2 + x.val + 1 := by ring
        _ = 0 := x.property
    · intro t
      apply Subtype.ext
      exact neg_neg t.val
    · intro x
      apply Subtype.ext
      exact neg_neg x.val
