/-
Copyright 2026 Anthropic, PBC. Licensed under Apache-2.0; see LICENSE.
Source: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_CuspForm_span_heckeTLin_eigen_eq_top.lean
Modified: replaced the proof with sorry and removed P2M proof imports.
Requires the upstream Definitions modules and their dependencies.
-/

import Definitions.Def_ModularForm_HeckeOperatorForms
attribute [-instance] FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2
attribute [-simp] FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero

theorem CuspForm.span_heckeTLin_eigen_eq_top (M : ℕ) [NeZero M] :
    Submodule.span ℂ {v : CuspForm (CongruenceSubgroup.Gamma0 M) 2 |
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M), ∃ c : ℂ,
        CuspForm.heckeTLin 2 hℓ hℓM v = c • v} = ⊤ := by
  sorry

open ModularForm ModularFormClass
open P2MW.S_ModularForm_mdifferentiable_heckeT.M4cP1W2

namespace Submission

/-- Good-prime weight-two Hecke operators commute on cusp forms of level `M`. -/
theorem f036cc6b1f_hecke_commute :
    ∀ (M : ℕ) [NeZero M] (p r : ℕ) (hp : p.Prime) (hr : r.Prime)
      (hpM : ¬ p ∣ M) (hrM : ¬ r ∣ M),
      (CuspForm.heckeTLin 2 hp hpM).comp (CuspForm.heckeTLin 2 hr hrM) =
        (CuspForm.heckeTLin 2 hr hrM).comp (CuspForm.heckeTLin 2 hp hpM) := by
  intro M _ p r hp hr hpM hrM
  by_cases hpr : p = r
  · subst r
    rfl
  have hcop : p.Coprime r := (Nat.coprime_primes hp hr).mpr hpr
  have hpr' : ¬ p ∣ r := hp.coprime_iff_not_dvd.mp hcop
  have hrp' : ¬ r ∣ p := hr.coprime_iff_not_dvd.mp hcop.symm
  have hΓ : (1 : ℝ) ∈
      (CongruenceSubgroup.Gamma0 M : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
    simp
  -- P2M/Sol/S_ModularForm_mdifferentiable_heckeT.lean, already present at
  -- proof base 674e47109a2c121849b48a3754cad6d3c648d80e, proves this coefficient
  -- formula for the exact bundled Hecke normalization and qCoeff uniqueness below.
  have hcoeff (s : ℕ) (hs : s.Prime) (hsM : ¬ s ∣ M)
      (g : CuspForm (CongruenceSubgroup.Gamma0 M) 2) :
      qCoeff (CuspForm.heckeTLin 2 hs hsM g) = coeffHeckeT 2 s (qCoeff g) := by
    funext n
    exact qCoeff_heckeT_class hs.ne_zero g hΓ n
  refine LinearMap.ext fun f => eq_of_forall_qCoeff_eq hΓ fun n => ?_
  change qCoeff (CuspForm.heckeTLin 2 hp hpM (CuspForm.heckeTLin 2 hr hrM f)) n =
    qCoeff (CuspForm.heckeTLin 2 hr hrM (CuspForm.heckeTLin 2 hp hpM f)) n
  rw [hcoeff p hp hpM, hcoeff r hr hrM, hcoeff r hr hrM, hcoeff p hp hpM]
  simp only [coeffHeckeT_apply, show (2 : ℤ) - 1 = 1 from rfl, zpow_one,
    hp.dvd_mul, hr.dvd_mul, hpr', hrp', or_false]
  -- These four divisibility cases also include the constant coefficient `n = 0`.
  by_cases hpn : p ∣ n <;> by_cases hrn : r ∣ n
  · have hrnp : r ∣ n / p :=
      (Nat.dvd_div_iff_mul_dvd hpn).mpr (hcop.mul_dvd_of_dvd_of_dvd hpn hrn)
    have hpnr : p ∣ n / r :=
      (Nat.dvd_div_iff_mul_dvd hrn).mpr (hcop.symm.mul_dvd_of_dvd_of_dvd hrn hpn)
    simp only [if_pos hpn, if_pos hrn, if_pos hrnp, if_pos hpnr]
    rw [Nat.mul_comm n p, Nat.mul_comm n r, Nat.mul_div_assoc p hrn,
      Nat.mul_div_assoc r hpn]
    simp only [Nat.div_div_eq_div_mul, Nat.mul_comm, Nat.mul_left_comm]
    ring
  · have hrnp : ¬ r ∣ n / p := fun h => hrn (dvd_trans h (Nat.div_dvd_of_dvd hpn))
    simp only [if_pos hpn, if_neg hrn, if_neg hrnp, add_zero]
    rw [Nat.mul_comm n r, Nat.mul_div_assoc r hpn]
    simp only [Nat.mul_comm, Nat.mul_left_comm]
  · have hpnr : ¬ p ∣ n / r := fun h => hpn (dvd_trans h (Nat.div_dvd_of_dvd hrn))
    simp only [if_neg hpn, if_pos hrn, if_neg hpnr, add_zero]
    rw [Nat.mul_comm n p, Nat.mul_div_assoc p hrn]
    simp only [Nat.mul_comm, Nat.mul_left_comm]
  · simp only [if_neg hpn, if_neg hrn, add_zero]
    congr 1
    exact Nat.mul_right_comm n p r

end Submission
