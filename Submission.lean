/-
Copyright 2026 Anthropic, PBC. Licensed under Apache-2.0; see LICENSE.
Source: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_AlgebraicCurve_hasPrincipalDivisors_of_transcendental.lean
Modified: implements the selected fraction-unit criterion in namespace Submission.
Requires the upstream Definitions modules and their dependencies.
-/

import Definitions.Def_AlgebraicCurve_PlacesOverDVR

namespace Submission

set_option warningAsError true

theorem p06_9e0f5043ff_fno_fraction_isunit
    (K F : Type*) [Field K] [Field F] [Algebra K F] (x : F)
    (hx : Transcendental K x) (q : Polynomial K) (_hqmonic : q.Monic)
    (hq : Irreducible q) (v : AlgebraicCurve.Place K F)
    (hmem : ∀ f : F, f ∈ v.toValuationSubring ↔
      ∃ a b : Polynomial K, ¬ q ∣ b ∧
        f = Polynomial.aeval x a / Polynomial.aeval x b)
    (a b : Polynomial K) (z : v.toValuationSubring) (hb : ¬ q ∣ b)
    (hz : (z : F) = Polynomial.aeval x a / Polynomial.aeval x b) :
    IsUnit z ↔ ¬ q ∣ a := by
  have hinj : Function.Injective (Polynomial.aeval x : Polynomial K →ₐ[K] F) :=
    transcendental_iff_injective.mp hx
  have hnonzero : ∀ p : Polynomial K, ¬ q ∣ p → Polynomial.aeval x p ≠ 0 := by
    intro p hp he
    have hpzero : p = 0 := hinj (by simpa only [map_zero] using he)
    exact hp (hpzero ▸ dvd_zero q)
  have hbzero := hnonzero b hb
  constructor
  · intro hu hqa
    obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.mp hu
    obtain ⟨c, d, hd, hwd⟩ := (hmem (w : F)).mp w.property
    have hprod : Polynomial.aeval x a * Polynomial.aeval x c =
        Polynomial.aeval x b * Polynomial.aeval x d := by
      have heq : (z : F) * (w : F) = 1 :=
        congrArg (fun t : v.toValuationSubring => (t : F)) hw
      rw [hz, hwd, div_mul_div_comm] at heq
      exact (div_eq_one_iff_eq (mul_ne_zero hbzero (hnonzero d hd))).mp heq
    have hpoly : a * c = b * d := hinj (by simpa only [map_mul] using hprod)
    have hdiv : q ∣ b * d := hpoly ▸ dvd_mul_of_dvd_left hqa c
    exact (hq.prime.dvd_or_dvd hdiv).elim hb hd
  · intro ha
    have hwmem : Polynomial.aeval x b / Polynomial.aeval x a ∈ v.toValuationSubring :=
      (hmem _).mpr ⟨b, a, ha, rfl⟩
    apply isUnit_iff_exists_inv.mpr
    refine ⟨⟨_, hwmem⟩, ?_⟩
    apply Subtype.ext
    change (z : F) * (Polynomial.aeval x b / Polynomial.aeval x a) = 1
    rw [hz, div_mul_div_comm, mul_comm (Polynomial.aeval x b) (Polynomial.aeval x a)]
    exact div_self (mul_ne_zero (hnonzero a ha) hbzero)

end Submission
