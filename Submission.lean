import Definitions.Def_AlgebraicCurve_PlacesOverDVR

namespace Submission

/-- A place containing the polynomial coordinate is the localization at a monic
irreducible polynomial. The center and localization lemmas are inherited from
`Definitions.Def_AlgebraicCurve_PlacesOverDVR` in the frozen proof base. -/
theorem p06_9e0f5043ff_rmp_finite_place_classification
    (K : Type*) [Field K]
    (v : AlgebraicCurve.Place K (FractionRing (Polynomial K)))
    (hX : algebraMap (Polynomial K) (FractionRing (Polynomial K)) Polynomial.X ∈
      v.toValuationSubring) :
    ∃ q : Polynomial K, q.Monic ∧ Irreducible q ∧
      (∀ f : FractionRing (Polynomial K), f ∈ v.toValuationSubring ↔
        ∃ a b : Polynomial K, ¬ q ∣ b ∧
          f = algebraMap (Polynomial K) (FractionRing (Polynomial K)) a /
            algebraMap (Polynomial K) (FractionRing (Polynomial K)) b) := by
  classical
  -- Constants and the coordinate generate the polynomial ring.
  have hpoly : ∀ p : Polynomial K,
      algebraMap (Polynomial K) (FractionRing (Polynomial K)) p ∈
        v.toValuationSubring := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p r hp hr => simpa only [map_add] using add_mem hp hr
    | monomial n a =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow]
      apply mul_mem
      · rw [Polynomial.C_eq_algebraMap, ← IsScalarTower.algebraMap_apply]
        exact v.algebraMap_mem' a
      · exact pow_mem hX n
  -- Normalize the generator of the nonzero prime center.
  obtain ⟨q, hnorm, hspan⟩ := Ideal.exists_normalized_span_of_isPrincipal
    (AlgebraicCurve.Place.center (Polynomial K) v hpoly)
  have hq0 : q ≠ 0 := by
    intro hq
    apply v.center_ne_bot hpoly
    simpa only [hq, Ideal.span_singleton_zero] using hspan
  have hprime : (Ideal.span {q}).IsPrime := by
    rw [← hspan]
    infer_instance
  refine ⟨q, (Polynomial.normalize_eq_self_iff_monic hq0).mp hnorm,
    ((Ideal.span_singleton_prime hq0).mp hprime).irreducible, ?_⟩
  intro f
  rw [v.toValuationSubring_eq_of_forall_mem hpoly]
  change (∃ (a b : Polynomial K)
    (_ : b ∉ AlgebraicCurve.Place.center (Polynomial K) v hpoly),
      f = algebraMap (Polynomial K) (FractionRing (Polynomial K)) a *
        (algebraMap (Polynomial K) (FractionRing (Polynomial K)) b)⁻¹) ↔ _
  simp only [hspan, Ideal.mem_span_singleton, exists_prop, div_eq_mul_inv]

end Submission
