import Definitions.Def_AlgebraicCurve_PlacesOverDVR

namespace Submission

/-- An algebra equivalence transports places and preserves their residue degrees. -/
theorem p06_9e0f5043ff_pae_place_equivalence_degree :
    ∀ (K E L : Type*) [Field K] [Field E] [Field L] [Algebra K E] [Algebra K L]
      (e : E ≃ₐ[K] L),
      ∃ θ : AlgebraicCurve.Place K E ≃ AlgebraicCurve.Place K L,
        (∀ v : AlgebraicCurve.Place K E, (θ v).deg = v.deg) ∧
        (∀ v : AlgebraicCurve.Place K E,
          ∃ r : v.toValuationSubring ≃ₐ[K] (θ v).toValuationSubring,
            ∀ a : v.toValuationSubring, (r a : L) = e (a : E)) := by
  intro K E L _ _ _ _ _ e
  classical
  -- Prove both directions together so the fields retain independent universes.
  have transport :
      (∀ (f : E ≃ₐ[K] L) (v : AlgebraicCurve.Place K E),
        ∃ w : AlgebraicCurve.Place K L,
          w.toValuationSubring = v.toValuationSubring.comap f.symm.toRingHom ∧
          ∃ r : v.toValuationSubring ≃ₐ[K] w.toValuationSubring,
            ∀ a : v.toValuationSubring, (r a : L) = f (a : E)) ∧
      (∀ (f : L ≃ₐ[K] E) (v : AlgebraicCurve.Place K L),
        ∃ w : AlgebraicCurve.Place K E,
          w.toValuationSubring = v.toValuationSubring.comap f.symm.toRingHom ∧
          ∃ r : v.toValuationSubring ≃ₐ[K] w.toValuationSubring,
            ∀ a : v.toValuationSubring, (r a : E) = f (a : L)) := by
    constructor <;> intro f v
    all_goals
      let A := v.toValuationSubring.comap f.symm.toRingHom
      let r₀ : v.toValuationSubring ≃+* A :=
        { toFun := fun a => ⟨f a, by simp [A, a.property]⟩
          invFun := fun b => ⟨f.symm b, b.property⟩
          left_inv := fun a => Subtype.ext (f.symm_apply_apply a)
          right_inv := fun b => Subtype.ext (f.apply_symm_apply b)
          map_mul' := fun a b => Subtype.ext (f.map_mul a b)
          map_add' := fun a b => Subtype.ext (f.map_add a b) }
      let w : AlgebraicCurve.Place K _ :=
        { toValuationSubring := A
          algebraMap_mem' := fun k => by
            change f.symm (algebraMap K _ k) ∈ v.toValuationSubring
            rw [f.symm.commutes]
            exact v.algebraMap_mem' k
          ne_top' := by
            intro h
            apply v.ne_top'
            apply eq_top_iff.mpr
            intro x _
            have hx : f x ∈ A := by
              rw [h]
              exact ValuationSubring.mem_top _
            change f.symm (f x) ∈ v.toValuationSubring at hx
            simpa using hx
          isPrincipalIdealRing' := IsPrincipalIdealRing.of_surjective r₀ r₀.surjective }
      let := AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring w
      let r : v.toValuationSubring ≃ₐ[K] w.toValuationSubring :=
        { r₀ with commutes' := fun k => Subtype.ext (f.commutes k) }
      exact ⟨w, rfl, r, fun _ => rfl⟩
  choose T hT using transport.1 e
  choose S hS using transport.2 e.symm
  let θ : AlgebraicCurve.Place K E ≃ AlgebraicCurve.Place K L :=
    { toFun := T
      invFun := S
      left_inv := fun v => by
        apply AlgebraicCurve.Place.ext
        rw [(hS (T v)).1, (hT v).1]
        apply SetLike.ext
        intro x
        change e.symm (e x) ∈ v.toValuationSubring ↔ x ∈ v.toValuationSubring
        rw [e.symm_apply_apply]
      right_inv := fun v => by
        apply AlgebraicCurve.Place.ext
        rw [(hT (S v)).1, (hS v).1]
        apply SetLike.ext
        intro x
        change e (e.symm x) ∈ v.toValuationSubring ↔ x ∈ v.toValuationSubring
        rw [e.apply_symm_apply] }
  refine ⟨θ, ?_, fun v => (hT v).2⟩
  intro v
  obtain ⟨r, _⟩ := (hT v).2
  exact (IsLocalRing.ResidueField.mapAlgEquiv r).toLinearEquiv.finrank_eq.symm

end Submission
