import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Mathlib.RingTheory.Length

namespace Submission

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
  classical
  have hstep (i : Fin s.length) :
      Module.length A (s i.succ) =
        Module.length A (s i.castSucc) + Module.length A (B ⧸ (p i).asIdeal) := by
    let N := (s i.castSucc).comap (s i.succ).subtype
    have h := Module.length_eq_add_of_exact
      (N.subtype.restrictScalars A) (N.mkQ.restrictScalars A)
      N.subtype_injective N.mkQ_surjective (LinearMap.exact_subtype_mkQ N)
    rw [(Submodule.comapSubtypeEquivOfLe (s.lt_succ i).le).restrictScalars A |>.length_eq,
      ((hfactors i).some.restrictScalars A).length_eq] at h
    exact h
  have hsum : ∀ (n : ℕ) (f : Fin (n + 1) → ℕ∞) (g : Fin n → ℕ∞),
      (∀ i, f i.succ = f i.castSucc + g i) →
      f (Fin.last n) = f 0 + ∑ i, g i := by
    intro n
    induction n with
    | zero => intro f g h; simp
    | succ n ih =>
      intro f g h
      change f (Fin.last n).succ = _
      rw [h (Fin.last n), ih (fun i => f i.castSucc) (fun i => g i.castSucc)
        (fun i => h i.castSucc), Fin.sum_univ_castSucc, add_assoc, Fin.castSucc_zero]
  have h := hsum s.length (fun i => Module.length A (s i))
    (fun i => Module.length A (B ⧸ (p i).asIdeal)) hstep
  change Module.length A s.last = Module.length A s.head + _ at h
  rw [hhead, hlast, Module.length_eq_zero (R := A) (M := (⊥ : Submodule B M)), zero_add] at h
  rw [← (Submodule.topEquiv (R := B) (M := M)).restrictScalars A |>.length_eq]
  exact h

end Submission
