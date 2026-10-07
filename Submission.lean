import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology

set_option autoImplicit false

namespace Submission

open Representation

/-- Transfer and projection on the kernels of the coinvariant norm maps. -/
theorem p04_tia_tate_neg_one_transfer
    {k G : Type _} [CommRing k] [Group G] [Fintype G]
    (A : Rep k G) (H : Subgroup G) [Fintype H] :
    ∃ T : A.tateHneg1 →ₗ[k] (Rep.res H.subtype A).tateHneg1,
    ∃ P : (Rep.res H.subtype A).tateHneg1 →ₗ[k] A.tateHneg1,
    ∀ x : A.tateHneg1, P (T x) = H.index • x := by
  classical
  let B := Rep.res H.subtype A
  let S : H.RightTransversal := default
  let U : H.LeftTransversal := default
  let : Fintype S.val := Fintype.ofFinite _
  let : Fintype U.val := Fintype.ofFinite _
  have hcard : Fintype.card S.val = H.index := by
    rw [← Nat.card_eq_fintype_card]
    exact S.property.card_right
  -- The projection is induced by the identity on the underlying module.
  let π : B.ρ.Coinvariants →ₗ[k] A.ρ.Coinvariants :=
    Coinvariants.lift B.ρ (Coinvariants.mk A.ρ) (fun h => by
      ext a
      exact Coinvariants.mk_self_apply A.ρ (h : G) a)
  have hπ (a : A) : π (Coinvariants.mk B.ρ a) = Coinvariants.mk A.ρ a := rfl
  -- A right transversal gives the transfer before taking G-coinvariants.
  let f : A →ₗ[k] B.ρ.Coinvariants :=
    ∑ s : S.val, Coinvariants.mk B.ρ ∘ₗ A.ρ (s : G)
  have hf (a : A) : f a = ∑ s : S.val, Coinvariants.mk B.ρ (A.ρ (s : G) a) := by
    simp only [f, LinearMap.sum_apply, LinearMap.comp_apply]
  have hrep (s : S.val) : (S.property.equiv (s : G)).2 = s := by
    have hs := congrArg Prod.snd (S.property.equiv.apply_symm_apply (1, s))
    simpa only [Subgroup.IsComplement.equiv_symm_apply, Subgroup.coe_one, one_mul] using hs
  have hclass (g : G) (a : A) :
      Coinvariants.mk B.ρ (A.ρ g a) =
        Coinvariants.mk B.ρ (A.ρ ((S.property.equiv g).2 : G) a) := by
    conv_lhs => rw [← S.property.equiv_fst_mul_equiv_snd g]
    rw [map_mul, Module.End.mul_apply]
    exact Coinvariants.mk_self_apply B.ρ (S.property.equiv g).1 _
  have hinv (g : G) : f ∘ₗ A.ρ g = f := by
    ext a
    rw [LinearMap.comp_apply, hf, hf]
    let r : S.val → S.val := fun s => (S.property.equiv ((s : G) * g)).2
    have hr : Function.Injective r := by
      intro s t hst
      have hc := S.property.equiv_snd_eq_iff_rightCosetEquivalence.mp hst
      have hc' : RightCosetEquivalence (H : Set G) (s : G) (t : G) := by
        simpa only [RightCosetEquivalence, rightCoset_eq_iff, mul_inv_rev,
          mul_assoc, mul_inv_cancel_left] using hc
      have he := S.property.equiv_snd_eq_iff_rightCosetEquivalence.mpr hc'
      simpa only [hrep] using he
    let e : S.val ≃ S.val := Equiv.ofBijective r ⟨hr, Finite.surjective_of_injective hr⟩
    refine Fintype.sum_equiv e _ _ (fun s => ?_)
    rw [← Module.End.mul_apply, ← map_mul]
    exact hclass ((s : G) * g) a
  let τ : A.ρ.Coinvariants →ₗ[k] B.ρ.Coinvariants := Coinvariants.lift A.ρ f hinv
  have hτ (a : A) : τ (Coinvariants.mk A.ρ a) = f a := rfl
  have hcomp (x : A.ρ.Coinvariants) : π (τ x) = H.index • x := by
    induction x using Coinvariants.induction_on with | h a =>
      rw [hτ, hf, map_sum]
      simp only [hπ, Coinvariants.mk_self_apply, Finset.sum_const, Finset.card_univ, hcard]
  -- The H-norm of the transfer is the G-norm, using H × S ≃ G.
  have hnormτ (a : A) : (B.ρ.normBar (f a) : A) = A.ρ.norm a := by
    rw [hf, map_sum]
    simp only [Submodule.coe_sum, normBar_mk, coe_normToInvariants_apply]
    simp only [Representation.norm, LinearMap.sum_apply]
    change (∑ s : S.val, ∑ h : H, A.ρ (h : G) (A.ρ (s : G) a)) = _
    rw [Finset.sum_comm, ← Fintype.sum_prod_type
      (fun p : H × S.val => A.ρ (p.1 : G) (A.ρ (p.2 : G) a))]
    change (∑ p : H × S.val, A.ρ (p.1 : G) (A.ρ (p.2 : G) a)) =
      ∑ g : G, A.ρ g a
    exact Fintype.sum_equiv S.property.equiv.symm _ _ (fun p => by
      simp only [Subgroup.IsComplement.equiv_symm_apply, map_mul, Module.End.mul_apply])
  -- The G-norm factors through the H-norm, using U × H ≃ G.
  have hnormπ (a : A) : A.ρ.norm a = ∑ t : U.val, A.ρ (t : G) (B.ρ.norm a) := by
    rw [Representation.norm, LinearMap.sum_apply]
    trans ∑ p : U.val × H, A.ρ (p.1 : G) (A.ρ (p.2 : G) a)
    · exact Fintype.sum_equiv U.property.equiv _ _ (fun g => by
        rw [← Module.End.mul_apply, ← map_mul, U.property.equiv_fst_mul_equiv_snd])
    · rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl (fun t _ => ?_)
      simp only [Representation.norm, LinearMap.sum_apply, map_sum]
      rfl
  have hτker (x : A.tateHneg1) : τ x.val ∈ LinearMap.ker B.ρ.normBar := by
    obtain ⟨a, ha⟩ := Coinvariants.mk_surjective A.ρ x.val
    have hx : A.ρ.norm a = 0 := by
      have hx := congrArg Subtype.val x.property
      simpa only [← ha, normBar_mk, coe_normToInvariants_apply, ZeroMemClass.coe_zero] using hx
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    rw [← ha, hτ, hnormτ, hx]
    rfl
  have hπker (x : B.tateHneg1) : π x.val ∈ LinearMap.ker A.ρ.normBar := by
    obtain ⟨a, ha⟩ := Coinvariants.mk_surjective B.ρ x.val
    have hx : B.ρ.norm a = 0 := by
      have hx := congrArg Subtype.val x.property
      simpa only [← ha, normBar_mk, coe_normToInvariants_apply, ZeroMemClass.coe_zero] using hx
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    rw [← ha, hπ, normBar_mk, coe_normToInvariants_apply, hnormπ, hx]
    simp only [map_zero, Finset.sum_const_zero, ZeroMemClass.coe_zero]
  let T : A.tateHneg1 →ₗ[k] B.tateHneg1 :=
    (τ ∘ₗ (LinearMap.ker A.ρ.normBar).subtype).codRestrict _ hτker
  let P : B.tateHneg1 →ₗ[k] A.tateHneg1 :=
    (π ∘ₗ (LinearMap.ker B.ρ.normBar).subtype).codRestrict _ hπker
  refine ⟨T, P, fun x => Subtype.ext ?_⟩
  exact hcomp x.val

end Submission
