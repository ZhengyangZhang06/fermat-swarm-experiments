/-
Copyright 2026 Anthropic, PBC. Licensed under Apache-2.0; see LICENSE.
Source: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_Rep_isZero_tateCohomology_of_forall_sylow.lean
Selected atomic node: invariant transfer preserves norms and realizes the index action.
Requires the upstream Definitions modules and their dependencies.
-/

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology

set_option autoImplicit false
open CategoryTheory Rep

namespace Submission

theorem p04_tz91_invariant_restriction_norm_range
    {k G : Type _} [CommRing k] [Group G] [Fintype G]
    (A : Rep k G) (H : Subgroup G) [Fintype H] :
    ∃ j : A.ρ.invariants →ₗ[k] (Rep.res H.subtype A).ρ.invariants,
      (∀ a : A.ρ.invariants, (j a : A) = (a : A)) ∧
      LinearMap.range A.ρ.normBar ≤
        (LinearMap.range (Rep.res H.subtype A).ρ.normBar).comap j := by
  classical
  let j : A.ρ.invariants →ₗ[k] (Rep.res H.subtype A).ρ.invariants :=
    { toFun := fun a => ⟨(a : A),
        (Representation.mem_invariants _ _).2 fun h =>
          (Representation.mem_invariants _ _).1 a.property (h : G)⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine ⟨j, fun _ => rfl, ?_⟩
  intro y hy
  obtain ⟨x, rfl⟩ := hy
  obtain ⟨v, rfl⟩ := Representation.Coinvariants.mk_surjective A.ρ x
  -- The right-coset decomposition writes the ambient norm as a subgroup norm.
  let S : H.RightTransversal := default
  let : Fintype S.1 := Fintype.ofFinite _
  refine ⟨Representation.Coinvariants.mk (Rep.res H.subtype A).ρ
    (∑ s : S.1, A.ρ (s : G) v), ?_⟩
  apply Subtype.ext
  change (Rep.res H.subtype A).ρ.norm (∑ s : S.1, A.ρ (s : G) v) = A.ρ.norm v
  simp only [Representation.norm, LinearMap.sum_apply]
  simp only [map_sum]
  change (∑ h : H, ∑ s : S.1, A.ρ (h : G) (A.ρ (s : G) v)) = ∑ g : G, A.ρ g v
  simp only [← Module.End.mul_apply, ← map_mul]
  rw [← Fintype.sum_prod_type (fun p : H × S.1 => A.ρ ((p.1 : G) * (p.2 : G)) v)]
  exact Fintype.sum_equiv S.2.equiv.symm _ _ fun _ => rfl
/-- Summing translates over left cosets transfers subgroup invariants to ambient invariants.
It takes the subgroup norm to the ambient norm and acts on ambient invariants by the index. -/
theorem p04_tz91_invariant_transfer_norm_index
    {k G : Type _} [CommRing k] [Group G] [Fintype G]
    (A : Rep k G) (H : Subgroup G) [Fintype H] :
    ∃ c : (Rep.res H.subtype A).ρ.invariants →ₗ[k] A.ρ.invariants,
      (∀ v : A, c ((Rep.res H.subtype A).ρ.normToInvariants v) =
        A.ρ.normToInvariants v) ∧
      ∀ (a : A.ρ.invariants) (b : (Rep.res H.subtype A).ρ.invariants),
        (b : A) = (a : A) → c b = H.index • a := by
  classical
  let : Fintype (G ⧸ H) := Fintype.ofFinite _
  -- An H-invariant vector has the same translate for any representative of a coset.
  have hrep (b : (Rep.res H.subtype A).ρ.invariants) (g : G) :
      A.ρ (QuotientGroup.mk g : G ⧸ H).out (b : A) = A.ρ g (b : A) := by
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H g
    rw [hh, map_mul, Module.End.mul_apply]
    exact congrArg (A.ρ g) (b.property h)
  let t : (Rep.res H.subtype A).ρ.invariants →ₗ[k] A :=
    ∑ q : G ⧸ H, (A.ρ q.out).comp (Rep.res H.subtype A).ρ.invariants.subtype
  have ht (b : (Rep.res H.subtype A).ρ.invariants) : t b ∈ A.ρ.invariants := by
    intro g
    simp only [t, LinearMap.sum_apply, LinearMap.comp_apply, Submodule.subtype_apply, map_sum]
    refine Fintype.sum_equiv (MulAction.toPerm g) _ _ fun q => ?_
    change A.ρ g (A.ρ q.out (b : A)) = A.ρ (g • q).out (b : A)
    rw [← Module.End.mul_apply, ← map_mul]
    simpa only [← smul_eq_mul, MulAction.Quotient.mk_smul_out] using
      (hrep b (g * q.out)).symm
  let c := t.codRestrict A.ρ.invariants ht
  refine ⟨c, ?_, ?_⟩
  · intro v
    apply Subtype.ext
    -- Multiplication identifies a coset representative and an H-coordinate with G.
    let e : (G ⧸ H) × H ≃ G := Equiv.ofBijective
      (fun p => p.1.out * (p.2 : G)) (by
        constructor
        · rintro ⟨q, h⟩ ⟨q', h'⟩ heq
          have hq : q = q' := by
            have := congrArg (fun g : G => (QuotientGroup.mk g : G ⧸ H)) heq
            simpa only [QuotientGroup.mk_mul_of_mem _ h.property,
              QuotientGroup.mk_mul_of_mem _ h'.property, QuotientGroup.out_eq'] using this
          subst q'
          exact Prod.ext rfl (Subtype.ext (mul_left_cancel heq))
        · intro g
          refine ⟨⟨QuotientGroup.mk g, ⟨(QuotientGroup.mk g : G ⧸ H).out⁻¹ * g,
            QuotientGroup.eq.mp (QuotientGroup.out_eq' _)⟩⟩, ?_⟩
          exact mul_inv_cancel_left _ _)
    change t ((Rep.res H.subtype A).ρ.normToInvariants v) = A.ρ.norm v
    simp only [t, LinearMap.sum_apply, LinearMap.comp_apply, Submodule.subtype_apply,
      Representation.coe_normToInvariants_apply, Representation.norm, map_sum]
    rw [← Fintype.sum_prod_type']
    refine Fintype.sum_equiv e _ _ fun p => ?_
    change A.ρ p.1.out (A.ρ (p.2 : G) v) = A.ρ (p.1.out * (p.2 : G)) v
    rw [map_mul, Module.End.mul_apply]
  · intro a b hab
    apply Subtype.ext
    change t b = H.index • (a : A)
    have ha : ∀ g : G, A.ρ g (a : A) = a := a.property
    simp only [t, LinearMap.sum_apply, LinearMap.comp_apply, Submodule.subtype_apply,
      hab, ha, Finset.sum_const, Finset.card_univ]
    rw [Subgroup.index_eq_card, Nat.card_eq_fintype_card]

end Submission
