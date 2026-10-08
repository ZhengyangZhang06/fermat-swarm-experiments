/-
Copyright 2026 Anthropic, PBC. Licensed under Apache-2.0; see LICENSE.
Source: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_Rep_isZero_tateCohomology_of_forall_sylow.lean
Modified: replaced the proof with sorry and removed P2M proof imports.
Requires the upstream Definitions modules and their dependencies.
-/

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
attribute [-simp] Representation.TateResCor.cosetDecomp_apply Rep.coe_tateHneg1Res_apply Representation.TateResCor.coe_tateHneg1Cores_apply Representation.TateResCor.tateH0Res_mk Rep.coe_tateHneg1Cores_apply Rep.tateH0Res_mk Representation.TateResCor.coe_cosetNormInvariants_apply Rep.tateH0Cores_mk Representation.TateResCor.coinvariantsCores_mk Representation.TateResCor.coinvariantsTransfer_mk Representation.TateResCor.tateH0Cores_mk Representation.TateResCor.coe_tateHneg1Res_apply Rep.coe_tateδneg2_apply

set_option autoImplicit false
universe u
open CategoryTheory Rep
theorem Rep.isZero_tateCohomology_of_forall_sylow {k G : Type u} [CommRing k] [Group G] [Fintype G]
    (A : Rep.{u} k G) (q : ℤ)
    (h : ∀ (p : ℕ) [Fact p.Prime] (P : Sylow p G) [Fintype (P : Subgroup G)],
      CategoryTheory.Limits.IsZero ((Rep.res (P : Subgroup G).subtype A).tateCohomology q)) :
    CategoryTheory.Limits.IsZero (A.tateCohomology q) := by
  sorry

namespace Submission

set_option warningAsError true in
/-- Conjugating an `H`-equivariant morphism depends only on the left coset in `G ⧸ H`.
The proof uses `QuotientGroup.eq` to identify the subgroup element and
`Rep.hom_comm_apply` to cancel its action through the restricted morphism. -/

namespace Submission

set_option warningAsError true in
/-- Conjugating an `H`-equivariant morphism depends only on the left coset in `G ⧸ H`. -/
theorem p04_hca_bc7c754a4b_summand_eq_of_coset_eq
    {k G : Type _} [CommRing k] [Group G] (A B : Rep k G) (H : Subgroup G)
    (F : Quiver.Hom (Rep.res H.subtype B) (Rep.res H.subtype A)) (s t : G)
    (hst : (QuotientGroup.mk s : G ⧸ H) = QuotientGroup.mk t) (x : B) :
    A.ρ s (F.hom (B.ρ s⁻¹ x)) = A.ρ t (F.hom (B.ρ t⁻¹ x)) := by
  -- Equal left cosets differ by right multiplication by an element of H.
  let h : H := ⟨s⁻¹ * t, QuotientGroup.eq.mp hst⟩
  have ht : t = s * (h : G) := by simp [h]
  -- Equivariance moves the inverse subgroup action through F.
  have hF : F.hom (B.ρ (h : G)⁻¹ (B.ρ s⁻¹ x)) =
      A.ρ (h : G)⁻¹ (F.hom (B.ρ s⁻¹ x)) :=
    Rep.hom_comm_apply F h⁻¹ (B.ρ s⁻¹ x)
  -- Expand the product action, use equivariance, and cancel the inverse actions.
  let h : H := ⟨s⁻¹ * t, QuotientGroup.eq.mp hst⟩
  have ht : t = s * (h : G) := by simp [h]
  -- Equivariance moves the inverse subgroup action through F.
  have hF : F.hom (B.ρ (h : G)⁻¹ (B.ρ s⁻¹ x)) =
      A.ρ (h : G)⁻¹ (F.hom (B.ρ s⁻¹ x)) :=
    Rep.hom_comm_apply F h⁻¹ (B.ρ s⁻¹ x)
  rw [ht]
  simp only [mul_inv_rev, map_mul, Module.End.mul_apply]
  rw [hF, Representation.self_inv_apply]

end Submission

namespace Submission

open CategoryTheory

/-- The restricted standard resolution computes subgroup homology.
Subgroup restriction is exact and preserves projective objects, so the restricted
standard resolution resolves the trivial representation of the subgroup.
`groupHomologyIso` identifies its tensor-coinvariant homology in every degree,
including zero. The restriction instances are in mathlib's `Rep/Res.lean` and
`Coinduced.lean`; the comparison is in `Homological/GroupHomology/Basic.lean`,
all under `Mathlib/RepresentationTheory`. The same restricted-resolution
construction is used in `Homological/GroupHomology/Shapiro.lean`. -/
theorem p04_ht_restricted_standard_comparison
    {k G : Type _} [CommRing k] [Group G] [Fintype G]
    (A : Rep k G) (H : Subgroup G) [Fintype H] (n : ℕ) :
    Nonempty
      (((((Rep.resFunctor (k := k) H.subtype).mapHomologicalComplex
          (ComplexShape.down ℕ)).obj (Rep.standardComplex k G)).coinvariantsTensorObj
          (Rep.res H.subtype A)).homology n ≃ₗ[k]
        groupHomology (Rep.res H.subtype A) n) := by
  classical
  let P : ProjectiveResolution (Rep.trivial k H k) :=
    (Rep.resFunctor (k := k) H.subtype).mapProjectiveResolution (Rep.standardResolution k G)
  -- `mapProjectiveResolution` gives exactly the complex in the frozen goal.
  -- Reverse the library comparison to start at its tensor-coinvariant homology.
  exact ⟨(groupHomologyIso (Rep.res H.subtype A) n P).symm.toLinearEquiv⟩
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
It takes the subgroup norm to the ambient norm and acts on ambient invariants by the index.

The coset representatives use `QuotientGroup.mk_out_eq_mul` from Mathlib's
`GroupTheory.Coset.Defs`; the norm is the `normToInvariants` map from
`Definitions.Def_GroupCohomology_TateCohomology`. Left multiplication on cosets uses
`MulAction.Quotient.mk_smul_out` from `GroupTheory.GroupAction.Quotient`, and
`Subgroup.index_eq_card` from `GroupTheory.Index` identifies the number of summands.
The multiplication bijection is proved locally so its formula remains explicit in the norm sum. -/
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
  -- Summing linear maps gives the transfer's linearity before restricting its codomain.
  let t : (Rep.res H.subtype A).ρ.invariants →ₗ[k] A :=
    ∑ q : G ⧸ H, (A.ρ q.out).comp (Rep.res H.subtype A).ρ.invariants.subtype
  have ht (b : (Rep.res H.subtype A).ρ.invariants) : t b ∈ A.ρ.invariants := by
    intro g
    simp only [t, LinearMap.sum_apply, LinearMap.comp_apply, Submodule.subtype_apply, map_sum]
    -- Left multiplication permutes the cosets, and hrep identifies their translates.
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

theorem Submission.p04_hca_bc7c754a4b_sum_equivariant :
    ∀ {k G : Type _} [CommRing k] [Group G] (A B : Rep k G) (H : Subgroup G)
      [Fintype (G ⧸ H)]
      (F : Quiver.Hom (Rep.res H.subtype B) (Rep.res H.subtype A)) (g : G) (x : B),
      (∑ q : G ⧸ H, A.ρ q.out (F.hom (B.ρ q.out⁻¹ (B.ρ g x)))) =
        A.ρ g (∑ q : G ⧸ H, A.ρ q.out (F.hom (B.ρ q.out⁻¹ x))) := by
  intro k G _ _ A B H _ F g x
  classical
  let e : (G ⧸ H) ≃ (G ⧸ H) :=
    { toFun := fun q => g • q
      invFun := fun q => g⁻¹ • q
      left_inv := fun q => inv_smul_smul g q
      right_inv := fun q => smul_inv_smul g q }
  calc
    (∑ q : G ⧸ H, A.ρ q.out (F.hom (B.ρ q.out⁻¹ (B.ρ g x)))) =
        ∑ q : G ⧸ H, A.ρ (g • q).out (F.hom (B.ρ (g • q).out⁻¹ (B.ρ g x))) :=
      (e.sum_comp fun q => A.ρ q.out (F.hom (B.ρ q.out⁻¹ (B.ρ g x)))).symm
    _ = ∑ q : G ⧸ H, A.ρ (g * q.out)
        (F.hom (B.ρ (g * q.out)⁻¹ (B.ρ g x))) := by
      apply Finset.sum_congr rfl
      intro q _
      apply Submission.p04_hca_bc7c754a4b_summand_eq_of_coset_eq A B H F
      rw [QuotientGroup.out_eq']
      exact (MulAction.Quotient.mk_smul_out H g q).symm
    _ = ∑ q : G ⧸ H, A.ρ g (A.ρ q.out (F.hom (B.ρ q.out⁻¹ x))) := by
      apply Finset.sum_congr rfl
      intro q _
      simp only [mul_inv_rev, map_mul, Module.End.mul_apply, Representation.inv_self_apply]
    _ = A.ρ g (∑ q : G ⧸ H, A.ρ q.out (F.hom (B.ρ q.out⁻¹ x))) :=
      (map_sum (A.ρ g) _ _).symm
