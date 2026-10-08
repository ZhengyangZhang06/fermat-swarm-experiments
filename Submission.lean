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
  rw [ht]
  simp only [mul_inv_rev, map_mul, Module.End.mul_apply]
  rw [hF, Representation.self_inv_apply]

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

namespace Submission

set_option warningAsError true in
/-- The finite coset sum defines a linear map on equivariant Hom spaces. -/
theorem p04_hct139_coset_average_exists
    {k G : Type _} [CommRing k] [Group G] [Fintype G]
    (A B : Rep k G) (H : Subgroup G) [Fintype H] [Fintype (G ⧸ H)] :
    ∃ C : (Quiver.Hom (Rep.res H.subtype B) (Rep.res H.subtype A)) →ₗ[k]
        (Quiver.Hom B A),
      ∀ (F : Quiver.Hom (Rep.res H.subtype B) (Rep.res H.subtype A)) (x : B),
        (C F).hom x = ∑ q : G ⧸ H, A.ρ q.out (F.hom (B.ρ q.out⁻¹ x)) := by
  classical
  let S (F : Quiver.Hom (Rep.res H.subtype B) (Rep.res H.subtype A)) : B →ₗ[k] A :=
    { toFun := fun x => ∑ q : G ⧸ H, A.ρ q.out (F.hom (B.ρ q.out⁻¹ x))
      map_add' := by
        intro x y
        simp only [map_add, Finset.sum_add_distrib]
      map_smul' := by
        intro a x
        simp only [map_smul, RingHom.id_apply, Finset.smul_sum] }
  let C (F : Quiver.Hom (Rep.res H.subtype B) (Rep.res H.subtype A)) :
      Quiver.Hom B A :=
    Rep.ofHom
      { toLinearMap := S F
        isIntertwining' := by
          intro g
          apply LinearMap.ext
          intro x
          exact p04_hca_bc7c754a4b_sum_equivariant A B H F g x }
  refine ⟨{ toFun := C, map_add' := ?_, map_smul' := ?_ }, ?_⟩
  · intro F₁ F₂
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    change S (F₁ + F₂) x = S F₁ x + S F₂ x
    simp [S, Rep.add_hom, Finset.sum_add_distrib]
  · intro a F
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    change S (a • F) x = a • S F x
    simp [S, Rep.smul_hom, Finset.smul_sum]
  · intro F x
    rfl


namespace Submission

/-- Coset averaging is natural in its source and acts by the subgroup index on restricted
`G`-equivariant morphisms. -/
theorem p04_hct139_coset_average_laws :
    ∀ {k G : Type _} [CommRing k] [Group G] [Fintype G]
      (A : Rep k G) (H : Subgroup G) [Fintype H] [Fintype (G ⧸ H)]
      (C : ∀ B : Rep k G,
        (Quiver.Hom (Rep.res H.subtype B) (Rep.res H.subtype A)) →ₗ[k] (Quiver.Hom B A)),
      (∀ (B : Rep k G)
        (F : Quiver.Hom (Rep.res H.subtype B) (Rep.res H.subtype A)) (x : B),
        (C B F).hom x = ∑ q : G ⧸ H, A.ρ q.out (F.hom (B.ρ q.out⁻¹ x))) →
      (∀ (B D : Rep k G) (f : Quiver.Hom D B)
        (F : Quiver.Hom (Rep.res H.subtype B) (Rep.res H.subtype A)),
        C D (CategoryTheory.CategoryStruct.comp ((Rep.resFunctor H.subtype).map f) F) =
          CategoryTheory.CategoryStruct.comp f (C B F)) ∧
      (∀ (B : Rep k G) (F : Quiver.Hom B A),
        C B ((Rep.resFunctor H.subtype).map F) = H.index • F) := by
  classical
  intro k G _ _ _ A H _ _ C hC
  constructor
  -- Naturality follows by commuting the source map through each averaging summand.
  · intro B D f F
    ext x
    change (C D _).hom x = (C B F).hom (f.hom x)
    rw [hC, hC]
    change (∑ q : G ⧸ H, A.ρ q.out (F.hom (f.hom (D.ρ q.out⁻¹ x)))) =
      ∑ q : G ⧸ H, A.ρ q.out (F.hom (B.ρ q.out⁻¹ (f.hom x)))
    simp only [Rep.hom_comm_apply]
  -- For a restricted equivariant map, each coset contributes the same value.
  · intro B F
    ext x
    change (C B _).hom x = H.index • F.hom x
    rw [hC]
    change (∑ q : G ⧸ H, A.ρ q.out (F.hom (B.ρ q.out⁻¹ x))) = H.index • F.hom x
    simp [Rep.hom_comm_apply, Subgroup.index_eq_card, Nat.card_eq_fintype_card]

end Submission
