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
open CategoryTheory Rep

theorem Rep.isZero_tateCohomology_of_forall_sylow {k G : Type u} [CommRing k] [Group G] [Fintype G]
    (A : Rep.{u} k G) (q : ℤ)
    (h : ∀ (p : ℕ) [Fact p.Prime] (P : Sylow p G) [Fintype (P : Subgroup G)],
      CategoryTheory.Limits.IsZero ((Rep.res (P : Subgroup G).subtype A).tateCohomology q)) :
    CategoryTheory.Limits.IsZero (A.tateCohomology q) := by
  sorry

namespace Submission

/-- Restriction and corestriction on group cohomology compose to the subgroup index. -/
theorem p04_tia_cohomology_transfer {k G : Type u} [CommRing k] [Group G] [Fintype G]
    (A : Rep k G) (H : Subgroup G) [Fintype H] (n : ℕ) :
    ∃ R : groupCohomology A n →ₗ[k] groupCohomology (Rep.res H.subtype A) n,
      ∃ C : groupCohomology (Rep.res H.subtype A) n →ₗ[k] groupCohomology A n,
        ∀ x : groupCohomology A n, C (R x) = H.index • x := by
  classical
  obtain ⟨e⟩ := p04_tia_coh_restricted_standard_homotopy_equiv (k := k) H
  obtain ⟨r, c, hrc⟩ := p04_tia_coh_hom_complex_transfer A H (Rep.standardComplex k G)
  -- Applying Hom(-, Res A) reverses the comparison of the two resolutions.
  let F := ((linearYoneda k (Rep k H)).obj (Rep.res H.subtype A)).rightOp
  let e' := F.mapHomotopyEquiv e
  let T := HomologicalComplex.homologyFunctor (ModuleCat k) (ComplexShape.up ℕ) n
  let γ : groupCohomology A n ≅ T.obj ((Rep.standardComplex k G).linearYonedaObj k A) :=
    groupCohomologyIso A n (Rep.standardResolution k G)
  let α :
      T.obj (ChainComplex.linearYonedaObj
        (((Rep.resFunctor H.subtype).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          (Rep.standardComplex k G)) k (Rep.res H.subtype A)) ≅
        groupCohomology (Rep.res H.subtype A) n :=
    HomologicalComplex.homologyUnop _ n ≪≫ (e'.toHomologyIso n).unop.symm ≪≫
      (HomologicalComplex.homologyUnop _ n).symm ≪≫
        (groupCohomologyIso (Rep.res H.subtype A) n (Rep.standardResolution k H)).symm
  have hrc' : T.map r ≫ T.map c = H.index • 𝟙 _ := by
    rw [← T.map_comp, hrc, T.map_nsmul, T.map_id]
  let R := γ.hom ≫ T.map r ≫ α.hom
  let C := α.inv ≫ T.map c ≫ γ.inv
  have hRC : R ≫ C = H.index • 𝟙 (groupCohomology A n) := by
    change (γ.hom ≫ T.map r ≫ α.hom) ≫ (α.inv ≫ T.map c ≫ γ.inv) = _
    calc
      _ = γ.hom ≫ (T.map r ≫ T.map c) ≫ γ.inv := by
        simp only [Category.assoc, Iso.hom_inv_id_assoc]
      _ = H.index • 𝟙 (groupCohomology A n) := by
        rw [hrc']
        simp only [Preadditive.comp_nsmul, Preadditive.nsmul_comp, Category.id_comp,
          Iso.hom_inv_id]
  refine ⟨R.hom, C.hom, fun x => ?_⟩
  exact congrArg (fun f : groupCohomology A n ⟶ groupCohomology A n => f.hom x) hRC

end Submission

theorem Rep.isZero_tateCohomology_of_forall_sylow {k G : Type u} [CommRing k] [Group G] [Fintype G]
    (A : Rep.{u} k G) (q : ℤ)
    (h : ∀ (p : ℕ) [Fact p.Prime] (P : Sylow p G) [Fintype (P : Subgroup G)],
      CategoryTheory.Limits.IsZero ((Rep.res (P : Subgroup G).subtype A).tateCohomology q)) :
    CategoryTheory.Limits.IsZero (A.tateCohomology q) := by
  sorry


theorem Rep.isZero_tateCohomology_of_forall_sylow {k G : Type u} [CommRing k] [Group G] [Fintype G]
    (A : Rep.{u} k G) (q : ℤ)
    (h : ∀ (p : ℕ) [Fact p.Prime] (P : Sylow p G) [Fintype (P : Subgroup G)],
      CategoryTheory.Limits.IsZero ((Rep.res (P : Subgroup G).subtype A).tateCohomology q)) :
    CategoryTheory.Limits.IsZero (A.tateCohomology q) := by
  sorry

set_option maxHeartbeats 4000000
set_option warningAsError true

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

namespace Submission

/-- The subgroup coefficient in a right transversal containing `1` gives an equivariant retraction.
`Subgroup.exists_isComplement_right` supplies the normalized transversal, and
`Subgroup.IsComplement.equiv` records the unique factorization into subgroup and transversal parts.
`Subgroup.IsComplement.equiv_mul_left` gives equivariance, and
`Subgroup.IsComplement.equiv_fst_eq_self_of_mem_of_one_mem` gives normalization.
All four APIs are from
`Mathlib/GroupTheory/Complement.lean` at pinned mathlib commit
`db584cd6d46c92f209a44c0f1c829460d327499d`. -/
theorem p04_rsh_82a013d1d0_equivariant_retraction {G : Type*} [Group G] (H : Subgroup G) :
    ∃ r : G → H, (∀ (h : H) (g : G), r ((h : G) * g) = h * r g) ∧
      ∀ h : H, r (h : G) = h := by

namespace Submission

/-- The subgroup coefficient in a right transversal containing `1` gives an equivariant retraction.
`Subgroup.exists_isComplement_right` supplies the normalized transversal, and
`Subgroup.IsComplement.equiv` records the unique factorization into subgroup and transversal parts.
`Subgroup.IsComplement.equiv_mul_left` gives equivariance, and
`Subgroup.IsComplement.equiv_fst_eq_self_of_mem_of_one_mem` gives normalization.
All four APIs are from
`Mathlib/GroupTheory/Complement.lean` at pinned mathlib commit
`db584cd6d46c92f209a44c0f1c829460d327499d`. -/
theorem p04_rsh_82a013d1d0_equivariant_retraction {G : Type*} [Group G] (H : Subgroup G) :
    ∃ r : G → H, (∀ (h : H) (g : G), r ((h : G) * g) = h * r g) ∧
      ∀ h : H, r (h : G) = h := by
  obtain ⟨T, hT, h1⟩ := H.exists_isComplement_right (1 : G)
  refine ⟨fun g => (hT.equiv g).1, ?_, ?_⟩
  · intro h g
    exact congrArg Prod.fst (hT.equiv_mul_left h g)
  · intro h
    exact hT.equiv_fst_eq_self_of_mem_of_one_mem h1 h.property

end Submission

namespace Submission

/-- The signed prism assignment extends to morphisms of the restricted standard complex.

The free-module extension uses `Finsupp.lift` and `MonoidAlgebra.coeffLinearEquiv`, as in
`Rep.standardComplex.d`. Equivariance is checked on generators using
`Representation.ofMulAction_single` and `Fin.insertNth_eq_iff`. -/
theorem p04_prism_a8325b9888_equivariant_components :
    ∀ {k G : Type _} [CommRing k] [Group G] (H : Subgroup G) (u v : G → G),
      (∀ (h : H) (g : G), u ((h : G) * g) = (h : G) * u g) →
      (∀ (h : H) (g : G), v ((h : G) * g) = (h : G) * v g) →
      let P : ∀ n : ℕ, (Fin (n + 1) → G) → MonoidAlgebra k (Fin (n + 2) → G) :=
        fun n c => ∑ j : Fin (n + 1),
          MonoidAlgebra.single (Fin.insertNth j.castSucc (u (c j))
            (fun i : Fin (n + 1) => if i < j then u (c i) else v (c i)))
            ((-1 : k) ^ j.val)
      let C := ((Rep.resFunctor H.subtype).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (Rep.standardComplex k G)
      ∃ D : ∀ n : ℕ, C.X n ⟶ C.X (n + 1), ∀ (n : ℕ) (c : Fin (n + 1) → G),
        (D n).hom (MonoidAlgebra.single c (1 : k)) = P n c := by
  classical
  intro k G _ _ H u v hu hv P C
  let L (n : ℕ) : MonoidAlgebra k (Fin (n + 1) → G) →ₗ[k]
      MonoidAlgebra k (Fin (n + 2) → G) :=
    (Finsupp.lift _ k _ (P n)) ∘ₗ (MonoidAlgebra.coeffLinearEquiv k).toLinearMap
  have hL (n : ℕ) (c : Fin (n + 1) → G) :
      L n (MonoidAlgebra.single c 1) = P n c := by
    simp [L]
  have hP (n : ℕ) (h : H) (c : Fin (n + 1) → G) :
      P n ((h : G) • c) =
        Representation.ofMulAction k G (Fin (n + 2) → G) (h : G) (P n c) := by
    simp only [P, map_sum, Representation.ofMulAction_single]
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    apply Fin.insertNth_eq_iff.mpr
    constructor
    · simpa using hu h (c j)
    · funext i
      simp only [Fin.removeNth, Pi.smul_apply, smul_eq_mul, Fin.insertNth_apply_succAbove]
      split_ifs with hij
      · exact hu h (c i)
      · exact hv h (c i)
  let D (n : ℕ) : C.X n ⟶ C.X (n + 1) := Rep.ofHom
    { toLinearMap := L n
      isIntertwining' := fun h => by
        refine MonoidAlgebra.lhom_ext' fun (c : Fin (n + 1) → G) => LinearMap.ext_ring ?_
        change L n (Representation.ofMulAction k G (Fin (n + 1) → G) (h : G)
          (MonoidAlgebra.single c 1)) =
            Representation.ofMulAction k G (Fin (n + 2) → G) (h : G)
              (L n (MonoidAlgebra.single c 1))
        rw [Representation.ofMulAction_single, hL, hL]
        exact hP n h c }
  exact ⟨D, hL⟩

end Submission

set_option maxHeartbeats 4000000
set_option warningAsError true

namespace Submission

/-- Pair noncentral prism faces with the signed prisms of the boundary.

The inverse pairing sends a boundary index `(b, t)` to `(t + 1, b)` when `b ≤ t`,
and to `(t, b + 1)` otherwise. The paired tuples agree and the exponents differ by one.
-/
theorem p04_pb_60221840b0_noncentral_cancellation
    {k X : Type _} [CommRing k] (u v : X → X) (n : ℕ) (c : Fin (n + 2) → X) :
    let Q : ∀ m : ℕ, (Fin (m + 1) → X) → Fin (m + 1) → (Fin (m + 2) → X) :=
      fun m d j => Fin.insertNth j.castSucc (u (d j))
        (fun i : Fin (m + 1) => if i < j then u (d i) else v (d i))
    (∑ j : Fin (n + 2), ∑ a : Fin (n + 3) with a.val < j.val ∨ j.val + 1 < a.val,
      MonoidAlgebra.single (Q (n + 1) c j ∘ a.succAbove) ((-1 : k) ^ (j.val + a.val))) +
    (∑ b : Fin (n + 2), ∑ t : Fin (n + 1),
      MonoidAlgebra.single (Q n (c ∘ b.succAbove) t) ((-1 : k) ^ (b.val + t.val))) = 0 := by
  classical
  intro Q
  -- Evaluate the inserted tuple on either side of its transition.
  have eval (m : ℕ) (d : Fin (m + 1) → X) (j : Fin (m + 1)) (s : Fin (m + 2)) :
      Q m d j s = if h : s.val ≤ j.val then u (d ⟨s.val, by omega⟩)
        else v (d ⟨s.val - 1, by omega⟩) := by
    dsimp only [Q]
    split_ifs with h
    · by_cases he : s = j.castSucc
      · subst s
        simp
      · have hs : s < j.castSucc := by
          simp only [Fin.lt_def, Fin.val_castSucc]
          have := Fin.ext_iff.not.mp he
          simp only [Fin.val_castSucc] at this
          omega
        rw [Fin.insertNth_apply_below hs]
        simp only [Fin.lt_def, Fin.coe_castPred, if_pos (show s.val < j.val by exact hs)]
        simp
        congr 2
    · have hs : j.castSucc < s := by
        simpa only [Fin.lt_def, Fin.val_castSucc] using Nat.lt_of_not_ge h
      rw [Fin.insertNth_apply_above hs]
      simp only [Fin.lt_def, Fin.val_pred, if_neg (show ¬ s.val - 1 < j.val by omega)]
      simp
      congr 2
  -- Deleting before or after the transition gives the corresponding smaller prism.
  have before (b : Fin (n + 2)) (t : Fin (n + 1)) (h : b.val ≤ t.val) :
      Q (n + 1) c t.succ ∘ b.castSucc.succAbove = Q n (c ∘ b.succAbove) t := by
    funext s
    by_cases hsb : s.val < b.val <;> by_cases hst : s.val ≤ t.val
    all_goals simp (disch := omega) only [Function.comp_apply, eval, Fin.succAbove,
      Fin.lt_def, Fin.val_castSucc, Fin.val_succ, if_pos, if_neg, dif_pos, dif_neg]
    all_goals first | omega | (congr 2 <;> apply Fin.ext <;> simp <;> omega)
  have after (b : Fin (n + 2)) (t : Fin (n + 1)) (h : t.val < b.val) :
      Q (n + 1) c t.castSucc ∘ b.succ.succAbove = Q n (c ∘ b.succAbove) t := by
    funext s
    by_cases hsb : s.val < b.val + 1 <;> by_cases hst : s.val ≤ t.val
    all_goals simp (disch := omega) only [Function.comp_apply, eval, Fin.succAbove,
      Fin.lt_def, Fin.val_castSucc, Fin.val_succ, if_pos, if_neg, dif_pos, dif_neg]
    all_goals first | omega | (congr 2 <;> apply Fin.ext <;> simp <;> omega)
  -- The inverse pairing sends (b, t) to (t + 1, b) or (t, b + 1).
  let I := (Finset.univ : Finset (Fin (n + 2) × Fin (n + 3))).filter
    (fun p => p.2.val < p.1.val ∨ p.1.val + 1 < p.2.val)
  let pair (p : Fin (n + 2) × Fin (n + 1)) : Fin (n + 2) × Fin (n + 3) :=
    if p.1.val ≤ p.2.val then (p.2.succ, p.1.castSucc) else (p.2.castSucc, p.1.succ)
  have reindex :
      (∑ p : Fin (n + 2) × Fin (n + 1),
        -MonoidAlgebra.single (Q n (c ∘ p.1.succAbove) p.2)
          ((-1 : k) ^ (p.1.val + p.2.val))) =
      ∑ p ∈ I, MonoidAlgebra.single (Q (n + 1) c p.1 ∘ p.2.succAbove)
        ((-1 : k) ^ (p.1.val + p.2.val)) := by
    apply Finset.sum_bij (fun p _ => pair p)
    · intro p _
      simp only [I, Finset.mem_filter, Finset.mem_univ, true_and]
      dsimp only [pair]
      split_ifs <;> simp only [Fin.val_succ, Fin.val_castSucc] <;> omega
    · intro p _ q _ hpq
      have h₁ := congrArg (fun r => r.1.val) hpq
      have h₂ := congrArg (fun r => r.2.val) hpq
      dsimp only [pair] at h₁ h₂
      split_ifs at h₁ h₂ <;> simp only [Fin.val_succ, Fin.val_castSucc] at *
      all_goals apply Prod.ext <;> apply Fin.ext <;> omega
    · rintro ⟨j, a⟩ hp
      have hp : a.val < j.val ∨ j.val + 1 < a.val := by simpa [I] using hp
      rcases hp with h | h
      · refine ⟨(⟨a.val, by omega⟩, ⟨j.val - 1, by omega⟩), Finset.mem_univ _, ?_⟩
        dsimp only [pair]
        rw [if_pos (by omega)]
        apply Prod.ext <;> apply Fin.ext <;> simp
        omega
      · refine ⟨(⟨a.val - 1, by omega⟩, ⟨j.val, by omega⟩), Finset.mem_univ _, ?_⟩
        dsimp only [pair]
        rw [if_neg (by omega)]
        apply Prod.ext <;> apply Fin.ext <;> simp
        omega
    -- Corresponding exponents differ by one.
    · rintro ⟨b, t⟩ _
      dsimp only [pair]
      split_ifs with h
      · rw [before b t h]
        simp only [Fin.val_succ, Fin.val_castSucc]
        rw [show t.val + 1 + b.val = (b.val + t.val) + 1 by omega, pow_succ]
        simp
      · rw [after b t (by omega)]
        simp only [Fin.val_succ, Fin.val_castSucc]
        rw [show t.val + (b.val + 1) = (b.val + t.val) + 1 by omega, pow_succ]
        simp
  simp only [I, Finset.sum_filter, Fintype.sum_prod_type, Finset.sum_neg_distrib] at reindex
  simp only [Finset.sum_filter]
  rw [← reindex]
  exact neg_add_cancel _

end Submission

namespace Submission

/-- The two central faces of each inserted tuple telescope to the endpoint tuples. -/
theorem p04_pb_60221840b0_central_telescoping :
    ∀ {k X : Type _} [CommRing k] (u v : X → X) (m : ℕ) (c : Fin (m + 1) → X),
      let Q : Fin (m + 1) → (Fin (m + 2) → X) := fun j =>
        Fin.insertNth j.castSucc (u (c j))
          (fun i : Fin (m + 1) => if i < j then u (c i) else v (c i))
      (∑ j : Fin (m + 1),
        (MonoidAlgebra.single (Q j ∘ j.castSucc.succAbove) (1 : k) -
          MonoidAlgebra.single (Q j ∘ j.succ.succAbove) (1 : k))) =
        MonoidAlgebra.single (v ∘ c) (1 : k) -
          MonoidAlgebra.single (u ∘ c) (1 : k) := by
  intro k X _ u v m c Q
  classical
  -- Moving the transition one position accounts for the two central deletions.
  let T : ℕ → (Fin (m + 1) → X) := fun l i =>
    if i.val < l then u (c i) else v (c i)
  have hleft (j : Fin (m + 1)) : Q j ∘ j.castSucc.succAbove = T j.val := by
    simpa only [Q, T, Fin.lt_def] using
      Fin.insertNth_comp_succAbove j.castSucc (u (c j))
        (fun i : Fin (m + 1) => if i < j then u (c i) else v (c i))
  have hright (j : Fin (m + 1)) : Q j ∘ j.succ.succAbove = T (j.val + 1) := by
    funext i
    change Fin.insertNth (α := fun _ => X) j.castSucc (u (c j))
      (fun i : Fin (m + 1) => if i < j then u (c i) else v (c i))
      (j.succ.succAbove i) = if i.val < j.val + 1 then u (c i) else v (c i)
    rcases lt_trichotomy i j with hij | rfl | hji
    · rw [Fin.succAbove_succ_of_le _ _ hij.le,
        ← Fin.succAbove_castSucc_of_lt _ _ hij, Fin.insertNth_apply_succAbove]
      simp [hij, show i.val < j.val + 1 by omega]
    · simp
    · rw [Fin.succAbove_succ_of_lt _ _ hji,
        ← Fin.succAbove_castSucc_of_le _ _ hji.le, Fin.insertNth_apply_succAbove]
      simp [not_lt_of_gt hji, show ¬i.val < j.val + 1 by omega]
  have hzero : T 0 = v ∘ c := by
    funext i
    simp [T]
  have hlast : T (m + 1) = u ∘ c := by
    funext i
    simp [T, i.is_lt]
  -- The adjacent differences cancel, leaving the all-v and all-u tuples.
  simp_rw [hleft, hright]
  rw [Fin.sum_univ_eq_sum_range (fun l =>
    MonoidAlgebra.single (T l) (1 : k) - MonoidAlgebra.single (T (l + 1)) (1 : k)),
    Finset.sum_range_sub', hzero, hlast]

end Submission

namespace Submission

/-- The alternating prism has boundary equal to its two endpoints. -/
theorem p04_prism_a8325b9888_boundary_identity :
    ∀ {k X : Type _} [CommRing k] (u v : X → X),
    let P : ∀ n : ℕ, (Fin (n + 1) → X) → MonoidAlgebra k (Fin (n + 2) → X) :=
      fun n c => ∑ j : Fin (n + 1),
        MonoidAlgebra.single
          (Fin.insertNth j.castSucc (u (c j))
            (fun i : Fin (n + 1) => if i < j then u (c i) else v (c i)))
          ((-1 : k) ^ j.val)
    (∀ c : Fin 1 → X, Rep.standardComplex.d k X 1 (P 0 c) =
      MonoidAlgebra.single (v ∘ c) (1 : k) - MonoidAlgebra.single (u ∘ c) (1 : k)) ∧
    ∀ (n : ℕ) (c : Fin (n + 2) → X),
      Rep.standardComplex.d k X (n + 2) (P (n + 1) c) +
          ∑ b : Fin (n + 2), ((-1 : k) ^ b.val) • P n (c ∘ b.succAbove) =
        MonoidAlgebra.single (v ∘ c) (1 : k) -
          MonoidAlgebra.single (u ∘ c) (1 : k) := by
  classical
  intro k X _ u v P
  let Q : ∀ m : ℕ, (Fin (m + 1) → X) → Fin (m + 1) → (Fin (m + 2) → X) :=
    fun m c j => Fin.insertNth j.castSucc (u (c j))
      (fun i : Fin (m + 1) => if i < j then u (c i) else v (c i))
  -- Separate the two central faces from all other faces, retaining their signs.
  have split_faces (m : ℕ) (c : Fin (m + 1) → X) (j : Fin (m + 1)) :
      (∑ a : Fin (m + 2),
        MonoidAlgebra.single (Q m c j ∘ a.succAbove) ((-1 : k) ^ (j.val + a.val))) =
      (∑ a : Fin (m + 2) with a.val < j.val ∨ j.val + 1 < a.val,
        MonoidAlgebra.single (Q m c j ∘ a.succAbove) ((-1 : k) ^ (j.val + a.val))) +
      (MonoidAlgebra.single (Q m c j ∘ j.castSucc.succAbove) (1 : k) -
        MonoidAlgebra.single (Q m c j ∘ j.succ.succAbove) (1 : k)) := by
    have central :
        (Finset.univ.filter fun a : Fin (m + 2) =>
          ¬ (a.val < j.val ∨ j.val + 1 < a.val)) = {j.castSucc, j.succ} := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, Fin.val_castSucc,
        Fin.val_succ]
      omega
    have distinct : j.castSucc ≠ j.succ := by
      intro h
      have := congrArg Fin.val h
      simp only [Fin.val_castSucc, Fin.val_succ] at this
      omega
    have even_sign : (-1 : k) ^ (j.val + j.val) = 1 := by
      rw [← two_mul, pow_mul]
      simp
    have odd_sign : (-1 : k) ^ (j.val + (j.val + 1)) = -1 := by
      rw [← Nat.add_assoc, pow_succ, even_sign, one_mul]
    rw [← Finset.sum_filter_add_sum_filter_not
      (s := Finset.univ) (p := fun a : Fin (m + 2) =>
        a.val < j.val ∨ j.val + 1 < a.val)]
    rw [central, Finset.sum_pair distinct]
    simp only [Fin.val_castSucc, Fin.val_succ, even_sign, odd_sign,
      MonoidAlgebra.single_neg, sub_eq_add_neg]
  have boundary (m : ℕ) (c : Fin (m + 1) → X) :
      Rep.standardComplex.d k X (m + 1) (P m c) =
      (∑ j : Fin (m + 1),
        ∑ a : Fin (m + 2) with a.val < j.val ∨ j.val + 1 < a.val,
          MonoidAlgebra.single (Q m c j ∘ a.succAbove) ((-1 : k) ^ (j.val + a.val))) +
      (MonoidAlgebra.single (v ∘ c) (1 : k) -
        MonoidAlgebra.single (u ∘ c) (1 : k)) := by
    change Rep.standardComplex.d k X (m + 1)
      (∑ j : Fin (m + 1), MonoidAlgebra.single (Q m c j) ((-1 : k) ^ j.val)) = _
    simp only [map_sum, Rep.standardComplex.d_single, ← pow_add]
    simp_rw [split_faces]
    rw [Finset.sum_add_distrib]
    congr 1
    exact Submission.p04_pb_60221840b0_central_telescoping u v m c
  constructor
  · intro c
    rw [boundary]
    have no_noncentral (j : Fin 1) (a : Fin 2) :
        ¬ (a.val < j.val ∨ j.val + 1 < a.val) := by
      have hj := j.isLt
      have ha := a.isLt
      omega
    simp only [no_noncentral, Finset.filter_false, Finset.sum_empty,
      Finset.sum_const_zero, zero_add]
  · intro n c
    have lower :
        (∑ b : Fin (n + 2), ((-1 : k) ^ b.val) • P n (c ∘ b.succAbove)) =
        ∑ b : Fin (n + 2), ∑ t : Fin (n + 1),
          MonoidAlgebra.single (Q n (c ∘ b.succAbove) t)
            ((-1 : k) ^ (b.val + t.val)) := by
      simp only [P, Q, Finset.smul_sum, MonoidAlgebra.smul_single, smul_eq_mul, pow_add]
    rw [boundary, lower, add_right_comm]
    have cancel := Submission.p04_pb_60221840b0_noncentral_cancellation (k := k) u v n c
    change _ + _ = 0 at cancel
    rw [cancel, zero_add]

end Submission

set_option maxHeartbeats 4000000

namespace Submission

/-- Pair noncentral prism faces with the signed prisms of the boundary.

The inverse pairing sends a boundary index `(b, t)` to `(t + 1, b)` when `b ≤ t`,
and to `(t, b + 1)` otherwise. The paired tuples agree and the exponents differ by one.
-/
theorem p04_pb_60221840b0_noncentral_cancellation
    {k X : Type _} [CommRing k] (u v : X → X) (n : ℕ) (c : Fin (n + 2) → X) :
    let Q : ∀ m : ℕ, (Fin (m + 1) → X) → Fin (m + 1) → (Fin (m + 2) → X) :=
      fun m d j => Fin.insertNth j.castSucc (u (d j))
        (fun i : Fin (m + 1) => if i < j then u (d i) else v (d i))
    (∑ j : Fin (n + 2), ∑ a : Fin (n + 3) with a.val < j.val ∨ j.val + 1 < a.val,
      MonoidAlgebra.single (Q (n + 1) c j ∘ a.succAbove) ((-1 : k) ^ (j.val + a.val))) +
    (∑ b : Fin (n + 2), ∑ t : Fin (n + 1),
      MonoidAlgebra.single (Q n (c ∘ b.succAbove) t) ((-1 : k) ^ (b.val + t.val))) = 0 := by
  classical
  intro Q
  -- Evaluate the inserted tuple on either side of its transition.
  have eval (m : ℕ) (d : Fin (m + 1) → X) (j : Fin (m + 1)) (s : Fin (m + 2)) :
      Q m d j s = if h : s.val ≤ j.val then u (d ⟨s.val, by omega⟩)
        else v (d ⟨s.val - 1, by omega⟩) := by
    dsimp only [Q]
    split_ifs with h
    · by_cases he : s = j.castSucc
      · subst s
        simp
      · have hs : s < j.castSucc := by
          simp only [Fin.lt_def, Fin.val_castSucc]
          have := Fin.ext_iff.not.mp he
          simp only [Fin.val_castSucc] at this
          omega
        rw [Fin.insertNth_apply_below hs]
        simp only [Fin.lt_def, Fin.coe_castPred, if_pos (show s.val < j.val by exact hs)]
        simp
        congr 2
    · have hs : j.castSucc < s := by
        simpa only [Fin.lt_def, Fin.val_castSucc] using Nat.lt_of_not_ge h
      rw [Fin.insertNth_apply_above hs]
      simp only [Fin.lt_def, Fin.val_pred, if_neg (show ¬ s.val - 1 < j.val by omega)]
      simp
      congr 2
  -- Deleting before or after the transition gives the corresponding smaller prism.
  have before (b : Fin (n + 2)) (t : Fin (n + 1)) (h : b.val ≤ t.val) :
      Q (n + 1) c t.succ ∘ b.castSucc.succAbove = Q n (c ∘ b.succAbove) t := by
    funext s
    by_cases hsb : s.val < b.val <;> by_cases hst : s.val ≤ t.val
    all_goals simp (disch := omega) only [Function.comp_apply, eval, Fin.succAbove,
      Fin.lt_def, Fin.val_castSucc, Fin.val_succ, if_pos, if_neg, dif_pos, dif_neg]
    all_goals first | omega | (congr 2 <;> apply Fin.ext <;> simp <;> omega)
  have after (b : Fin (n + 2)) (t : Fin (n + 1)) (h : t.val < b.val) :
      Q (n + 1) c t.castSucc ∘ b.succ.succAbove = Q n (c ∘ b.succAbove) t := by
    funext s
    by_cases hsb : s.val < b.val + 1 <;> by_cases hst : s.val ≤ t.val
    all_goals simp (disch := omega) only [Function.comp_apply, eval, Fin.succAbove,
      Fin.lt_def, Fin.val_castSucc, Fin.val_succ, if_pos, if_neg, dif_pos, dif_neg]
    all_goals first | omega | (congr 2 <;> apply Fin.ext <;> simp <;> omega)
  -- The inverse pairing sends (b, t) to (t + 1, b) or (t, b + 1).
  let I := (Finset.univ : Finset (Fin (n + 2) × Fin (n + 3))).filter
    (fun p => p.2.val < p.1.val ∨ p.1.val + 1 < p.2.val)
  let pair (p : Fin (n + 2) × Fin (n + 1)) : Fin (n + 2) × Fin (n + 3) :=
    if p.1.val ≤ p.2.val then (p.2.succ, p.1.castSucc) else (p.2.castSucc, p.1.succ)
  have reindex :
      (∑ p : Fin (n + 2) × Fin (n + 1),
        -MonoidAlgebra.single (Q n (c ∘ p.1.succAbove) p.2)
          ((-1 : k) ^ (p.1.val + p.2.val))) =
      ∑ p ∈ I, MonoidAlgebra.single (Q (n + 1) c p.1 ∘ p.2.succAbove)
        ((-1 : k) ^ (p.1.val + p.2.val)) := by
    apply Finset.sum_bij (fun p _ => pair p)
    · intro p _
      simp only [I, Finset.mem_filter, Finset.mem_univ, true_and]
      dsimp only [pair]
      split_ifs <;> simp only [Fin.val_succ, Fin.val_castSucc] <;> omega
    · intro p _ q _ hpq
      have h₁ := congrArg (fun r => r.1.val) hpq
      have h₂ := congrArg (fun r => r.2.val) hpq
      dsimp only [pair] at h₁ h₂
      split_ifs at h₁ h₂ <;> simp only [Fin.val_succ, Fin.val_castSucc] at *
      all_goals apply Prod.ext <;> apply Fin.ext <;> omega
    · rintro ⟨j, a⟩ hp
      have hp : a.val < j.val ∨ j.val + 1 < a.val := by simpa [I] using hp
      rcases hp with h | h
      · refine ⟨(⟨a.val, by omega⟩, ⟨j.val - 1, by omega⟩), Finset.mem_univ _, ?_⟩
        dsimp only [pair]
        rw [if_pos (by omega)]
        apply Prod.ext <;> apply Fin.ext <;> simp
        omega
      · refine ⟨(⟨a.val - 1, by omega⟩, ⟨j.val, by omega⟩), Finset.mem_univ _, ?_⟩
        dsimp only [pair]
        rw [if_neg (by omega)]
        apply Prod.ext <;> apply Fin.ext <;> simp
        omega
    -- Corresponding exponents differ by one.
    · rintro ⟨b, t⟩ _
      dsimp only [pair]
      split_ifs with h
      · rw [before b t h]
        simp only [Fin.val_succ, Fin.val_castSucc]
        rw [show t.val + 1 + b.val = (b.val + t.val) + 1 by omega, pow_succ]
        simp
      · rw [after b t (by omega)]
        simp only [Fin.val_succ, Fin.val_castSucc]
        rw [show t.val + (b.val + 1) = (b.val + t.val) + 1 by omega, pow_succ]
        simp
  simp only [I, Finset.sum_filter, Fintype.sum_prod_type, Finset.sum_neg_distrib] at reindex
  simp only [Finset.sum_filter]
  rw [← reindex]
  exact neg_add_cancel _

end Submission

namespace Submission

/-- The signed prism assignment extends to morphisms of the restricted standard complex.

The free-module extension uses `Finsupp.lift` and `MonoidAlgebra.coeffLinearEquiv`, as in
`Rep.standardComplex.d`. Equivariance is checked on generators using
`Representation.ofMulAction_single` and `Fin.insertNth_eq_iff`. -/
theorem p04_prism_a8325b9888_equivariant_components :
    ∀ {k G : Type _} [CommRing k] [Group G] (H : Subgroup G) (u v : G → G),
      (∀ (h : H) (g : G), u ((h : G) * g) = (h : G) * u g) →
      (∀ (h : H) (g : G), v ((h : G) * g) = (h : G) * v g) →
      let P : ∀ n : ℕ, (Fin (n + 1) → G) → MonoidAlgebra k (Fin (n + 2) → G) :=
        fun n c => ∑ j : Fin (n + 1),
          MonoidAlgebra.single (Fin.insertNth j.castSucc (u (c j))
            (fun i : Fin (n + 1) => if i < j then u (c i) else v (c i)))
            ((-1 : k) ^ j.val)
      let C := ((Rep.resFunctor H.subtype).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (Rep.standardComplex k G)
      ∃ D : ∀ n : ℕ, C.X n ⟶ C.X (n + 1), ∀ (n : ℕ) (c : Fin (n + 1) → G),
        (D n).hom (MonoidAlgebra.single c (1 : k)) = P n c := by
  classical
  intro k G _ _ H u v hu hv P C
  let L (n : ℕ) : MonoidAlgebra k (Fin (n + 1) → G) →ₗ[k]
      MonoidAlgebra k (Fin (n + 2) → G) :=
    (Finsupp.lift _ k _ (P n)) ∘ₗ (MonoidAlgebra.coeffLinearEquiv k).toLinearMap
  have hL (n : ℕ) (c : Fin (n + 1) → G) :
      L n (MonoidAlgebra.single c 1) = P n c := by
    simp [L]
  have hP (n : ℕ) (h : H) (c : Fin (n + 1) → G) :
      P n ((h : G) • c) =
        Representation.ofMulAction k G (Fin (n + 2) → G) (h : G) (P n c) := by
    simp only [P, map_sum, Representation.ofMulAction_single]
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    apply Fin.insertNth_eq_iff.mpr
    constructor
    · simpa using hu h (c j)
    · funext i
      simp only [Fin.removeNth, Pi.smul_apply, smul_eq_mul, Fin.insertNth_apply_succAbove]
      split_ifs with hij
      · exact hu h (c i)
      · exact hv h (c i)
  let D (n : ℕ) : C.X n ⟶ C.X (n + 1) := Rep.ofHom
    { toLinearMap := L n
      isIntertwining' := fun h => by
        refine MonoidAlgebra.lhom_ext' fun (c : Fin (n + 1) → G) => LinearMap.ext_ring ?_
        change L n (Representation.ofMulAction k G (Fin (n + 1) → G) (h : G)
          (MonoidAlgebra.single c 1)) =
            Representation.ofMulAction k G (Fin (n + 2) → G) (h : G)
              (L n (MonoidAlgebra.single c 1))
        rw [Representation.ofMulAction_single, hL, hL]
        exact hP n h c }
  exact ⟨D, hL⟩

end Submission

open CategoryTheory Rep Representation MonoidalCategory

namespace Submission

/-- Transfer and projection on tensor coinvariant homology have composite the subgroup index.

Transfer is the sum over right cosets, with each summand descended through representative
independence. Naturality gives chain maps, and the additive homology functor preserves their
index composite. The quotient of right cosets is used directly, so the construction does not
require a choice of transversal or normality of `H`.

The quotient and restriction APIs come from mathlib's `RepresentationTheory/Coinvariants.lean`
and `RepresentationTheory/Rep/Res.lean`; the complex and additive homology APIs come from
`RepresentationTheory/Homological/GroupHomology/Basic.lean` and
`Algebra/Homology/ShortComplex/HomologicalComplex.lean`, at the pinned revision
`db584cd6d46c92f209a44c0f1c829460d327499d`. Right-coset cardinality uses
`GroupTheory/Coset/Defs.lean` and `GroupTheory/Index.lean`; preservation of repeated addition
uses `CategoryTheory/Preadditive/AdditiveFunctor.lean` at the same revision. -/
theorem p04_ht_coinvariant_complex_transfer
    {k G : Type _} [CommRing k] [Group G] [Fintype G]
    (A : Rep k G) (H : Subgroup G) [Fintype H]
    (C : ChainComplex (Rep k G) ℕ) (n : ℕ) :
    ∃ T : (C.coinvariantsTensorObj A).homology n →ₗ[k]
      ((((Rep.resFunctor (k := k) H.subtype).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj C).coinvariantsTensorObj
          (Rep.res H.subtype A)).homology n,
    ∃ P : ((((Rep.resFunctor (k := k) H.subtype).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj C).coinvariantsTensorObj
          (Rep.res H.subtype A)).homology n →ₗ[k]
      (C.coinvariantsTensorObj A).homology n,
    ∀ x : (C.coinvariantsTensorObj A).homology n, P (T x) = H.index • x := by
  classical
  let Q := Quotient (QuotientGroup.rightRel H)
  let : Fintype Q := Fintype.ofFinite Q
  have cardQ : Fintype.card Q = H.index := by
    rw [H.index_eq_card, Nat.card_eq_fintype_card]
    exact Fintype.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel H)
  -- The summand depends only on the right coset of the representative.
  have representative_independent (W : Rep k G) (s t : G)
      (h : QuotientGroup.rightRel H s t) :
      Coinvariants.mk (W.ρ.comp H.subtype) ∘ₗ W.ρ s =
        Coinvariants.mk (W.ρ.comp H.subtype) ∘ₗ W.ρ t := by
    ext v
    have e := Coinvariants.mk_self_apply (W.ρ.comp H.subtype)
      (⟨t * s⁻¹, QuotientGroup.rightRel_apply.mp h⟩ : H) (W.ρ s v)
    simpa [← Module.End.mul_apply, ← map_mul] using e.symm
  let summand (W : Rep k G) : Q → (W →ₗ[k] Coinvariants (W.ρ.comp H.subtype)) :=
    Quotient.lift (fun s => Coinvariants.mk (W.ρ.comp H.subtype) ∘ₗ W.ρ s)
      (representative_independent W)
  let rightMul (g : G) : Q ≃ Q :=
    { toFun := Quotient.map (fun s => s * g) (by
        intro s t h
        apply QuotientGroup.rightRel_apply.mpr
        simpa using QuotientGroup.rightRel_apply.mp h)
      invFun := Quotient.map (fun s => s * g⁻¹) (by
        intro s t h
        apply QuotientGroup.rightRel_apply.mpr
        simpa using QuotientGroup.rightRel_apply.mp h)
      left_inv := by intro q; induction q using Quotient.inductionOn; simp
      right_inv := by intro q; induction q using Quotient.inductionOn; simp }
  have summand_mul (W : Rep k G) (g : G) (q : Q) :
      summand W q ∘ₗ W.ρ g = summand W (rightMul g q) := by
    induction q using Quotient.inductionOn with | h s =>
      dsimp [summand, rightMul]
      rw [map_mul]
      rfl
  let transfer (W : Rep k G) : W.ρ.Coinvariants →ₗ[k]
      Coinvariants (W.ρ.comp H.subtype) :=
    Coinvariants.lift W.ρ (∑ q : Q, summand W q) (by
      intro g
      ext v
      simp only [LinearMap.comp_apply, LinearMap.sum_apply]
      have term (q : Q) : summand W q (W.ρ g v) = summand W (rightMul g q) v :=
        congrArg (fun f => f v) (summand_mul W g q)
      simp_rw [term]
      exact (rightMul g).sum_comp (fun q => summand W q v))
  let projection (W : Rep k G) : Coinvariants (W.ρ.comp H.subtype) →ₗ[k]
      W.ρ.Coinvariants := Coinvariants.lift _ (Coinvariants.mk W.ρ) (by
        intro h
        ext v
        exact Coinvariants.mk_self_apply W.ρ (h : G) v)
  have projection_transfer (W : Rep k G) (x : W.ρ.Coinvariants) :
      projection W (transfer W x) = H.index • x := by
    induction x using Coinvariants.induction_on with | h v =>
      change projection W ((∑ q : Q, summand W q) v) = _
      simp only [LinearMap.sum_apply, map_sum]
      have term (q : Q) : projection W (summand W q v) = Coinvariants.mk W.ρ v := by
        induction q using Quotient.inductionOn with | h s =>
          exact Coinvariants.mk_self_apply W.ρ s v
      simp_rw [term]
      simp [cardQ]
  have transfer_natural {W V : Rep k G} (f : W ⟶ V) :
      Coinvariants.map _ _ (Rep.resMap H.subtype f).hom ∘ₗ transfer W =
        transfer V ∘ₗ Coinvariants.map _ _ f.hom := by
    apply Coinvariants.hom_ext
    ext v
    change Coinvariants.map _ _ (Rep.resMap H.subtype f).hom
      ((∑ q : Q, summand W q) v) = (∑ q : Q, summand V q) (f.hom v)
    simp only [LinearMap.sum_apply, map_sum]
    apply Finset.sum_congr rfl
    intro q _
    induction q using Quotient.inductionOn with | h s =>
      change Coinvariants.mk _ (f.hom (W.ρ s v)) = Coinvariants.mk _ (V.ρ s (f.hom v))
      rw [Rep.hom_comm_apply]
  have projection_natural {W V : Rep k G} (f : W ⟶ V) :
      Coinvariants.map _ _ f.hom ∘ₗ projection W =
        projection V ∘ₗ Coinvariants.map _ _ (Rep.resMap H.subtype f).hom := by
    apply Coinvariants.hom_ext
    rfl
  -- Restriction preserves the underlying tensor modules and their differentials definitionally.
  let D := C.coinvariantsTensorObj A
  let E := (((Rep.resFunctor (k := k) H.subtype).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj C).coinvariantsTensorObj (Rep.res H.subtype A)
  let τ : D ⟶ E :=
    { f := fun i => ModuleCat.ofHom (transfer (A ⊗ C.X i))
      comm' := by
        intro i j _
        apply ModuleCat.hom_ext
        exact transfer_natural (A ◁ C.d i j) }
  let π : E ⟶ D :=
    { f := fun i => ModuleCat.ofHom (projection (A ⊗ C.X i))
      comm' := by
        intro i j _
        apply ModuleCat.hom_ext
        exact projection_natural (A ◁ C.d i j) }
  have composite : τ ≫ π = H.index • 𝟙 D := by
    ext i x
    exact projection_transfer (A ⊗ C.X i) x
  -- Functoriality and additivity pass the degreewise identity to every homology degree.
  let F := HomologicalComplex.homologyFunctor (ModuleCat k) (ComplexShape.down ℕ) n
  refine ⟨(F.map τ).hom, (F.map π).hom, ?_⟩
  intro x
  have e : F.map τ ≫ F.map π = H.index • 𝟙 (F.obj D) := by
    rw [← F.map_comp, composite, F.map_nsmul, F.map_id]
  exact congrArg (fun f => f.hom x) e

end Submission

namespace Submission

open CategoryTheory

set_option warningAsError true in
/-- Transfer and projection on group homology have composite multiplication by the index.
The accepted complex transfer is transported through the accepted restricted comparison
and `groupHomologyIso` for `Rep.standardResolution`. These upstream declarations are in
`Mathlib/RepresentationTheory/Homological/GroupHomology/Basic.lean` and
`Mathlib/RepresentationTheory/Homological/Resolution.lean` at the pinned revision
`db584cd6d46c92f209a44c0f1c829460d327499d`. -/
theorem p04_tia_homology_transfer {k G : Type _} [CommRing k] [Group G] [Fintype G]
    (A : Rep k G) (H : Subgroup G) [Fintype H] (n : ℕ) :
    ∃ T : groupHomology A n →ₗ[k] groupHomology (Rep.res H.subtype A) n,
      ∃ P : groupHomology (Rep.res H.subtype A) n →ₗ[k] groupHomology A n,
        ∀ x : groupHomology A n, P (T x) = H.index • x := by
  classical
  obtain ⟨T, P, hPT⟩ :=
    Submission.p04_ht_coinvariant_complex_transfer A H (Rep.standardComplex k G) n
  obtain ⟨α⟩ := Submission.p04_ht_restricted_standard_comparison A H n
  let γ : groupHomology A n ≃ₗ[k]
      ((Rep.standardComplex k G).coinvariantsTensorObj A).homology n :=
    (groupHomologyIso A n (Rep.standardResolution k G)).toLinearEquiv
  refine ⟨α.toLinearMap.comp (T.comp γ.toLinearMap),
    γ.symm.toLinearMap.comp (P.comp α.symm.toLinearMap), ?_⟩
  intro x
  change γ.symm (P (α.symm (α (T (γ x))))) = H.index • x
  rw [α.symm_apply_apply, hPT, map_nsmul, γ.symm_apply_apply]

end Submission

namespace Submission

theorem p04_tia_tate_zero_transfer :
    ∀ {k G : Type _} [CommRing k] [Group G] [Fintype G]
      (A : Rep k G) (H : Subgroup G) [Fintype H],
      ∃ R : A.tateH0 →ₗ[k] (Rep.res H.subtype A).tateH0,
      ∃ C : (Rep.res H.subtype A).tateH0 →ₗ[k] A.tateH0,
      ∀ x : A.tateH0, C (R x) = H.index • x := by
  intro k G _ _ _ A H _
  obtain ⟨j, hj, hj_range⟩ :=
    Submission.p04_tz91_invariant_restriction_norm_range A H
  obtain ⟨c, hc_norm, hc_index⟩ :=
    Submission.p04_tz91_invariant_transfer_norm_index A H
  have hc_range : LinearMap.range (Rep.res H.subtype A).ρ.normBar ≤
      (LinearMap.range A.ρ.normBar).comap c := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨v, rfl⟩ :=
      Representation.Coinvariants.mk_surjective (Rep.res H.subtype A).ρ y
    exact ⟨Representation.Coinvariants.mk A.ρ v, by
      simpa only [Representation.normBar_mk] using (hc_norm v).symm⟩
  refine ⟨Submodule.mapQ _ _ j hj_range, Submodule.mapQ _ _ c hc_range, ?_⟩
  intro x
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  simp only [Submodule.mapQ_apply, hc_index a (j a) (hj a)]
  exact map_nsmul (LinearMap.range A.ρ.normBar).mkQ H.index a
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

end Submission

namespace Submission

/-- The two central faces of each inserted tuple telescope to the endpoint tuples. -/
theorem p04_pb_60221840b0_central_telescoping :
    ∀ {k X : Type _} [CommRing k] (u v : X → X) (m : ℕ) (c : Fin (m + 1) → X),
      let Q : Fin (m + 1) → (Fin (m + 2) → X) := fun j =>
        Fin.insertNth j.castSucc (u (c j))
          (fun i : Fin (m + 1) => if i < j then u (c i) else v (c i))
      (∑ j : Fin (m + 1),
        (MonoidAlgebra.single (Q j ∘ j.castSucc.succAbove) (1 : k) -
          MonoidAlgebra.single (Q j ∘ j.succ.succAbove) (1 : k))) =
        MonoidAlgebra.single (v ∘ c) (1 : k) -
          MonoidAlgebra.single (u ∘ c) (1 : k) := by
  intro k X _ u v m c Q
  classical
  -- Moving the transition one position accounts for the two central deletions.
  let T : ℕ → (Fin (m + 1) → X) := fun l i =>
    if i.val < l then u (c i) else v (c i)
  have hleft (j : Fin (m + 1)) : Q j ∘ j.castSucc.succAbove = T j.val := by
    simpa only [Q, T, Fin.lt_def] using
      Fin.insertNth_comp_succAbove j.castSucc (u (c j))
        (fun i : Fin (m + 1) => if i < j then u (c i) else v (c i))
  have hright (j : Fin (m + 1)) : Q j ∘ j.succ.succAbove = T (j.val + 1) := by
    funext i
    change Fin.insertNth (α := fun _ => X) j.castSucc (u (c j))
      (fun i : Fin (m + 1) => if i < j then u (c i) else v (c i))
      (j.succ.succAbove i) = if i.val < j.val + 1 then u (c i) else v (c i)
    rcases lt_trichotomy i j with hij | rfl | hji
    · rw [Fin.succAbove_succ_of_le _ _ hij.le,
        ← Fin.succAbove_castSucc_of_lt _ _ hij, Fin.insertNth_apply_succAbove]
      simp [hij, show i.val < j.val + 1 by omega]
    · simp
    · rw [Fin.succAbove_succ_of_lt _ _ hji,
        ← Fin.succAbove_castSucc_of_le _ _ hji.le, Fin.insertNth_apply_succAbove]
      simp [not_lt_of_gt hji, show ¬i.val < j.val + 1 by omega]
  have hzero : T 0 = v ∘ c := by
    funext i
    simp [T]
  have hlast : T (m + 1) = u ∘ c := by
    funext i
    simp [T, i.is_lt]
  -- The adjacent differences cancel, leaving the all-v and all-u tuples.
  simp_rw [hleft, hright]
  rw [Fin.sum_univ_eq_sum_range (fun l =>
    MonoidAlgebra.single (T l) (1 : k) - MonoidAlgebra.single (T (l + 1)) (1 : k)),
    Finset.sum_range_sub', hzero, hlast]

end Submission

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
    exact S.property.equiv_snd_eq_self_of_mem_of_one_mem H.one_mem s.property
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

set_option warningAsError true in
/-- Restriction and coset averaging on the equivariant Hom cochain complex. -/
theorem Submission.p04_tia_coh_hom_complex_transfer :
    ∀ {k G : Type _} [CommRing k] [Group G] [Fintype G]
      (A : Rep k G) (H : Subgroup G) [Fintype H]
      (X : ChainComplex (Rep k G) ℕ),
      ∃ R : Quiver.Hom (X.linearYonedaObj k A)
        (ChainComplex.linearYonedaObj
          (((Rep.resFunctor H.subtype).mapHomologicalComplex (ComplexShape.down ℕ)).obj X)
          k (Rep.res H.subtype A)),
      ∃ C : Quiver.Hom
        (ChainComplex.linearYonedaObj
          (((Rep.resFunctor H.subtype).mapHomologicalComplex (ComplexShape.down ℕ)).obj X)
          k (Rep.res H.subtype A))
        (X.linearYonedaObj k A),
      CategoryTheory.CategoryStruct.comp R C =
        H.index • CategoryTheory.CategoryStruct.id (X.linearYonedaObj k A) := by
  intro k G _ _ _ A H _ X
  classical
  let : Fintype (G ⧸ H) := Fintype.ofFinite _
  choose C hC using fun (B : Rep k G) =>
    Submission.p04_hct139_coset_average_exists A B H
  obtain ⟨hC_natural, hC_index⟩ :=
    Submission.p04_hct139_coset_average_laws A H C hC
  let U := X.linearYonedaObj k A
  let V := ChainComplex.linearYonedaObj
    (((Rep.resFunctor H.subtype).mapHomologicalComplex (ComplexShape.down ℕ)).obj X)
    k (Rep.res H.subtype A)
  let R : U ⟶ V :=
    { f := fun _ => ModuleCat.ofHom ((Rep.resFunctor H.subtype).mapLinearMap k)
      comm' := by
        intro i j _
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro F
        change (Rep.resFunctor H.subtype).map (X.d j i) ≫
            (Rep.resFunctor H.subtype).map F =
          (Rep.resFunctor H.subtype).map (X.d j i ≫ F)
        exact ((Rep.resFunctor H.subtype).map_comp _ _).symm }
  let T : V ⟶ U :=
    { f := fun i => ModuleCat.ofHom (C (X.X i))
      comm' := by
        intro i j _
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro F
        change X.d j i ≫ C (X.X i) F =
          C (X.X j) ((Rep.resFunctor H.subtype).map (X.d j i) ≫ F)
        exact (hC_natural (X.X i) (X.X j) (X.d j i) F).symm }
  refine ⟨R, T, ?_⟩
  apply HomologicalComplex.hom_ext
  intro i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro F
  change C (X.X i) ((Rep.resFunctor H.subtype).map F) = H.index • F
  exact hC_index (X.X i) F

namespace Submission

/-- The alternating prism has boundary equal to its two endpoints. -/
theorem p04_prism_a8325b9888_boundary_identity :
    ∀ {k X : Type _} [CommRing k] (u v : X → X),
    let P : ∀ n : ℕ, (Fin (n + 1) → X) → MonoidAlgebra k (Fin (n + 2) → X) :=
      fun n c => ∑ j : Fin (n + 1),
        MonoidAlgebra.single
          (Fin.insertNth j.castSucc (u (c j))
            (fun i : Fin (n + 1) => if i < j then u (c i) else v (c i)))
          ((-1 : k) ^ j.val)
    (∀ c : Fin 1 → X, Rep.standardComplex.d k X 1 (P 0 c) =
      MonoidAlgebra.single (v ∘ c) (1 : k) - MonoidAlgebra.single (u ∘ c) (1 : k)) ∧
    ∀ (n : ℕ) (c : Fin (n + 2) → X),
      Rep.standardComplex.d k X (n + 2) (P (n + 1) c) +
          ∑ b : Fin (n + 2), ((-1 : k) ^ b.val) • P n (c ∘ b.succAbove) =
        MonoidAlgebra.single (v ∘ c) (1 : k) -
          MonoidAlgebra.single (u ∘ c) (1 : k) := by
  classical
  intro k X _ u v P
  let Q : ∀ m : ℕ, (Fin (m + 1) → X) → Fin (m + 1) → (Fin (m + 2) → X) :=
    fun m c j => Fin.insertNth j.castSucc (u (c j))
      (fun i : Fin (m + 1) => if i < j then u (c i) else v (c i))
  -- Separate the two central faces from all other faces, retaining their signs.
  have split_faces (m : ℕ) (c : Fin (m + 1) → X) (j : Fin (m + 1)) :
      (∑ a : Fin (m + 2),
        MonoidAlgebra.single (Q m c j ∘ a.succAbove) ((-1 : k) ^ (j.val + a.val))) =
      (∑ a : Fin (m + 2) with a.val < j.val ∨ j.val + 1 < a.val,
        MonoidAlgebra.single (Q m c j ∘ a.succAbove) ((-1 : k) ^ (j.val + a.val))) +
      (MonoidAlgebra.single (Q m c j ∘ j.castSucc.succAbove) (1 : k) -
        MonoidAlgebra.single (Q m c j ∘ j.succ.succAbove) (1 : k)) := by
    have central :
        (Finset.univ.filter fun a : Fin (m + 2) =>
          ¬ (a.val < j.val ∨ j.val + 1 < a.val)) = {j.castSucc, j.succ} := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, Fin.val_castSucc,
        Fin.val_succ]
      omega
    have distinct : j.castSucc ≠ j.succ := by
      intro h
      have := congrArg Fin.val h
      simp only [Fin.val_castSucc, Fin.val_succ] at this
      omega
    have even_sign : (-1 : k) ^ (j.val + j.val) = 1 := by
      rw [← two_mul, pow_mul]
      simp
    have odd_sign : (-1 : k) ^ (j.val + (j.val + 1)) = -1 := by
      rw [← Nat.add_assoc, pow_succ, even_sign, one_mul]
    rw [← Finset.sum_filter_add_sum_filter_not
      (s := Finset.univ) (p := fun a : Fin (m + 2) =>
        a.val < j.val ∨ j.val + 1 < a.val)]
    rw [central, Finset.sum_pair distinct]
    simp only [Fin.val_castSucc, Fin.val_succ, even_sign, odd_sign,
      MonoidAlgebra.single_neg, sub_eq_add_neg]
  have boundary (m : ℕ) (c : Fin (m + 1) → X) :
      Rep.standardComplex.d k X (m + 1) (P m c) =
      (∑ j : Fin (m + 1),
        ∑ a : Fin (m + 2) with a.val < j.val ∨ j.val + 1 < a.val,
          MonoidAlgebra.single (Q m c j ∘ a.succAbove) ((-1 : k) ^ (j.val + a.val))) +
      (MonoidAlgebra.single (v ∘ c) (1 : k) -
        MonoidAlgebra.single (u ∘ c) (1 : k)) := by
    change Rep.standardComplex.d k X (m + 1)
      (∑ j : Fin (m + 1), MonoidAlgebra.single (Q m c j) ((-1 : k) ^ j.val)) = _
    simp only [map_sum, Rep.standardComplex.d_single, ← pow_add]
    simp_rw [split_faces]
    rw [Finset.sum_add_distrib]
    congr 1
    exact Submission.p04_pb_60221840b0_central_telescoping u v m c
  constructor
  · intro c
    rw [boundary]
    have no_noncentral (j : Fin 1) (a : Fin 2) :
        ¬ (a.val < j.val ∨ j.val + 1 < a.val) := by
      have hj := j.isLt
      have ha := a.isLt
      omega
    simp only [no_noncentral, Finset.filter_false, Finset.sum_empty,
      Finset.sum_const_zero, zero_add]
  · intro n c
    have lower :
        (∑ b : Fin (n + 2), ((-1 : k) ^ b.val) • P n (c ∘ b.succAbove)) =
        ∑ b : Fin (n + 2), ∑ t : Fin (n + 1),
          MonoidAlgebra.single (Q n (c ∘ b.succAbove) t)
            ((-1 : k) ^ (b.val + t.val)) := by
      simp only [P, Q, Finset.smul_sum, MonoidAlgebra.smul_single, smul_eq_mul, pow_add]
    rw [boundary, lower, add_right_comm]
    have cancel := Submission.p04_pb_60221840b0_noncentral_cancellation (k := k) u v n c
    change _ + _ = 0 at cancel
    rw [cancel, zero_add]

end Submission

namespace Submission

/-- An additive group is trivial if every prime is avoided by a positive global annihilator.

For each element, its least positive annihilator divides every annihilator by Euclidean
division. A prime divisor of that least annihilator would contradict the hypothesis,
so the least annihilator is one and the element is zero.

The well-ordering step uses `Nat.find_spec` and `Nat.find_min` from
`Mathlib.Data.Nat.Find`. Euclidean division uses `nsmul_eq_mod_nsmul` from
`Mathlib.Algebra.Group.Basic`, and the prime divisor is supplied by
`Nat.exists_prime_and_dvd` from `Mathlib.Data.Nat.Prime.Defs`.
-/
theorem p04_eq_zero_of_prime_avoiding_annihilators :
    ∀ {V : Type*} [AddCommGroup V],
      (∀ p : ℕ, p.Prime → ∃ m : ℕ, 0 < m ∧ ¬ p ∣ m ∧ ∀ v : V, m • v = 0) →
      ∀ v : V, v = 0 := by
  intro V _ h v
  classical
  -- Choose the least positive annihilator of this element.
  obtain ⟨m₂, hm₂, _, h₂⟩ := h 2 Nat.prime_two
  have hex : ∃ n : ℕ, 0 < n ∧ n • v = 0 := ⟨m₂, hm₂, h₂ v⟩
  let n := Nat.find hex
  obtain ⟨hn_pos, hn_zero⟩ : 0 < n ∧ n • v = 0 := Nat.find_spec hex
  -- A nonzero remainder would be a smaller positive annihilator.
  have hn_dvd : ∀ m : ℕ, m • v = 0 → n ∣ m := by
    intro m hm
    apply Nat.dvd_of_mod_eq_zero
    by_contra hr
    have hr_zero : (m % n) • v = 0 := (nsmul_eq_mod_nsmul m hn_zero).symm.trans hm
    exact Nat.find_min hex (Nat.mod_lt m hn_pos) ⟨Nat.pos_of_ne_zero hr, hr_zero⟩
  -- Any prime divisor of n would divide its prime-avoiding annihilator.
  have hn_one : n = 1 := by
    by_contra hn
    obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd hn
    obtain ⟨m, _, hpm, hm⟩ := h p hp
    exact hpm (hpn.trans (hn_dvd m (hm v)))
  simpa only [hn_one, one_nsmul] using hn_zero

end Submission

namespace Submission

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The equivariant prism operators give a homotopy from the vertex map `v` to `u`. -/
theorem p04_rsh_82a013d1d0_prism_homotopy
    {k G : Type _} [CommRing k] [Group G] (H : Subgroup G) (u v : G → G)
    (hu : ∀ (h : H) (g : G), u ((h : G) * g) = (h : G) * u g)
    (hv : ∀ (h : H) (g : G), v ((h : G) * g) = (h : G) * v g) :
    let C := ((Rep.resFunctor H.subtype).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (Rep.standardComplex k G)
    ∀ U V : CategoryTheory.End C,
      (∀ (n : ℕ) (c : Fin (n + 1) → G),
        (U.f n).hom (MonoidAlgebra.single c (1 : k)) =
          MonoidAlgebra.single (u ∘ c) (1 : k)) →
      (∀ (n : ℕ) (c : Fin (n + 1) → G),
        (V.f n).hom (MonoidAlgebra.single c (1 : k)) =
          MonoidAlgebra.single (v ∘ c) (1 : k)) →
      Nonempty (Homotopy V U) := by
  classical
  intro C U V hU hV
  let P : ∀ n : ℕ, (Fin (n + 1) → G) → MonoidAlgebra k (Fin (n + 2) → G) :=
    fun n c => ∑ j : Fin (n + 1),
      MonoidAlgebra.single
        (Fin.insertNth j.castSucc (u (c j))
          (fun i : Fin (n + 1) => if i < j then u (c i) else v (c i)))
        ((-1 : k) ^ j.val)
  obtain ⟨D, hD⟩ := p04_prism_a8325b9888_equivariant_components (k := k) H u v hu hv
  change ∀ (n : ℕ) (c : Fin (n + 1) → G),
    (D n).hom (MonoidAlgebra.single c (1 : k)) = P n c at hD
  obtain ⟨hzero, hsucc⟩ := p04_prism_a8325b9888_boundary_identity (k := k) u v
  change ∀ c : Fin 1 → G, Rep.standardComplex.d k G 1 (P 0 c) =
    MonoidAlgebra.single (v ∘ c) (1 : k) - MonoidAlgebra.single (u ∘ c) (1 : k) at hzero
  change ∀ (n : ℕ) (c : Fin (n + 2) → G),
    Rep.standardComplex.d k G (n + 2) (P (n + 1) c) +
      ∑ b : Fin (n + 2), ((-1 : k) ^ b.val) • P n (c ∘ b.succAbove) =
    MonoidAlgebra.single (v ∘ c) (1 : k) - MonoidAlgebra.single (u ∘ c) (1 : k) at hsucc
  have hd (n : ℕ) (x : MonoidAlgebra k (Fin (n + 2) → G)) :
      (C.d (n + 1) n).hom x = Rep.standardComplex.d k G (n + 1) x :=
    Rep.standardComplex.d_apply k G x
  let hom : ∀ i j, C.X i ⟶ C.X j := fun i j =>
    if h : i + 1 = j then D i ≫ eqToHom (congrArg C.X h) else 0
  have hom_succ (i : ℕ) : hom i (i + 1) = D i := by
    simp [hom]
  refine ⟨{ hom := hom, zero := ?_, comm := ?_ }⟩
  · intro i j hij
    exact dif_neg hij
  · intro n
    cases n with
    | zero =>
      rw [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex, hom_succ, zero_add]
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.toLinearMap_injective
      refine MonoidAlgebra.lhom_ext' fun (c : Fin 1 → G) => LinearMap.ext_ring ?_
      change (V.f 0).hom (MonoidAlgebra.single c (1 : k)) =
        (C.d 1 0).hom ((D 0).hom (MonoidAlgebra.single c (1 : k))) +
          (U.f 0).hom (MonoidAlgebra.single c (1 : k))
      rw [hU, hV, hD, hd, hzero, sub_add_cancel]
    | succ n =>
      rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex, hom_succ, hom_succ]
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.toLinearMap_injective
      refine MonoidAlgebra.lhom_ext' fun (c : Fin (n + 2) → G) => LinearMap.ext_ring ?_
      change (V.f (n + 1)).hom (MonoidAlgebra.single c (1 : k)) =
        (D n).hom ((C.d (n + 1) n).hom (MonoidAlgebra.single c (1 : k))) +
          (C.d (n + 2) (n + 1)).hom
            ((D (n + 1)).hom (MonoidAlgebra.single c (1 : k))) +
          (U.f (n + 1)).hom (MonoidAlgebra.single c (1 : k))
      rw [hU, hV, hD, hd, hd, Rep.standardComplex.d_of, map_sum]
      have hsum :
          (∑ b : Fin (n + 2), (D n).hom
            (MonoidAlgebra.single (c ∘ b.succAbove) ((-1 : k) ^ b.val))) =
          ∑ b : Fin (n + 2), ((-1 : k) ^ b.val) • P n (c ∘ b.succAbove) := by
        apply Finset.sum_congr rfl
        intro b _
        rw [← mul_one ((-1 : k) ^ b.val), ← smul_eq_mul,
          ← MonoidAlgebra.smul_single, map_smul, hD]
        simp only [smul_eq_mul, mul_one]
      rw [hsum, add_comm _ (Rep.standardComplex.d k G (n + 2) (P (n + 1) c)),
        hsucc, sub_add_cancel]

set_option backward.isDefEq.respectTransparency.types false in
/-- The coordinatewise retraction and inclusion of homogeneous tuples give the
restricted standard-complex homotopy equivalence.

The linear extensions and their differential compatibility use
`MonoidAlgebra.mapDomainLinearMap` and `Rep.standardComplex.d_of` from pinned mathlib
`db584cd6d46c92f209a44c0f1c829460d327499d`; the two approved child declarations supply
the retraction and the prism homotopy. -/
theorem p04_tia_coh_restricted_standard_homotopy_equiv
    {k G : Type _} [CommRing k] [Group G] (H : Subgroup G) :
    Nonempty (HomotopyEquiv
      (((Rep.resFunctor H.subtype).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (Rep.standardComplex k G)) (Rep.standardComplex k H)) := by
  classical
  obtain ⟨r, hr, hrH⟩ := p04_rsh_82a013d1d0_equivariant_retraction H
  let C := ((Rep.resFunctor H.subtype).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj (Rep.standardComplex k G)
  let D := Rep.standardComplex k H
  -- Coordinatewise maps commute with every vertex deletion.
  have natural_d (L M : Type _) (f : L → M) (n : ℕ) :
      (Rep.standardComplex.d k M (n + 1)).comp
          (MonoidAlgebra.mapDomainLinearMap k k (fun c : Fin (n + 2) → L => f ∘ c)) =
        (MonoidAlgebra.mapDomainLinearMap k k (fun c : Fin (n + 1) → L => f ∘ c)).comp
          (Rep.standardComplex.d k L (n + 1)) := by
    apply MonoidAlgebra.lhom_ext'
    intro c
    apply LinearMap.ext_ring
    simp [Rep.standardComplex.d_of, Function.comp_assoc]
  let pF : ∀ n, C.X n ⟶ D.X n := fun n => Rep.ofHom
    { toLinearMap := MonoidAlgebra.mapDomainLinearMap k k
        (fun c : Fin (n + 1) → G => r ∘ c)
      isIntertwining' := by
        intro h
        apply MonoidAlgebra.lhom_ext'
        intro c
        apply LinearMap.ext_ring
        change MonoidAlgebra.mapDomainLinearMap k k (fun c => r ∘ c)
            (Representation.ofMulAction k G (Fin (n + 1) → G) (h : G)
              (MonoidAlgebra.single c 1)) =
          Representation.ofMulAction k H (Fin (n + 1) → H) h
            (MonoidAlgebra.mapDomainLinearMap k k (fun c => r ∘ c)
              (MonoidAlgebra.single c 1))
        simp only [Representation.ofMulAction_single,
          MonoidAlgebra.mapDomainLinearMap_single]
        congr 1
        funext i
        exact hr h (c i) }
  let qF : ∀ n, D.X n ⟶ C.X n := fun n => Rep.ofHom
    { toLinearMap := MonoidAlgebra.mapDomainLinearMap k k
        (fun c : Fin (n + 1) → H => H.subtype ∘ c)
      isIntertwining' := by
        intro h
        apply MonoidAlgebra.lhom_ext'
        intro c
        apply LinearMap.ext_ring
        change MonoidAlgebra.mapDomainLinearMap k k (fun c => H.subtype ∘ c)
            (Representation.ofMulAction k H (Fin (n + 1) → H) h
              (MonoidAlgebra.single c 1)) =
          Representation.ofMulAction k G (Fin (n + 1) → G) (h : G)
            (MonoidAlgebra.mapDomainLinearMap k k (fun c => H.subtype ∘ c)
              (MonoidAlgebra.single c 1))
        simp only [Representation.ofMulAction_single,
          MonoidAlgebra.mapDomainLinearMap_single]
        rfl }
  let p : C ⟶ D :=
    { f := pF
      comm' := by
        intro i j hij
        obtain rfl : j + 1 = i := hij
        apply Rep.hom_ext
        apply Representation.IntertwiningMap.ext
        apply LinearMap.ext
        intro x
        change ((Rep.standardComplex k H).d (j + 1) j).hom
            (MonoidAlgebra.mapDomainLinearMap k k (fun c => r ∘ c) x) =
          MonoidAlgebra.mapDomainLinearMap k k (fun c => r ∘ c)
            ((Rep.standardComplex k G).d (j + 1) j |>.hom x)
        rw [Rep.standardComplex.d_apply, Rep.standardComplex.d_apply]
        exact LinearMap.congr_fun (natural_d G H r j) x }
  let q : D ⟶ C :=
    { f := qF
      comm' := by
        intro i j hij
        obtain rfl : j + 1 = i := hij
        apply Rep.hom_ext
        apply Representation.IntertwiningMap.ext
        apply LinearMap.ext
        intro x
        change ((Rep.standardComplex k G).d (j + 1) j).hom
            (MonoidAlgebra.mapDomainLinearMap k k (fun c => H.subtype ∘ c) x) =
          MonoidAlgebra.mapDomainLinearMap k k (fun c => H.subtype ∘ c)
            ((Rep.standardComplex k H).d (j + 1) j |>.hom x)
        rw [Rep.standardComplex.d_apply, Rep.standardComplex.d_apply]
        exact LinearMap.congr_fun (natural_d H G H.subtype j) x }
  have hpq : q ≫ p = 𝟙 D := by
    apply HomologicalComplex.hom_ext
    intro n
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply MonoidAlgebra.lhom_ext'
    intro c
    apply LinearMap.ext_ring
    change MonoidAlgebra.mapDomainLinearMap k k (fun c => r ∘ c)
        (MonoidAlgebra.mapDomainLinearMap k k (fun c => H.subtype ∘ c)
          (MonoidAlgebra.single c 1)) = MonoidAlgebra.single c 1
    simp only [MonoidAlgebra.mapDomainLinearMap_single]
    congr 1
    funext i
    exact hrH (c i)
  obtain ⟨hp⟩ := p04_rsh_82a013d1d0_prism_homotopy (k := k) H
    id (fun g => (r g : G)) (fun _ _ => rfl)
    (fun h g => congrArg Subtype.val (hr h g)) (𝟙 C) (p ≫ q)
    (by intro n c; rfl)
    (by
      intro n c
      change MonoidAlgebra.mapDomainLinearMap k k (fun c => H.subtype ∘ c)
          (MonoidAlgebra.mapDomainLinearMap k k (fun c => r ∘ c)
            (MonoidAlgebra.single c 1)) = _
      simp only [MonoidAlgebra.mapDomainLinearMap_single]
      rfl)
  exact ⟨{ hom := p
           inv := q
           homotopyHomInvId := hp
           homotopyInvHomId := Homotopy.ofEq hpq }⟩

end Submission

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

namespace Submission

set_option backward.isDefEq.respectTransparency.types false in
/-- The coordinatewise retraction and inclusion of homogeneous tuples give the
restricted standard-complex homotopy equivalence.

The linear extensions and their differential compatibility use
`MonoidAlgebra.mapDomainLinearMap` and `Rep.standardComplex.d_of` from pinned mathlib
`db584cd6d46c92f209a44c0f1c829460d327499d`; the two approved child declarations supply
the retraction and the prism homotopy. -/
theorem p04_tia_coh_restricted_standard_homotopy_equiv
    {k G : Type _} [CommRing k] [Group G] (H : Subgroup G) :
    Nonempty (HomotopyEquiv
      (((Rep.resFunctor H.subtype).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (Rep.standardComplex k G)) (Rep.standardComplex k H)) := by
  classical
  obtain ⟨r, hr, hrH⟩ := p04_rsh_82a013d1d0_equivariant_retraction H
  let C := ((Rep.resFunctor H.subtype).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj (Rep.standardComplex k G)
  let D := Rep.standardComplex k H
  -- Coordinatewise maps commute with every vertex deletion.
  have natural_d (L M : Type _) (f : L → M) (n : ℕ) :
      (Rep.standardComplex.d k M (n + 1)).comp
          (MonoidAlgebra.mapDomainLinearMap k k (fun c : Fin (n + 2) → L => f ∘ c)) =
        (MonoidAlgebra.mapDomainLinearMap k k (fun c : Fin (n + 1) → L => f ∘ c)).comp
          (Rep.standardComplex.d k L (n + 1)) := by
    apply MonoidAlgebra.lhom_ext'
    intro c
    apply LinearMap.ext_ring
    simp [Rep.standardComplex.d_of, Function.comp_assoc]
  let pF : ∀ n, C.X n ⟶ D.X n := fun n => Rep.ofHom
    { toLinearMap := MonoidAlgebra.mapDomainLinearMap k k
        (fun c : Fin (n + 1) → G => r ∘ c)
      isIntertwining' := by
        intro h
        apply MonoidAlgebra.lhom_ext'
        intro c
        apply LinearMap.ext_ring
        change MonoidAlgebra.mapDomainLinearMap k k (fun c => r ∘ c)
            (Representation.ofMulAction k G (Fin (n + 1) → G) (h : G)
              (MonoidAlgebra.single c 1)) =
          Representation.ofMulAction k H (Fin (n + 1) → H) h
            (MonoidAlgebra.mapDomainLinearMap k k (fun c => r ∘ c)
              (MonoidAlgebra.single c 1))
        simp only [Representation.ofMulAction_single,
          MonoidAlgebra.mapDomainLinearMap_single]
        congr 1
        funext i
        exact hr h (c i) }
  let qF : ∀ n, D.X n ⟶ C.X n := fun n => Rep.ofHom
    { toLinearMap := MonoidAlgebra.mapDomainLinearMap k k
        (fun c : Fin (n + 1) → H => H.subtype ∘ c)
      isIntertwining' := by
        intro h
        apply MonoidAlgebra.lhom_ext'
        intro c
        apply LinearMap.ext_ring
        change MonoidAlgebra.mapDomainLinearMap k k (fun c => H.subtype ∘ c)
            (Representation.ofMulAction k H (Fin (n + 1) → H) h
              (MonoidAlgebra.single c 1)) =
          Representation.ofMulAction k G (Fin (n + 1) → G) (h : G)
            (MonoidAlgebra.mapDomainLinearMap k k (fun c => H.subtype ∘ c)
              (MonoidAlgebra.single c 1))
        simp only [Representation.ofMulAction_single,
          MonoidAlgebra.mapDomainLinearMap_single]
        rfl }
  let p : C ⟶ D :=
    { f := pF
      comm' := by
        intro i j hij
        obtain rfl : j + 1 = i := hij
        apply Rep.hom_ext
        apply Representation.IntertwiningMap.ext
        apply LinearMap.ext
        intro x
        change ((Rep.standardComplex k H).d (j + 1) j).hom
            (MonoidAlgebra.mapDomainLinearMap k k (fun c => r ∘ c) x) =
          MonoidAlgebra.mapDomainLinearMap k k (fun c => r ∘ c)
            ((Rep.standardComplex k G).d (j + 1) j |>.hom x)
        rw [Rep.standardComplex.d_apply, Rep.standardComplex.d_apply]
        exact LinearMap.congr_fun (natural_d G H r j) x }
  let q : D ⟶ C :=
    { f := qF
      comm' := by
        intro i j hij
        obtain rfl : j + 1 = i := hij
        apply Rep.hom_ext
        apply Representation.IntertwiningMap.ext
        apply LinearMap.ext
        intro x
        change ((Rep.standardComplex k G).d (j + 1) j).hom
            (MonoidAlgebra.mapDomainLinearMap k k (fun c => H.subtype ∘ c) x) =
          MonoidAlgebra.mapDomainLinearMap k k (fun c => H.subtype ∘ c)
            ((Rep.standardComplex k H).d (j + 1) j |>.hom x)
        rw [Rep.standardComplex.d_apply, Rep.standardComplex.d_apply]
        exact LinearMap.congr_fun (natural_d H G H.subtype j) x }
  have hpq : q ≫ p = 𝟙 D := by
    apply HomologicalComplex.hom_ext
    intro n
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply MonoidAlgebra.lhom_ext'
    intro c
    apply LinearMap.ext_ring
    change MonoidAlgebra.mapDomainLinearMap k k (fun c => r ∘ c)
        (MonoidAlgebra.mapDomainLinearMap k k (fun c => H.subtype ∘ c)
          (MonoidAlgebra.single c 1)) = MonoidAlgebra.single c 1
    simp only [MonoidAlgebra.mapDomainLinearMap_single]
    congr 1
    funext i
    exact hrH (c i)
  obtain ⟨hp⟩ := p04_rsh_82a013d1d0_prism_homotopy (k := k) H
    id (fun g => (r g : G)) (fun _ _ => rfl)
    (fun h g => congrArg Subtype.val (hr h g)) (𝟙 C) (p ≫ q)
    (by intro n c; rfl)
    (by
      intro n c
      change MonoidAlgebra.mapDomainLinearMap k k (fun c => H.subtype ∘ c)
          (MonoidAlgebra.mapDomainLinearMap k k (fun c => r ∘ c)
            (MonoidAlgebra.single c 1)) = _
      simp only [MonoidAlgebra.mapDomainLinearMap_single]
      rfl)
  exact ⟨{ hom := p
           inv := q
           homotopyHomInvId := hp
           homotopyInvHomId := Homotopy.ofEq hpq }⟩

end Submission

namespace Submission

set_option warningAsError true in
/-- Restriction and corestriction on group cohomology compose to the subgroup index.

The two approved dependencies give the resolution comparison and the Hom-complex
transfer identity. Transport to group cohomology uses `groupCohomologyIso`,
`Functor.mapHomotopyEquiv`, `HomotopyEquiv.toHomologyIso`, and
`HomologicalComplex.homologyUnop` from pinned mathlib
`db584cd6d46c92f209a44c0f1c829460d327499d`. -/
theorem p04_tia_cohomology_transfer :
    ∀ {k G : Type _} [CommRing k] [Group G] [Fintype G]
      (A : Rep k G) (H : Subgroup G) [Fintype H] (n : ℕ),
    ∃ R : groupCohomology A n →ₗ[k] groupCohomology (Rep.res H.subtype A) n,
      ∃ C : groupCohomology (Rep.res H.subtype A) n →ₗ[k] groupCohomology A n,
        ∀ x : groupCohomology A n, C (R x) = H.index • x := by
  intro k G _ _ _ A H _ n
  classical
  obtain ⟨e⟩ := p04_tia_coh_restricted_standard_homotopy_equiv (k := k) H
  obtain ⟨r, c, hrc⟩ := p04_tia_coh_hom_complex_transfer A H (Rep.standardComplex k G)
  -- Applying Hom(-, Res A) reverses the comparison of the two resolutions.
  let F := ((linearYoneda k (Rep k H)).obj (Rep.res H.subtype A)).rightOp
  let e' := F.mapHomotopyEquiv e
  let T := HomologicalComplex.homologyFunctor (ModuleCat k) (ComplexShape.up ℕ) n
  let γ : groupCohomology A n ≅ T.obj ((Rep.standardComplex k G).linearYonedaObj k A) :=
    groupCohomologyIso A n (Rep.standardResolution k G)
  let α :
      T.obj (ChainComplex.linearYonedaObj
        (((Rep.resFunctor H.subtype).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          (Rep.standardComplex k G)) k (Rep.res H.subtype A)) ≅
        groupCohomology (Rep.res H.subtype A) n :=
    HomologicalComplex.homologyUnop _ n ≪≫ (e'.toHomologyIso n).unop.symm ≪≫
      (HomologicalComplex.homologyUnop _ n).symm ≪≫
        (groupCohomologyIso (Rep.res H.subtype A) n (Rep.standardResolution k H)).symm
  have hrc' : T.map r ≫ T.map c = H.index • 𝟙 _ := by
    rw [← T.map_comp, hrc, T.map_nsmul, T.map_id]
  let R := γ.hom ≫ T.map r ≫ α.hom
  let C := α.inv ≫ T.map c ≫ γ.inv
  have hRC : R ≫ C = H.index • 𝟙 (groupCohomology A n) := by
    change (γ.hom ≫ T.map r ≫ α.hom) ≫ (α.inv ≫ T.map c ≫ γ.inv) = _
    calc
      _ = γ.hom ≫ (T.map r ≫ T.map c) ≫ γ.inv := by
        simp only [Category.assoc, Iso.hom_inv_id_assoc]
      _ = H.index • 𝟙 (groupCohomology A n) := by
        rw [hrc']
        simp only [Preadditive.comp_nsmul, Preadditive.nsmul_comp, Category.id_comp,
          Iso.hom_inv_id]
  refine ⟨R.hom, C.hom, fun x => ?_⟩
  exact congrArg (fun f : groupCohomology A n ⟶ groupCohomology A n => f.hom x) hRC

end Submission

namespace Submission

set_option warningAsError true in
/-- Restriction to a subgroup with zero Tate cohomology makes its index annihilate
the ambient Tate cohomology. The four branches are those of `Rep.tateCohomology`
in `Definitions/Def_GroupCohomology_TateCohomology.lean`. -/
theorem p04_index_nsmul_zero_of_restriction_isZero :
    ∀ {k G : Type _} [CommRing k] [Group G] [Fintype G]
      (A : Rep k G) (H : Subgroup G) [Fintype H] (q : ℤ),
      CategoryTheory.Limits.IsZero ((Rep.res H.subtype A).tateCohomology q) →
        ∀ x : A.tateCohomology q, H.index • x = 0 := by
  intro k G _ _ _ A H _ q h
  cases q with
  | ofNat n =>
    cases n with
    | zero =>
      change ∀ x : A.tateH0, H.index • x = 0
      have : Subsingleton ((Rep.res H.subtype A).tateH0) :=
        ModuleCat.subsingleton_of_isZero h
      intro x
      obtain ⟨R, C, hCR⟩ := Submission.p04_tia_tate_zero_transfer A H
      rw [← hCR x, Subsingleton.elim (R x) 0, map_zero]
    | succ n =>
      change ∀ x : groupCohomology A (n + 1), H.index • x = 0
      have : Subsingleton (groupCohomology (Rep.res H.subtype A) (n + 1)) :=
        ModuleCat.subsingleton_of_isZero h
      intro x
      obtain ⟨R, C, hCR⟩ := Submission.p04_tia_cohomology_transfer A H (n + 1)
      rw [← hCR x, Subsingleton.elim (R x) 0, map_zero]
  | negSucc n =>
    cases n with
    | zero =>
      change ∀ x : A.tateHneg1, H.index • x = 0
      have : Subsingleton ((Rep.res H.subtype A).tateHneg1) :=
        ModuleCat.subsingleton_of_isZero h
      intro x
      obtain ⟨T, P, hPT⟩ := Submission.p04_tia_tate_neg_one_transfer A H
      rw [← hPT x, Subsingleton.elim (T x) 0, map_zero]
    | succ n =>
      change ∀ x : groupHomology A (n + 1), H.index • x = 0
      have : Subsingleton (groupHomology (Rep.res H.subtype A) (n + 1)) :=
        ModuleCat.subsingleton_of_isZero h
      intro x
      obtain ⟨T, P, hPT⟩ := Submission.p04_tia_homology_transfer A H (n + 1)
      rw [← hPT x, Subsingleton.elim (T x) 0, map_zero]

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


end Submission

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

set_option warningAsError true in
/-- Restriction and coset averaging on the equivariant Hom cochain complex. -/
theorem Submission.p04_tia_coh_hom_complex_transfer :
    ∀ {k G : Type _} [CommRing k] [Group G] [Fintype G]
      (A : Rep k G) (H : Subgroup G) [Fintype H]
      (X : ChainComplex (Rep k G) ℕ),
      ∃ R : Quiver.Hom (X.linearYonedaObj k A)
        (ChainComplex.linearYonedaObj
          (((Rep.resFunctor H.subtype).mapHomologicalComplex (ComplexShape.down ℕ)).obj X)
          k (Rep.res H.subtype A)),
      ∃ C : Quiver.Hom
        (ChainComplex.linearYonedaObj
          (((Rep.resFunctor H.subtype).mapHomologicalComplex (ComplexShape.down ℕ)).obj X)
          k (Rep.res H.subtype A))
        (X.linearYonedaObj k A),
      CategoryTheory.CategoryStruct.comp R C =
        H.index • CategoryTheory.CategoryStruct.id (X.linearYonedaObj k A) := by
  intro k G _ _ _ A H _ X
  classical
  let : Fintype (G ⧸ H) := Fintype.ofFinite _
  choose C hC using fun (B : Rep k G) =>
    Submission.p04_hct139_coset_average_exists A B H
  obtain ⟨hC_natural, hC_index⟩ :=
    Submission.p04_hct139_coset_average_laws A H C hC
  let U := X.linearYonedaObj k A
  let V := ChainComplex.linearYonedaObj
    (((Rep.resFunctor H.subtype).mapHomologicalComplex (ComplexShape.down ℕ)).obj X)
    k (Rep.res H.subtype A)
  let R : U ⟶ V :=
    { f := fun _ => ModuleCat.ofHom ((Rep.resFunctor H.subtype).mapLinearMap k)
      comm' := by
        intro i j _
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro F
        change (Rep.resFunctor H.subtype).map (X.d j i) ≫
            (Rep.resFunctor H.subtype).map F =
          (Rep.resFunctor H.subtype).map (X.d j i ≫ F)
        exact ((Rep.resFunctor H.subtype).map_comp _ _).symm }
  let T : V ⟶ U :=
    { f := fun i => ModuleCat.ofHom (C (X.X i))
      comm' := by
        intro i j _
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro F
        change X.d j i ≫ C (X.X i) F =
          C (X.X j) ((Rep.resFunctor H.subtype).map (X.d j i) ≫ F)
        exact (hC_natural (X.X i) (X.X j) (X.d j i) F).symm }
  refine ⟨R, T, ?_⟩
  apply HomologicalComplex.hom_ext
  intro i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro F
  change C (X.X i) ((Rep.resFunctor H.subtype).map F) = H.index • F
  exact hC_index (X.X i) F

namespace Submission

set_option warningAsError true in
/-- Restriction and corestriction on group cohomology compose to the subgroup index.

The two approved dependencies give the resolution comparison and the Hom-complex
transfer identity. Transport to group cohomology uses `groupCohomologyIso`,
`Functor.mapHomotopyEquiv`, `HomotopyEquiv.toHomologyIso`, and
`HomologicalComplex.homologyUnop` from pinned mathlib
`db584cd6d46c92f209a44c0f1c829460d327499d`. -/
theorem p04_tia_cohomology_transfer :
    ∀ {k G : Type _} [CommRing k] [Group G] [Fintype G]
      (A : Rep k G) (H : Subgroup G) [Fintype H] (n : ℕ),
    ∃ R : groupCohomology A n →ₗ[k] groupCohomology (Rep.res H.subtype A) n,
      ∃ C : groupCohomology (Rep.res H.subtype A) n →ₗ[k] groupCohomology A n,
        ∀ x : groupCohomology A n, C (R x) = H.index • x := by
  intro k G _ _ _ A H _ n
  classical
  obtain ⟨e⟩ := p04_tia_coh_restricted_standard_homotopy_equiv (k := k) H
  obtain ⟨r, c, hrc⟩ := p04_tia_coh_hom_complex_transfer A H (Rep.standardComplex k G)
  -- Applying Hom(-, Res A) reverses the comparison of the two resolutions.
  let F := ((linearYoneda k (Rep k H)).obj (Rep.res H.subtype A)).rightOp
  let e' := F.mapHomotopyEquiv e
  let T := HomologicalComplex.homologyFunctor (ModuleCat k) (ComplexShape.up ℕ) n
  let γ : groupCohomology A n ≅ T.obj ((Rep.standardComplex k G).linearYonedaObj k A) :=
    groupCohomologyIso A n (Rep.standardResolution k G)
  let α :
      T.obj (ChainComplex.linearYonedaObj
        (((Rep.resFunctor H.subtype).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          (Rep.standardComplex k G)) k (Rep.res H.subtype A)) ≅
        groupCohomology (Rep.res H.subtype A) n :=
    HomologicalComplex.homologyUnop _ n ≪≫ (e'.toHomologyIso n).unop.symm ≪≫
      (HomologicalComplex.homologyUnop _ n).symm ≪≫
        (groupCohomologyIso (Rep.res H.subtype A) n (Rep.standardResolution k H)).symm
  have hrc' : T.map r ≫ T.map c = H.index • 𝟙 _ := by
    rw [← T.map_comp, hrc, T.map_nsmul, T.map_id]
  let R := γ.hom ≫ T.map r ≫ α.hom
  let C := α.inv ≫ T.map c ≫ γ.inv
  have hRC : R ≫ C = H.index • 𝟙 (groupCohomology A n) := by
    change (γ.hom ≫ T.map r ≫ α.hom) ≫ (α.inv ≫ T.map c ≫ γ.inv) = _
    calc
      _ = γ.hom ≫ (T.map r ≫ T.map c) ≫ γ.inv := by
        simp only [Category.assoc, Iso.hom_inv_id_assoc]
      _ = H.index • 𝟙 (groupCohomology A n) := by
        rw [hrc']
        simp only [Preadditive.comp_nsmul, Preadditive.nsmul_comp, Category.id_comp,
          Iso.hom_inv_id]
  refine ⟨R.hom, C.hom, fun x => ?_⟩
  exact congrArg (fun f : groupCohomology A n ⟶ groupCohomology A n => f.hom x) hRC

open CategoryTheory Rep Representation MonoidalCategory

namespace Submission

/-- Transfer and projection on tensor coinvariant homology have composite the subgroup index.

Transfer is the sum over right cosets, with each summand descended through representative
independence. Naturality gives chain maps, and the additive homology functor preserves their
index composite. The quotient of right cosets is used directly, so the construction does not
require a choice of transversal or normality of `H`.

The quotient and restriction APIs come from mathlib's `RepresentationTheory/Coinvariants.lean`
and `RepresentationTheory/Rep/Res.lean`; the complex and additive homology APIs come from
`RepresentationTheory/Homological/GroupHomology/Basic.lean` and
`Algebra/Homology/ShortComplex/HomologicalComplex.lean`, at the pinned revision
`db584cd6d46c92f209a44c0f1c829460d327499d`. Right-coset cardinality uses
`GroupTheory/Coset/Defs.lean` and `GroupTheory/Index.lean`; preservation of repeated addition
uses `CategoryTheory/Preadditive/AdditiveFunctor.lean` at the same revision. -/
theorem p04_ht_coinvariant_complex_transfer
    {k G : Type _} [CommRing k] [Group G] [Fintype G]
    (A : Rep k G) (H : Subgroup G) [Fintype H]
    (C : ChainComplex (Rep k G) ℕ) (n : ℕ) :
    ∃ T : (C.coinvariantsTensorObj A).homology n →ₗ[k]
      ((((Rep.resFunctor (k := k) H.subtype).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj C).coinvariantsTensorObj
          (Rep.res H.subtype A)).homology n,
    ∃ P : ((((Rep.resFunctor (k := k) H.subtype).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj C).coinvariantsTensorObj
          (Rep.res H.subtype A)).homology n →ₗ[k]
      (C.coinvariantsTensorObj A).homology n,
    ∀ x : (C.coinvariantsTensorObj A).homology n, P (T x) = H.index • x := by
  classical
  let Q := Quotient (QuotientGroup.rightRel H)
  let : Fintype Q := Fintype.ofFinite Q
  have cardQ : Fintype.card Q = H.index := by
    rw [H.index_eq_card, Nat.card_eq_fintype_card]
    exact Fintype.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel H)
  -- The summand depends only on the right coset of the representative.
  have representative_independent (W : Rep k G) (s t : G)
      (h : QuotientGroup.rightRel H s t) :
      Coinvariants.mk (W.ρ.comp H.subtype) ∘ₗ W.ρ s =
        Coinvariants.mk (W.ρ.comp H.subtype) ∘ₗ W.ρ t := by
    ext v
    have e := Coinvariants.mk_self_apply (W.ρ.comp H.subtype)
      (⟨t * s⁻¹, QuotientGroup.rightRel_apply.mp h⟩ : H) (W.ρ s v)
    simpa [← Module.End.mul_apply, ← map_mul] using e.symm
  let summand (W : Rep k G) : Q → (W →ₗ[k] Coinvariants (W.ρ.comp H.subtype)) :=
    Quotient.lift (fun s => Coinvariants.mk (W.ρ.comp H.subtype) ∘ₗ W.ρ s)
      (representative_independent W)
  let rightMul (g : G) : Q ≃ Q :=
    { toFun := Quotient.map (fun s => s * g) (by
        intro s t h
        apply QuotientGroup.rightRel_apply.mpr
        simpa using QuotientGroup.rightRel_apply.mp h)
      invFun := Quotient.map (fun s => s * g⁻¹) (by
        intro s t h
        apply QuotientGroup.rightRel_apply.mpr
        simpa using QuotientGroup.rightRel_apply.mp h)
      left_inv := by intro q; induction q using Quotient.inductionOn; simp
      right_inv := by intro q; induction q using Quotient.inductionOn; simp }
  have summand_mul (W : Rep k G) (g : G) (q : Q) :
      summand W q ∘ₗ W.ρ g = summand W (rightMul g q) := by
    induction q using Quotient.inductionOn with | h s =>
      dsimp [summand, rightMul]
      rw [map_mul]
      rfl
  let transfer (W : Rep k G) : W.ρ.Coinvariants →ₗ[k]
      Coinvariants (W.ρ.comp H.subtype) :=
    Coinvariants.lift W.ρ (∑ q : Q, summand W q) (by
      intro g
      ext v
      simp only [LinearMap.comp_apply, LinearMap.sum_apply]
      have term (q : Q) : summand W q (W.ρ g v) = summand W (rightMul g q) v :=
        congrArg (fun f => f v) (summand_mul W g q)
      simp_rw [term]
      exact (rightMul g).sum_comp (fun q => summand W q v))
  let projection (W : Rep k G) : Coinvariants (W.ρ.comp H.subtype) →ₗ[k]
      W.ρ.Coinvariants := Coinvariants.lift _ (Coinvariants.mk W.ρ) (by
        intro h
        ext v
        exact Coinvariants.mk_self_apply W.ρ (h : G) v)
  have projection_transfer (W : Rep k G) (x : W.ρ.Coinvariants) :
      projection W (transfer W x) = H.index • x := by
    induction x using Coinvariants.induction_on with | h v =>
      change projection W ((∑ q : Q, summand W q) v) = _
      simp only [LinearMap.sum_apply, map_sum]
      have term (q : Q) : projection W (summand W q v) = Coinvariants.mk W.ρ v := by
        induction q using Quotient.inductionOn with | h s =>
          exact Coinvariants.mk_self_apply W.ρ s v
      simp_rw [term]
      simp [cardQ]
  have transfer_natural {W V : Rep k G} (f : W ⟶ V) :
      Coinvariants.map _ _ (Rep.resMap H.subtype f).hom ∘ₗ transfer W =
        transfer V ∘ₗ Coinvariants.map _ _ f.hom := by
    apply Coinvariants.hom_ext
    ext v
    change Coinvariants.map _ _ (Rep.resMap H.subtype f).hom
      ((∑ q : Q, summand W q) v) = (∑ q : Q, summand V q) (f.hom v)
    simp only [LinearMap.sum_apply, map_sum]
    apply Finset.sum_congr rfl
    intro q _
    induction q using Quotient.inductionOn with | h s =>
      change Coinvariants.mk _ (f.hom (W.ρ s v)) = Coinvariants.mk _ (V.ρ s (f.hom v))
      rw [Rep.hom_comm_apply]
  have projection_natural {W V : Rep k G} (f : W ⟶ V) :
      Coinvariants.map _ _ f.hom ∘ₗ projection W =
        projection V ∘ₗ Coinvariants.map _ _ (Rep.resMap H.subtype f).hom := by
    apply Coinvariants.hom_ext
    rfl
  -- Restriction preserves the underlying tensor modules and their differentials definitionally.
  let D := C.coinvariantsTensorObj A
  let E := (((Rep.resFunctor (k := k) H.subtype).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj C).coinvariantsTensorObj (Rep.res H.subtype A)
  let τ : D ⟶ E :=
    { f := fun i => ModuleCat.ofHom (transfer (A ⊗ C.X i))
      comm' := by
        intro i j _
        apply ModuleCat.hom_ext
        exact transfer_natural (A ◁ C.d i j) }
  let π : E ⟶ D :=
    { f := fun i => ModuleCat.ofHom (projection (A ⊗ C.X i))
      comm' := by
        intro i j _
        apply ModuleCat.hom_ext
        exact projection_natural (A ◁ C.d i j) }
  have composite : τ ≫ π = H.index • 𝟙 D := by
    ext i x
    exact projection_transfer (A ⊗ C.X i) x
  -- Functoriality and additivity pass the degreewise identity to every homology degree.
  let F := HomologicalComplex.homologyFunctor (ModuleCat k) (ComplexShape.down ℕ) n
  refine ⟨(F.map τ).hom, (F.map π).hom, ?_⟩
  intro x
  have e : F.map τ ≫ F.map π = H.index • 𝟙 (F.obj D) := by
    rw [← F.map_comp, composite, F.map_nsmul, F.map_id]
  exact congrArg (fun f => f.hom x) e

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

set_option warningAsError true in
/-- Transfer and projection on group homology have composite multiplication by the index.
The accepted complex transfer is transported through the accepted restricted comparison
and `groupHomologyIso` for `Rep.standardResolution`. These upstream declarations are in
`Mathlib/RepresentationTheory/Homological/GroupHomology/Basic.lean` and
`Mathlib/RepresentationTheory/Homological/Resolution.lean` at the pinned revision
`db584cd6d46c92f209a44c0f1c829460d327499d`. -/
theorem p04_tia_homology_transfer {k G : Type _} [CommRing k] [Group G] [Fintype G]
    (A : Rep k G) (H : Subgroup G) [Fintype H] (n : ℕ) :
    ∃ T : groupHomology A n →ₗ[k] groupHomology (Rep.res H.subtype A) n,
      ∃ P : groupHomology (Rep.res H.subtype A) n →ₗ[k] groupHomology A n,
        ∀ x : groupHomology A n, P (T x) = H.index • x := by
  classical
  obtain ⟨T, P, hPT⟩ :=
    Submission.p04_ht_coinvariant_complex_transfer A H (Rep.standardComplex k G) n
  obtain ⟨α⟩ := Submission.p04_ht_restricted_standard_comparison A H n
  let γ : groupHomology A n ≃ₗ[k]
      ((Rep.standardComplex k G).coinvariantsTensorObj A).homology n :=
    (groupHomologyIso A n (Rep.standardResolution k G)).toLinearEquiv
  refine ⟨α.toLinearMap.comp (T.comp γ.toLinearMap),
    γ.symm.toLinearMap.comp (P.comp α.symm.toLinearMap), ?_⟩
  intro x
  change γ.symm (P (α.symm (α (T (γ x))))) = H.index • x
  rw [α.symm_apply_apply, hPT, map_nsmul, γ.symm_apply_apply]
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
