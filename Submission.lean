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
  obtain ⟨T, hT, h1⟩ := H.exists_isComplement_right (1 : G)
  refine ⟨fun g => (hT.equiv g).1, ?_, ?_⟩
  · intro h g
    exact congrArg Prod.fst (hT.equiv_mul_left h g)
  · intro h
    exact hT.equiv_fst_eq_self_of_mem_of_one_mem h1 h.property

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
