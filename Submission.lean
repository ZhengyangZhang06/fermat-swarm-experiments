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

end Submission
