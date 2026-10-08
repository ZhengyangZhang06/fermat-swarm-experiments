/-
Copyright 2026 Anthropic, PBC. Licensed under Apache-2.0; see LICENSE.
Source: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_Rep_isZero_tateCohomology_of_forall_sylow.lean
Selected child: equivariant components of the prism homotopy.
-/

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology

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

namespace Submission

/-- The signed prism assignment extends to morphisms of the restricted standard complex.

The free-module extension uses `Finsupp.lift` and `MonoidAlgebra.coeffLinearEquiv`, as in
`Rep.standardComplex.d`. Equivariance is checked on generators using
`Representation.ofMulAction_single` and `Fin.insertNth_eq_iff`. -/
theorem p04_prism_a8325b9888_equivariant_components :
    ∀ {k G : Type u} [CommRing k] [Group G] (H : Subgroup G) (u v : G → G),
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
