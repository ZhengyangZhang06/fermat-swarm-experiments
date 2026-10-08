<!-- theorem-id: fermat-p07/root.full_level_quotient-a1.curve_quotient-a1.abelian_surface_quotient-a1 -->

## Theorem `Submission.p07_cq_abelian_surface_quotient_857cd4d38c`

Let S be a universe-zero commutative ring, J an ideal of S, A a universe-zero scheme, and f : A → Spec S. Assume AbelianSchemePropertyBundle S f and that topologicalKrullDim of the topological fibre f⁻¹({s}) is 2 for every s ∈ Spec S. Put β = Spec(Ideal.Quotient.mk J) and p = pullback.snd f β. Then AbelianSchemePropertyBundle (S/J) p holds, and every topological fibre of p has topological Krull dimension 2. There are no Noetherian, nontriviality, or nilpotence assumptions.

Node: `root.full_level_quotient-a1.curve_quotient-a1.abelian_surface_quotient-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/7

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/63

Prerequisites: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/78

Decomposition children: None

## Lean problem

Declaration: `Submission.p07_cq_abelian_surface_quotient_857cd4d38c`

```lean
∀ (S : Type) [CommRing S] (J : Ideal S) (A : AlgebraicGeometry.Scheme.{0}) (f : Quiver.Hom A (AlgebraicGeometry.Spec (CommRingCat.of S))), GoodReductionJacobian.AbelianSchemePropertyBundle S f → (∀ s : ↥(AlgebraicGeometry.Spec (CommRingCat.of S)), topologicalKrullDim ↥(f.base ⁻¹' {s}) = 2) → let β := AlgebraicGeometry.Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)); let p := CategoryTheory.Limits.pullback.snd f β; GoodReductionJacobian.AbelianSchemePropertyBundle (S ⧸ J) p ∧ (∀ t : ↥(AlgebraicGeometry.Spec (CommRingCat.of (S ⧸ J))), topologicalKrullDim ↥(p.base ⁻¹' {t}) = 2)
```

### Frozen project context

`Fermat/Thm_CerednikDrinfeld_QM_RigidifiedPairClass_exists_ptR_eq.lean` at `73257f1e32d99b75813b037f28a5cf45a2db886d` supplies the original imports, definitions and root contract. Child hypotheses are stated above; prerequisite declarations are linked in their issues.

```lean
/-
Copyright 2026 Anthropic, PBC. Licensed under Apache-2.0; see LICENSE.
Source: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_CerednikDrinfeld_QM_RigidifiedPairClass_exists_ptR_eq.lean
Modified: replaced the proof with sorry and removed P2M proof imports.
Requires the upstream Definitions modules and their dependencies.
-/

import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMFineModuliT
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneCharts
import Definitions.Def_CerednikDrinfeld_RigidifiedPairClassModel
attribute [-instance] AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory
attribute [-simp] GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst
attribute [-simp] RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.PolarisedAbelianScheme.mk.injEq AlgebraicGeometry.PolarisedAbelianScheme.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian

theorem CerednikDrinfeld.QM.RigidifiedPairClass.exists_ptR_eq
    {r N : ℕ} [Fact r.Prime] [NeZero N] (hrN : ¬ r ∣ N) {rbar : ℕ} [Fact rbar.Prime] (hrr : rbar ≠ r)

    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π}) (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr]
    {a b : ℚ} (hBq : IsIndefiniteRamifiedExactlyAt a b r rbar)
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)

    (coord : ↥Λ → Zp2 r × Zp2 r) (hcoord : IsOrderCoord Λ r coord)
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))

    (n : ℕ) (hn : 3 ≤ n) (hrn : ¬ r ∣ n) (M : Scheme.{0}) (fM : M ⟶ Spec (CommRingCat.of 𝒪))
    (ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N n S → SchemeHomOver s fM)
    (hM : IsFineModuli Λ N n M fM ptF)

    (C : Type) [CommRing C] [IsNoetherianRing C] [Algebra 𝒪 C] (hC : IsNilpotent (algebraMap 𝒪 C π)) (ψ : Onr →ₐ[𝒪] C)

    (X : ℕ → Scheme.{0}) (ξ : ∀ d, X d ⟶ Limits.pullback fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))))
    (tM : ∀ (T : Type) [CommRing T] [Algebra C T],
      FakeEllipticCurve.WithFullLevel Λ N n T → SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C T))) (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))))
    (xOf : ∀ (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
      (ψT : Onr →ₐ[𝒪] T) (_ : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
      (u : FakeEllipticCurve.WithFullLevel Λ N n T) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1),
      { x : Spec (CommRingCat.of (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)})) ⟶ X ρ.d //
        x ≫ ξ ρ.d = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}))) ≫ (tM T u).1 })
    (hmap : RigidifiedPairClass.MapCompat 𝒪 π Onr Λ hΛℤ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ tM xOf)

    (htM : ∀ (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
        (u : FakeEllipticCurve.WithFullLevel Λ N n T),
        (tM T u).1 ≫ Limits.pullback.fst fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))) = (ptF T (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 T))) u).1)

    (hx3 : (∀ (d : ℕ) (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
                (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
                (h0 : algebraMap C T (algebraMap 𝒪 C π) = 0) (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C T))) (ξ d ≫ Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C))))),
                ∃ (u : FakeEllipticCurve.WithFullLevel Λ N n T) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1) (hd : ρ.d = d),
                  (RigidifiedPairClass.ptX 𝒪 π Onr Λ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ tM xOf) d T ψT hψT u ρ hd h0 = x))

    (hxOf : ∀ (S S' : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
        [CommRing S'] [Algebra C S'] [Algebra 𝒪 S'] [IsScalarTower 𝒪 C S'] (φ : S →ₐ[C] S')
        (ψS : Onr →ₐ[𝒪] S) (hψS : ψS = (IsScalarTower.toAlgHom 𝒪 C S).comp ψ)
        (hψS' : (φ.restrictScalars 𝒪).comp ψS = (IsScalarTower.toAlgHom 𝒪 C S').comp ψ)
        (u : FakeEllipticCurve.WithFullLevel Λ N n S) (u' : FakeEllipticCurve.WithFullLevel Λ N n S')
        (ρ : FakeEllipticCurve.Rigidification r π A₀ ψS u.1)
        (ρ' : FakeEllipticCurve.Rigidification r π A₀ ((φ.restrictScalars 𝒪).comp ψS) u'.1)
        (g : u'.1.A ⟶ u.1.A) (hg : FakeEllipticCurve.IsPullbackVia (φ : S →+* S') u.1 u'.1 g),
        (u'.2.P).1 ≫ g = Spec.map (CommRingCat.ofHom (φ : S →+* S')) ≫ (u.2.P).1 →
        FakeEllipticCurve.Rigidification.IsPullbackVia (φ.restrictScalars 𝒪) g hg ρ ρ' →
          ∃ hd : ρ'.d = ρ.d, (xOf S' ((φ.restrictScalars 𝒪).comp ψS) hψS' u' ρ').1 ≫ eqToHom (congrArg X hd) =
            Spec.map (CommRingCat.ofHom (RigidifiedPairClass.qmap (algebraMap 𝒪 C π) φ)) ≫ (xOf S ψS hψS u ρ).1) :
    (∀ (S : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
          (ψS : Onr →ₐ[𝒪] S) (hψS : ψS = (IsScalarTower.toAlgHom 𝒪 C S).comp ψ) (z : (RigidifiedPairClass.PR 𝒪 π Onr Λ hΛℤ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ tM xOf hmap).obj S),
          ∃ (u : FakeEllipticCurve.WithFullLevel Λ N n S) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψS u.1), (RigidifiedPairClass.ptR 𝒪 π Onr Λ hΛℤ A₀ n C ψ (Limits.pullback.snd fM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))) X ξ tM xOf hmap) S ψS hψS u ρ = z) := by
  sorry
```

## Natural-language proof

Reviewed mathematical argument; formal verification state: `proved`.

# Parent-supplied natural-language proof

- Parent DAG node: `root.full_level_quotient-a1.curve_quotient-a1`
- Child DAG node: `root.full_level_quotient-a1.curve_quotient-a1.abelian_surface_quotient-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Let h be the assumed bundle and let T = S/J, β = Spec(Ideal.Quotient.mk J), A_T = A ×_{Spec S} Spec T, g = pullback.fst f β, and p = pullback.snd f β. The quotient map is surjective. Consequently β is a closed immersion by AlgebraicGeometry.IsClosedImmersion.spec_of_quotient_mk in Mathlib/AlgebraicGeometry/Morphisms/ClosedImmersion.lean:115, at the pinned mathlib revision db584cd6d46c92f209a44c0f1c829460d327499d. Its underlying map is therefore injective.
2. The morphism p is the base change of f. The fields h.smooth and h.proper, together with AlgebraicGeometry.smooth_isStableUnderBaseChange in Morphisms/Smooth.lean:117 and AlgebraicGeometry.IsProper.isStableUnderBaseChange in Morphisms/Proper.lean:72 at that same revision, imply Smooth p and IsProper p.
3. The morphism g is the base change of the closed immersion β. By IsClosedImmersion.isStableUnderBaseChange in Morphisms/ClosedImmersion.lean:382, it is a closed immersion, hence a topological embedding. The pinned theorem AlgebraicGeometry.Scheme.Pullback.range_fst in Mathlib/AlgebraicGeometry/PullbackCarrier.lean:328 gives range(g) = f⁻¹(range(β)).
4. Fix t ∈ Spec T and put s = β(t). The equation g ≫ f = p ≫ β shows that g restricts to a map F_t : p⁻¹({t}) → f⁻¹({s}). This map is injective because g is. For x in f⁻¹({s}), f(x) = β(t) belongs to range(β), so step 3 supplies y ∈ A_T with g(y) = x. Commutativity gives β(p(y)) = f(g(y)) = β(t); injectivity of β gives p(y) = t. Thus y is in the required fibre and F_t is surjective.
5. Restricting a topological embedding to subspaces yields an embedding into the target subspace. Hence the bijection F_t is a homeomorphism: its inducing property identifies the source topology with the topology transported from the target, making the inverse continuous. The old fibre is nonempty and connected by h.connectedFibres s. Its homeomorphic new fibre is likewise nonempty and connected. Interpreted as a subset of A_T, this is precisely IsConnected (p.base ⁻¹' {t}).
6. A homeomorphism sends irreducible closed subsets bijectively to irreducible closed subsets, preserves inclusion in both directions, and therefore preserves the lengths of all strict chains. Thus it preserves topological Krull dimension; the pinned formal result is IsHomeomorph.topologicalKrullDim_eq in Mathlib/Topology/KrullDimension.lean:53. Applied to F_t and the assumed dimension equation for s, it gives topologicalKrullDim ↥(p.base ⁻¹' {t}) = 2. Since t was arbitrary, both the connectedness and dimension conclusions hold for every fibre.
7. Extract G : RelativeGroupLaw S f from h.hasGroupLaw. Apply the sibling theorem group_law_pullback to S, T, Ideal.Quotient.mk J, A, f, and G. Its witness H : RelativeGroupLaw T p supplies Nonempty (RelativeGroupLaw T p).
8. Assemble Smooth p, IsProper p, the connected-fibre assertions from step 5, and the group-law witness from step 7 into AbelianSchemePropertyBundle T p. Pair this bundle with the dimension assertions from step 6. This proves the exact conclusion, including when Spec T is empty, in which case the universally quantified fibre assertions are vacuous.

## Key steps

1. Recognize the quotient spectrum map and its pullback as closed immersions.
2. Transfer smoothness and properness by base change.
3. Use the pullback image formula and injectivity to identify each entire topological fibre.
4. Transfer nonempty connectedness and topological Krull dimension through the resulting homeomorphism.
5. Obtain a group-law witness from group_law_pullback and assemble the bundle.

## Reference use

### local-project

Queries:
- `structure FakeEllipticCurve|structure RelativeGroupLaw|def tangentZero|def IsTangentVector|structure AbelianSchemePropertyBundle`
- `baseChangePointToBase|baseChangePointOfBase|baseChange_mul|RelativeGroupLaw.baseChange`
- `baseChange|pullback|tangent`
- `homeomorph|Homeomorph|isConnected`
- `p07_cq_group_law_pullback_857cd4d38c|p07_cq_abelian_surface_quotient_857cd4d38c|p07_cq_level_geometry_pullback_857cd4d38c`
- `\b(sorry|admit|axiom)\b`
- `git -C .lake/packages/mathlib rev-parse HEAD`
- `git -C .lake/packages/mathlib status --porcelain`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lean /tmp/p07-cq-decomposition-857cd4d38c/TypesAgainstPrerequisites.lean`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lean -o /tmp/p07-cq-decomposition-857cd4d38c/Submission.olean Submission.lean`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lean /tmp/p07-cq-decomposition-857cd4d38c/AxiomsVerified.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/project/Definitions/Def_CerednikDrinfeld_QMModuli.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/project/Definitions/Def_AlgebraicGeometry_RelativeGroupLaw.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/project/Definitions/Def_JacJ1Iface.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/project/P2M`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/mathlib/Mathlib/AlgebraicGeometry/PullbackCarrier.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/mathlib/Mathlib/AlgebraicGeometry/Morphisms/Smooth.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/mathlib/Mathlib/AlgebraicGeometry/Morphisms/Proper.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/mathlib/Mathlib/AlgebraicGeometry/Morphisms/ClosedImmersion.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/mathlib/Mathlib/AlgebraicGeometry/Morphisms/Finite.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/mathlib/Mathlib/AlgebraicGeometry/Morphisms/Flat.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/mathlib/Mathlib/AlgebraicGeometry/Morphisms/FinitePresentation.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/mathlib/Mathlib/AlgebraicGeometry/Morphisms/FlatRank.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/mathlib/Mathlib/Topology/KrullDimension.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/Submission.lean`
- `/tmp/p07-cq-decomposition-857cd4d38c/TypesAgainstPrerequisites.lean`
- `/tmp/p07-cq-decomposition-857cd4d38c/TypesAgainstPrerequisites.log`
- `/tmp/p07-cq-decomposition-857cd4d38c/Submission.log`
- `/tmp/p07-cq-decomposition-857cd4d38c/AxiomsVerified.lean`
- `/tmp/p07-cq-decomposition-857cd4d38c/AxiomsVerified.log`

The snapshot pins project 73257f1e32d99b75813b037f28a5cf45a2db886d and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. The definitions confirm the exact group-law, bundle, curve, and level obligations. PullbackCarrier:328 supplies range_fst; ClosedImmersion:115 and :382 supply quotient closed immersions and base-change stability; Smooth:117 and Proper:72 supply the other bundle properties. Finite:60, Flat:81, FinitePresentation:85, and FlatRank:157 support the level-geometry statement. KrullDimension:53 supplies homeomorphism invariance. No relevant P2M helper or existing relative-group-law base-change construction was found. None of the proposed names occurs in the inspected DAG or handoffs. All nine dependency checkouts are clean and match their pinned revisions. The 47 prerequisite source modules match the snapshot and cached-build sources byte-for-byte. All three proposed types elaborate without warnings against Submission's unchanged five imports. Symbolic quotient-ring instance synthesis returns Ideal.Quotient.commRing J. The completed transitive axiom audit reports only propext, Classical.choice, and Quot.sound. Literal import Submission validation remains blocked: compiling the unchanged module fails on the pre-existing attribute references AlgebraicGeometry.Scheme.Hom.opensMapFinal, GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase, and RegularLocalRingQuotientAscent.dualNumberFst_apply. No source repair or proof acceptance is claimed.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: Pending

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
