<!-- theorem-id: fermat-p07/root.rigidification_reduction-a1.curve_pullback_composition-a1 -->

## Theorem `Submission.p07_rr_pullback_comp_857cd4d38c`

Let a,b ∈ ℚ, let Λ be a ℤ-submodule of QuaternionAlgebra ℚ a 0 b, and let N ∈ ℕ. Let S₀,S₁,S₂ be commutative rings of universe zero, with ring homomorphisms f : S₀ → S₁ and h : S₁ → S₂. For j = 0,1,2 let Eⱼ be a FakeEllipticCurve Λ N over Sⱼ. Let g₀₁ : E₁.A → E₀.A and g₁₂ : E₂.A → E₁.A be scheme morphisms. If FakeEllipticCurve.IsPullbackVia f E₀ E₁ g₀₁ and FakeEllipticCurve.IsPullbackVia h E₁ E₂ g₁₂, then FakeEllipticCurve.IsPullbackVia (h.comp f) E₀ E₂ (g₁₂ ≫ g₀₁).

Node: `root.rigidification_reduction-a1.curve_pullback_composition-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/7

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/56

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p07_rr_pullback_comp_857cd4d38c`

```lean
∀ {a b : ℚ} (Λ : Submodule ℤ (QuaternionAlgebra ℚ a 0 b)) (N : ℕ) (S₀ S₁ S₂ : Type) [CommRing S₀] [CommRing S₁] [CommRing S₂] (f : S₀ →+* S₁) (h : S₁ →+* S₂) (E₀ : CerednikDrinfeld.QM.FakeEllipticCurve Λ N S₀) (E₁ : CerednikDrinfeld.QM.FakeEllipticCurve Λ N S₁) (E₂ : CerednikDrinfeld.QM.FakeEllipticCurve Λ N S₂) (g₀₁ : Quiver.Hom E₁.A E₀.A) (g₁₂ : Quiver.Hom E₂.A E₁.A), CerednikDrinfeld.QM.FakeEllipticCurve.IsPullbackVia f E₀ E₁ g₀₁ → CerednikDrinfeld.QM.FakeEllipticCurve.IsPullbackVia h E₁ E₂ g₁₂ → CerednikDrinfeld.QM.FakeEllipticCurve.IsPullbackVia (h.comp f) E₀ E₂ (CategoryTheory.CategoryStruct.comp g₁₂ g₀₁)
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

- Parent DAG node: `root.rigidification_reduction-a1`
- Child DAG node: `root.rigidification_reduction-a1.curve_pullback_composition-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Write α = Spec(f) and β = Spec(h). Unpack the two IsPullbackVia hypotheses into their pullback squares and their multiplication, action, and level conditions. Their commuting equations are g₀₁ ≫ E₀.f = E₁.f ≫ α and g₁₂ ≫ E₁.f = E₂.f ≫ β. Hence (g₁₂ ≫ g₀₁) ≫ E₀.f = E₂.f ≫ (β ≫ α). Contravariance of Spec identifies β ≫ α with Spec(h.comp f).
2. Verify the universal property of this composite square. Given any scheme X, maps a : X → E₀.A and t : X → Spec S₂ satisfying a ≫ E₀.f = t ≫ β ≫ α, the first pullback square gives a unique b : X → E₁.A with b ≫ g₀₁ = a and b ≫ E₁.f = t ≫ β. The second gives a unique c : X → E₂.A with c ≫ g₁₂ = b and c ≫ E₂.f = t. Then c ≫ g₁₂ ≫ g₀₁ = a. If c' satisfies the same outer equations, c' ≫ g₁₂ has the two defining equations of b and therefore equals b; uniqueness in the second square now gives c' = c. Thus the composite square is a pullback.
3. Fix X, t : X → Spec S₂, and E₂-points P,Q over t. Let P₁,Q₁ be their composites with g₁₂, regarded as E₁-points over t ≫ β using the second square's commuting equation. Let P₀,Q₀ be their further composites with g₀₁, now over t ≫ β ≫ α. The second multiplication condition gives (E₂.L.mul t P Q).1 ≫ g₁₂ = (E₁.L.mul (t ≫ β) P₁ Q₁).1. Composing this equality with g₀₁ and applying the first multiplication condition gives (E₂.L.mul t P Q).1 ≫ (g₁₂ ≫ g₀₁) = (E₀.L.mul (t ≫ Spec(h.comp f)) P₀ Q₀).1. Associativity and Spec's composition identity identify the displayed bases and the point morphisms with those required by the composite predicate; proof irrelevance identifies their over-base proofs.
4. For each x ∈ Λ, the two action conditions give E₂.act(x) ≫ g₁₂ ≫ g₀₁ = g₁₂ ≫ E₁.act(x) ≫ g₀₁ = g₁₂ ≫ g₀₁ ≫ E₀.act(x). This is the composite action condition.
5. Suppose a point P of E₂ over t factors through E₂.lev. The second level condition supplies w₁ : X → E₁.C with w₁ ≫ E₁.lev = P.1 ≫ g₁₂. Thus P₁ factors through E₁.lev. Applying the first level condition to P₁ supplies w₀ : X → E₀.C with w₀ ≫ E₀.lev = P₁.1 ≫ g₀₁ = P.1 ≫ (g₁₂ ≫ g₀₁). This is exactly the required final level witness.
6. The pullback square from step 2 together with steps 3–5 supplies every conjunct of IsPullbackVia (h.comp f) E₀ E₂ (g₁₂ ≫ g₀₁).

## Key steps

1. Identify the composite base morphism using contravariance of Spec.
2. Construct and prove uniqueness of the outer lift by two successive pullback lifts.
3. Compose multiplication compatibility on test-scheme points.
4. Compose action compatibility by associativity.
5. Pass level-factorization witnesses through both morphisms.
6. Assemble the composite IsPullbackVia predicate.

## Reference use

### local-project

Queries:
- `rg -n 'structure Rigidification|def IsPullbackVia|structure IsPullbackVia|def IsIsogenyPair|structure IsIsogenyPair|preservesLevel|namespace Rigidification' .humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/project/Definitions`
- `rg -n 'IsPullbackVia|IsIsogenyPair' .humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/project/Theorems --glob '*.lean'`
- `rg -n 'paste_horiz|paste_vert|theorem.*comp|def mapPt|def FactorsThrough' .humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/mathlib/Mathlib/CategoryTheory/Limits/Shapes/Pullback/IsPullback .humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/project/Definitions/Def_CerednikDrinfeld_QMModuli.lean`
- `rg -n --hidden --no-ignore 'p07_rr_pullback_comp_857cd4d38c|p07_rr_isogeny_transport_857cd4d38c' /mnt/data/zhengyang-workspace/fermat-swarm-projects --glob 'dag.json' --glob '*handoff*.json' --glob '*.lean'`
- `#print axioms CerednikDrinfeld.QM.FakeEllipticCurve.IsPullbackVia`
- `#print axioms CerednikDrinfeld.QM.FakeEllipticCurve.IsIsogenyPair`
- `#print axioms CerednikDrinfeld.QM.FakeEllipticCurve.PreservesLevel`
- `#print axioms CerednikDrinfeld.QM.mapPt`
- `#print axioms CerednikDrinfeld.QM.FactorsThrough`
- `#print axioms CategoryTheory.IsPullback.paste_horiz`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/project/Definitions/Def_CerednikDrinfeld_QMFormalModuleOf.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/project/Definitions/Def_CerednikDrinfeld_QMIsogeny.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/project/Definitions/Def_CerednikDrinfeld_QMRigidification.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/project/Definitions/Def_CerednikDrinfeld_QMModuli.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/project/Theorems`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/mathlib/Mathlib/CategoryTheory/Limits/Shapes/Pullback/IsPullback/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/dag.json`
- `/tmp/p07-rr-decomposition-857cd4d38c/TypesAgainstImports.lean`
- `/tmp/p07-rr-decomposition-857cd4d38c/types-and-axioms.log`
- `/tmp/p07-rr-decomposition-857cd4d38c/literal-submission.log`
- `/tmp/p07-rr-decomposition-857cd4d38c/literal-import.log`

The manifest pins project 73257f1e32d99b75813b037f28a5cf45a2db886d and mathlib db584cd6d46c92f209a44c0f1c829460d327499d; the checked revisions match and their checked tracked sources are clean. All 47 project modules in the import closure match the snapshot and the cached source modules used for diagnostics. IsPullbackVia contains a pullback square, multiplication compatibility, action compatibility, and directional level preservation. IsIsogenyPair and PreservesLevel have exactly the conditions addressed below. Mathlib supplies IsPullback.paste_horiz. The searched project Theorems directory contains no IsPullbackVia or IsIsogenyPair matches, and the proposed-name search found no collisions. Both proposed types elaborate against Submission's five imports under Lean 4.33.1. The six audited declarations depend only on propext, Classical.choice and Quot.sound. Literal import Submission remains blocked: unchanged Submission.lean reports unknown attribute targets AlgebraicGeometry.Scheme.Hom.opensMapFinal, GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase and RegularLocalRingQuotientAscent.dualNumberFst_apply, so no importable Submission object is produced. These diagnostic checks are not comparator acceptance.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/245

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
