<!-- theorem-id: fermat-p07/root.rigidification_reduction-a1.isogeny_level_transport-a1 -->

## Theorem `Submission.p07_rr_isogeny_transport_857cd4d38c`

Let a,b ∈ ℚ, let Λ be a ℤ-submodule of QuaternionAlgebra ℚ a 0 b, and let N,d ∈ ℕ. Let T,U be commutative rings of universe zero and k : T ≃+* U a ring isomorphism. Let E,F be FakeEllipticCurve Λ N over T and D,H be FakeEllipticCurve Λ N over U. Suppose i : D.A ≅ E.A and j : H.A ≅ F.A are scheme isomorphisms satisfying IsPullbackVia k.toRingHom E D i.hom, IsPullbackVia k.symm.toRingHom D E i.inv, IsPullbackVia k.toRingHom F H j.hom, and IsPullbackVia k.symm.toRingHom H F j.inv. Let φ : D.A → H.A and ψ : H.A → D.A be scheme morphisms, with hφ : φ ≫ H.f = D.f. Assume IsIsogenyPair d D H φ ψ and PreservesLevel D H φ hφ. Put Φ = i.inv ≫ φ ≫ j.hom and Ψ = j.inv ≫ ψ ≫ i.hom. Then IsIsogenyPair d E F Φ Ψ, and there exists hΦ : Φ ≫ F.f = E.f such that PreservesLevel E F Φ hΦ.

Node: `root.rigidification_reduction-a1.isogeny_level_transport-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/7

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/56

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p07_rr_isogeny_transport_857cd4d38c`

```lean
∀ {a b : ℚ} (Λ : Submodule ℤ (QuaternionAlgebra ℚ a 0 b)) (N d : ℕ) (T U : Type) [CommRing T] [CommRing U] (k : T ≃+* U) (E F : CerednikDrinfeld.QM.FakeEllipticCurve Λ N T) (D H : CerednikDrinfeld.QM.FakeEllipticCurve Λ N U) (i : CategoryTheory.Iso D.A E.A) (j : CategoryTheory.Iso H.A F.A), CerednikDrinfeld.QM.FakeEllipticCurve.IsPullbackVia k.toRingHom E D i.hom → CerednikDrinfeld.QM.FakeEllipticCurve.IsPullbackVia k.symm.toRingHom D E i.inv → CerednikDrinfeld.QM.FakeEllipticCurve.IsPullbackVia k.toRingHom F H j.hom → CerednikDrinfeld.QM.FakeEllipticCurve.IsPullbackVia k.symm.toRingHom H F j.inv → ∀ (φ : Quiver.Hom D.A H.A) (ψ : Quiver.Hom H.A D.A) (hφ : CategoryTheory.CategoryStruct.comp φ H.f = D.f), CerednikDrinfeld.QM.FakeEllipticCurve.IsIsogenyPair d D H φ ψ → CerednikDrinfeld.QM.FakeEllipticCurve.PreservesLevel D H φ hφ → CerednikDrinfeld.QM.FakeEllipticCurve.IsIsogenyPair d E F (CategoryTheory.CategoryStruct.comp i.inv (CategoryTheory.CategoryStruct.comp φ j.hom)) (CategoryTheory.CategoryStruct.comp j.inv (CategoryTheory.CategoryStruct.comp ψ i.hom)) ∧ ∃ hΦ : CategoryTheory.CategoryStruct.comp (CategoryTheory.CategoryStruct.comp i.inv (CategoryTheory.CategoryStruct.comp φ j.hom)) F.f = E.f, CerednikDrinfeld.QM.FakeEllipticCurve.PreservesLevel E F (CategoryTheory.CategoryStruct.comp i.inv (CategoryTheory.CategoryStruct.comp φ j.hom)) hΦ
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
- Child DAG node: `root.rigidification_reduction-a1.isogeny_level_transport-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Put u = i.hom, v = i.inv, z = j.hom and w = j.inv. Write κ = Spec(k.toRingHom) : Spec U → Spec T and ε = Spec(k.symm.toRingHom) : Spec T → Spec U. The ring-isomorphism identities and contravariance of Spec give ε ≫ κ = id and κ ≫ ε = id. The scheme-isomorphism identities give u ≫ v = id, v ≫ u = id, z ≫ w = id and w ≫ z = id. Define Φ = v ≫ φ ≫ z and Ψ = w ≫ ψ ≫ u, the exact morphisms in the conclusion.
2. The commuting equations contained in the four pullback hypotheses are u ≫ E.f = D.f ≫ κ, v ≫ D.f = E.f ≫ ε, z ≫ F.f = H.f ≫ κ and w ≫ H.f = F.f ≫ ε. The old isogeny-pair hypothesis supplies ψ ≫ D.f = H.f as well as φ's over-base equation. Therefore Φ ≫ F.f = v ≫ φ ≫ H.f ≫ κ = v ≫ D.f ≫ κ = E.f ≫ ε ≫ κ = E.f. Likewise Ψ ≫ E.f = w ≫ ψ ≫ D.f ≫ κ = w ≫ H.f ≫ κ = F.f. Denote these proofs by hΦ and hΨ. Any alternative proof of φ's over-base equality appearing in the isogeny-pair hypothesis agrees with the given hφ by proof irrelevance.
3. For any scheme X and t : X → Spec T, composition with v sends E-points over t to D-points over t ≫ ε; composition with w sends F-points over t to H-points over t ≫ ε. For any s : X → Spec U, composition with u sends D-points over s to E-points over s ≫ κ, and composition with z sends H-points to F-points over s ≫ κ. The equations in step 2 show that all four point maps are well-defined. Each preserves multiplication: its defining IsPullbackVia multiplication equality is the equality of underlying point morphisms, and subtype extensionality makes it the corresponding equality of points. Each also carries a level factorization to a level factorization, since its IsPullbackVia level condition supplies precisely a witness through the target level immersion.
4. Let P,Q be E-points over t. Their images under mapPt Φ hΦ are obtained successively by composition with v, application of mapPt φ hφ, and composition with z. The last base is (t ≫ ε) ≫ κ = t; after this identification the underlying composite morphism is P.1 ≫ Φ, respectively Q.1 ≫ Φ. The first and third point maps preserve multiplication by step 3, and the middle map preserves multiplication by the old isogeny-pair hypothesis. Applying these three multiplication equalities in order proves mapPt Φ hΦ (E.L.mul t P Q) = F.L.mul t (mapPt Φ hΦ P) (mapPt Φ hΦ Q). For F-points P,Q, use composition with w, the old multiplication-preserving map ψ, and composition with u. The same base identity and the three corresponding equalities give the multiplication condition for Ψ. All equalities of over-base points follow from equality of underlying morphisms and proof irrelevance.
5. Fix x ∈ Λ. The action equations for v, φ and z give E.act(x) ≫ Φ = v ≫ D.act(x) ≫ φ ≫ z = v ≫ φ ≫ H.act(x) ≫ z = Φ ≫ F.act(x). The action equations for w, ψ and u give F.act(x) ≫ Ψ = w ≫ H.act(x) ≫ ψ ≫ u = w ≫ ψ ≫ D.act(x) ≫ u = Ψ ≫ E.act(x).
6. Fix any membership witness hd for the quaternion scalar obtained from d in Λ, and let x_d be that element of Λ. Cancelling z ≫ w gives Φ ≫ Ψ = v ≫ (φ ≫ ψ) ≫ u. The old scalar equation changes this to v ≫ D.act(x_d) ≫ u. The action equation E.act(x_d) ≫ v = v ≫ D.act(x_d), followed by v ≫ u = id, makes it E.act(x_d). Cancelling u ≫ v in the other product similarly gives Ψ ≫ Φ = w ≫ (ψ ≫ φ) ≫ z = w ≫ H.act(x_d) ≫ z = F.act(x_d). This works for every hd; no hypothesis asserting that such a witness exists is needed. Steps 2, 4, 5 and 6 are exactly all fields of IsIsogenyPair d E F Φ Ψ.
7. Fix any E-point P over t that factors through E.lev. The level condition for v sends P to a D-point factoring through D.lev. The assumed PreservesLevel D H φ hφ sends that point under φ to an H-point factoring through H.lev. The level condition for z supplies a factorization of its image through F.lev. After (t ≫ ε) ≫ κ = t, the underlying image is P.1 ≫ v ≫ φ ≫ z = (mapPt Φ hΦ P).1. Thus this factorization proves PreservesLevel E F Φ hΦ.
8. Return the isogeny-pair assertion from step 6 and hΦ with the level assertion from step 7.

## Key steps

1. Define the conjugated morphisms and record the ring and scheme inverse identities.
2. Prove both conjugated morphisms lie over Spec T.
3. Extract multiplication and level preservation for the four transport maps on points.
4. Compose point-map multiplication identities to prove both isogeny multiplication conditions.
5. Compose the action equations to obtain equivariance.
6. Cancel inverse isomorphisms and transport both scalar-action equations.
7. Transport a level-factorization witness through the inverse isomorphism, old isogeny, and forward isomorphism.
8. Return the isogeny pair and its forward over-base proof with level preservation.

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

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/228

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
