<!-- theorem-id: fermat-p07/root.full_level_quotient-a1 -->

## Theorem `Submission.p07_full_level_quotient_857cd4d38c`

Let a,b be rational numbers, Λ a Z-submodule of QuaternionAlgebra Q a 0 b, N,n natural numbers, S a commutative ring of universe zero, and J an ideal of S. For every u : FakeEllipticCurve.WithFullLevel Λ N n S, put T = S/J and q = Ideal.Quotient.mk J. There exist v : FakeEllipticCurve.WithFullLevel Λ N n T and a scheme morphism g : v.1.A → u.1.A such that FakeEllipticCurve.IsPullbackVia q u.1 v.1 g and v.2.P.1 ≫ g = Spec(q) ≫ u.2.P.1. No Noetherian, nilpotence, primality, or nonzero-level assumption is required.

Node: `root.full_level_quotient-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/7

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/7

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/63, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/64

## Lean problem

Declaration: `Submission.p07_full_level_quotient_857cd4d38c`

```lean
∀ {a b : ℚ} (Λ : Submodule ℤ (QuaternionAlgebra ℚ a 0 b)) (N n : ℕ) (S : Type) [CommRing S] (J : Ideal S) (u : CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel Λ N n S), ∃ (v : CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel Λ N n (S ⧸ J)) (g : Quiver.Hom v.1.A u.1.A), CerednikDrinfeld.QM.FakeEllipticCurve.IsPullbackVia (Ideal.Quotient.mk J) u.1 v.1 g ∧ CategoryTheory.CategoryStruct.comp v.2.P.1 g = CategoryTheory.CategoryStruct.comp (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) u.2.P.1
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

- Parent DAG node: `root`
- Child DAG node: `root.full_level_quotient-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Write E = u.1, P = u.2.P, T = S/J, q : S → T for the quotient, and q* = Spec(q). Form A_T = E.A ×_{Spec S} Spec T with projections g : A_T → E.A and f_T : A_T → Spec T. Scheme pullbacks exist. For every scheme W and t : W → Spec T, composition with g gives a bijection B_t from morphisms Q : W → A_T satisfying Q ≫ f_T = t to morphisms R : W → E.A satisfying R ≫ E.f = t ≫ q*. Its inverse sends R to the unique pullback lift of R and t. The two projection equations prove both inverse identities. These bijections commute with precomposition, since precomposing a lift gives the lift with the precomposed projections.
2. Define multiplication, identity, and inverse on points of A_T by transporting E.L through B_t. Applying the injective B_t proves associativity, both identity laws, inverse cancellation, and commutativity from their counterparts for E. Compatibility of B with precomposition and E.L.mul_natural proves multiplication naturality. This constructs the required RelativeGroupLaw L_T and its commutativity witness. For m in Λ, define act_T(m) as the pullback lift of g ≫ E.act(m) and f_T. The action is over Spec T. Comparing both projections proves act_one and act_mul whenever the membership hypotheses in those fields hold. Applying B_t proves act_hom and act_add, using the corresponding equations for E. In particular, B intertwines the actions and preserves all group operations.
3. The morphism f_T is smooth and proper by base change. The precise pinned results are AlgebraicGeometry.smooth_isStableUnderBaseChange in Mathlib/AlgebraicGeometry/Morphisms/Smooth.lean:117 and AlgebraicGeometry.IsProper.isStableUnderBaseChange in Morphisms/Proper.lean:72, at revision db584cd6d46c92f209a44c0f1c829460d327499d. To check the topological fibre requirements, Spec T is the closed subspace V(J) of Spec S. On an affine chart Spec D of E.A, its inverse image in A_T is Spec(D ⊗_S T) = Spec(D/JD); thus g is a homeomorphism onto the subspace of E.A mapping into V(J). For t in Spec T and s = q*(t), every point over s belongs to this subspace. Its unique preimage lies over t because q* is injective. Therefore g induces a homeomorphism of the entire fibres over t and s. It preserves nonemptiness, connectedness, and topological Krull dimension: irreducible closed subsets and their strict inclusion chains correspond under a homeomorphism. The new fibre is consequently connected and has dimension two. Together with the group law, this verifies the AbelianSchemePropertyBundle and dim_fibre fields.
4. To prove act_trace, fix an algebraically closed field K, α : T → K, a finite K-module V₀, and a parametrization τ of tangent vectors satisfying every hypothesis in that field. Set α_S = α ∘ q. Apply B to points over Spec K and Spec(DualNumber K). These bijections commute with tangentZero and tangentScale because those operations are precomposition. They preserve identity and multiplication by construction. A dual-number point is tangent precisely when its image is tangent: the restriction equation can be checked after applying the injective B over Spec K. Hence τ_S = B ∘ τ is injective, has range exactly the tangent vectors of E, and satisfies the required addition and scalar equations. If a K-linear map Φ obeys the action equation for τ, action compatibility gives that equation for τ_S. For every m in Λ and integer j with m + star(m) = j, E.act_trace now gives trace_K(Φ) = j. The vector space and linear map are unchanged, proving act_trace for A_T.
5. Form C_T = E.C ×_{Spec S} Spec T using E.lev ≫ E.f. The projections define lev_T : C_T → A_T. This is the base change of E.lev: both C_T and E.C ×_{E.A} A_T represent pairs with the same compatibility equation. Hence lev_T is a closed immersion by AlgebraicGeometry.IsClosedImmersion.isStableUnderBaseChange, Morphisms/ClosedImmersion.lean:382 at the pinned revision. For a point Q over t, Q factors through lev_T if and only if B_t(Q) factors through E.lev. Forward composition gives one implication. Conversely, a factorization R ≫ E.lev = Q ≫ g implies R ≫ E.lev ≫ E.f = t ≫ q*, so R and t lift to C_T. The resulting map to A_T equals Q by its two projections.
6. Through this factorization equivalence and B_t, E.lev_sub gives closure under multiplication and inverse, E.lev_one gives the identity, and E.lev_stable gives action stability. Preservation of repeated addition follows by induction: the zero case is preservation of identity, and the successor case follows from preservation of multiplication. Applying this for N proves lev_torsion.
7. The structure map C_T → Spec T is the base change of E.C → Spec S. On affine charts, a finite S-module D becomes the finite T-module D ⊗_S T, generated by tensors of a finite generating family. For a T-module L, L ⊗_T (D ⊗_S T) identifies with L ⊗_S D; restriction of scalars is exact, so flatness of D over S proves flatness after base change. Finite presentations base change by sending their finitely many coefficients to T, proving local finite presentation. The rank is N² by AlgebraicGeometry.Scheme.Hom.finrank_pullback_snd, Morphisms/FlatRank.lean:157 at the pinned revision; its hypotheses are precisely finiteness and flatness, already verified. For an algebraically closed K and α : T → K with (N : K) ≠ 0, B restricts to a multiplication-preserving bijection on the level-subgroup points by step 5. Compose E.lev_fibre's parametrization by ZMod N × ZMod N with its inverse. The resulting bijection satisfies the required addition equation. These verifications complete the fake elliptic curve E_T over T.
8. Define P_T as the unique lift of q* ≫ P.1 and the identity of Spec T. Compatibility follows from P.1 ≫ E.f = id. Thus P_T.1 ≫ g = q* ≫ P.1. Precomposition of points preserves multiplication by RelativeGroupLaw.mul_natural. It also preserves identity: if H is the image of identity, then H·H = H, and group cancellation gives H = 1. It therefore preserves repeated addition by induction. Applying precomposition to u.2.torsion and then using the injectivity of B proves that P_T is n-torsion.
9. Fix an algebraically closed K, α : T → K, and an n-torsion point Q of E_T. B(Q) is n-torsion on E. The original full-level generation property supplies m in Λ whose action on P specialized at α ∘ q is B(Q). Naturality of B and its action compatibility identify this with the image of the corresponding equation for P_T; injectivity proves that equation. Similarly, m kills the specialization of P_T if and only if it kills the specialization of P. The original annihilator property identifies this with existence of y in Λ such that m = (n : Q) • y. This proves both remaining FullLevel fields.
10. Set v = (E_T,P_T). The pullback square from step 1, multiplication compatibility from step 2, action compatibility from step 2, and the forward factorization implication from step 5 are exactly the fields of FakeEllipticCurve.IsPullbackVia q E E_T g. Step 8 gives the required equation for distinguished sections. These witnesses prove the stated existential conclusion.

## Key steps

1. Construct the scheme pullback and its natural bijections on relative points.
2. Transport the group law and lift the quaternion action.
3. Verify smoothness, properness, connected fibres, and fibre dimension using quotient-fibre homeomorphisms.
4. Transport tangent parametrizations to prove act_trace.
5. Base change the level immersion and prove the factorization equivalence.
6. Verify the subgroup, finiteness, flatness, presentation, rank, and geometric-level fields.
7. Lift the full-level section and verify torsion, generation, and annihilator.
8. Package the curve pullback witness and section equation.

## Reference use

### local-project

Queries:
- `rg --files -g AGENTS.md -g Submission.lean -g lakefile.lean -g lakefile.toml -g lean-toolchain -g '*decompos*' -g '*reserv*' -g '*dag*' -g '*state*' .humanize .`
- `qmap_comp_mk|quotEquiv_comp_mk|Pt.ext|def qmap|def quotEquiv|def ptX`
- `exists.*[Pp]ullback|[Pp]ullback.*exists|def.*baseChange|theorem.*baseChange|quotient.*[Ff]ullLevel|[Rr]igidification.*[Ll]ift`
- `FakeEllipticCurve.*(baseChange|quotient|rebase)|exists.*(quotient|rebase)`
- `isStableUnderBaseChange|finrank_pullback_snd|mkₐ`
- `structure AbelianSchemePropertyBundle`
- `p07_full_level_quotient_857cd4d38c|p07_curve_ring_equiv_857cd4d38c|p07_rigidification_reduction_857cd4d38c`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/nodes/root/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/project/Definitions/Def_CerednikDrinfeld_QMModuli.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/project/Definitions/Def_CerednikDrinfeld_QMFormalModuleOf.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/project/Definitions/Def_CerednikDrinfeld_QMFineModuli.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/project/Definitions/Def_CerednikDrinfeld_QMRigidification.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/project/Definitions/Def_CerednikDrinfeld_QMIsogeny.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/project/Definitions/Def_CerednikDrinfeld_RigidifiedPairClassModel.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/project/Definitions/Def_JacJ1Iface.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/project/Definitions/Def_AlgebraicGeometry_RelativeGroupLaw.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/mathlib/Mathlib/AlgebraicGeometry/Morphisms/Smooth.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/mathlib/Mathlib/AlgebraicGeometry/Morphisms/Proper.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/mathlib/Mathlib/AlgebraicGeometry/Morphisms/ClosedImmersion.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/mathlib/Mathlib/AlgebraicGeometry/Morphisms/FlatRank.lean`
- `/tmp/p07_decomposition_current_check.lean`
- `/tmp/p07_decomposition_current_type_and_axiom_check.log`
- `/tmp/p07_decomposition_current_unchanged_submission.log`

The project and mathlib snapshots are clean at the manifest revisions 73257f1e32d99b75813b037f28a5cf45a2db886d and db584cd6d46c92f209a44c0f1c829460d327499d. Ripgrep is unavailable; the recorded search expressions were searched with grep after the failed rg attempt. No reusable fake-elliptic-curve quotient or rebase construction matched the searches in Definitions and P2M. The model file already supplies qmap_comp_mk, quotEquiv_comp_mk, and Pt.ext'. The inspected definitions specify all curve, full-level, isogeny, and rigidification fields used below. The DAG contains only the root; the three identifiers and exact types below agree with the existing proposals, and no corresponding Lean declaration was found. All three types elaborate against Submission's pinned definition imports. Reflexivity checks verify that the inferred quotient O-algebra map is q composed with the original algebra map and that mkₐ has underlying ring homomorphism mk. The audited structures, quotient identities, extensionality lemma, and four cited geometric library results depend only on propext, Classical.choice, and Quot.sound. However, unchanged Submission.lean fails on unknown attribute references AlgebraicGeometry.Scheme.Hom.opensMapFinal, GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase, and RegularLocalRingQuotientAscent.dualNumberFst_apply. Thus the literal import Submission gate has not passed; these diagnostic checks are not comparator acceptance.


## Acceptance

The exact contract must pass the machine comparator and an independent reviewer's comparator rerun, without changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: Pending

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
