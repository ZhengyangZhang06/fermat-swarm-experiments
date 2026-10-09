<!-- theorem-id: fermat-p07/root.rigidification_reduction-a1 -->

## Theorem `Submission.p07_rigidification_reduction_857cd4d38c`

Let a,b be rational numbers, Λ a Z-submodule of QuaternionAlgebra Q a 0 b, and r,N natural numbers. Let O,Onr,S be commutative rings of universe zero with O-algebra structures on Onr and S. Fix π : O, A₀ : FakeEllipticCurve Λ N (Onr/(algebraMap O Onr π)), ψ : Onr →ₐ[O] S, and E : FakeEllipticCurve Λ N S. Put J = Ideal.span {algebraMap O S π}, T = S/J with its induced O-algebra structure, and qₐ = Ideal.Quotient.mkₐ O J. Let V : FakeEllipticCurve Λ N T, g : V.A → E.A, and hg : FakeEllipticCurve.IsPullbackVia qₐ.toRingHom E V g. For every σ : Rigidification r π A₀ (qₐ.comp ψ) V, there exists ρ : Rigidification r π A₀ ψ E such that ρ.d = σ.d and Rigidification.IsPullbackVia qₐ g hg ρ σ.

Node: `root.rigidification_reduction-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/7

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/7

Prerequisites: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/55

Decomposition children: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/195, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/196

## Lean problem

Declaration: `Submission.p07_rigidification_reduction_857cd4d38c`

```lean
∀ {a b : ℚ} (Λ : Submodule ℤ (QuaternionAlgebra ℚ a 0 b)) (r N : ℕ) (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr] (A₀ : CerednikDrinfeld.QM.FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π})) (S : Type) [CommRing S] [Algebra 𝒪 S] (ψ : Onr →ₐ[𝒪] S) (E : CerednikDrinfeld.QM.FakeEllipticCurve Λ N S) (V : CerednikDrinfeld.QM.FakeEllipticCurve Λ N (S ⧸ Ideal.span {algebraMap 𝒪 S π})) (g : Quiver.Hom V.A E.A) (hg : CerednikDrinfeld.QM.FakeEllipticCurve.IsPullbackVia (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 S π})) E V g) (σ : CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification r π A₀ ((Ideal.Quotient.mkₐ 𝒪 (Ideal.span {algebraMap 𝒪 S π})).comp ψ) V), ∃ ρ : CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification r π A₀ ψ E, ρ.d = σ.d ∧ CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.IsPullbackVia (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {algebraMap 𝒪 S π})) g hg ρ σ
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
- Child DAG node: `root.rigidification_reduction-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Put s = algebraMap O S π, J = (s), T = S/J, and q : S → T for the quotient. Its induced O-algebra map sends a to q(algebraMap O S a). Therefore π_T = algebraMap O T π = q(s) = 0, since s lies in J. Set U = T/(π_T), and let k₀ : T → U be the quotient. The map e : U → T sending [t] to t is well-defined because (π_T) is the zero ideal. It preserves all ring operations, and e ∘ k₀ = id_T and k₀ ∘ e = id_U. Thus k₀ is the underlying map of a ring isomorphism k : T ≃+* U with inverse e. Write k* and e* for the associated scheme morphisms.
2. Let λ : Onr/(π_Onr) → T be the residue map induced by ψ, and let λ' : Onr/(π_Onr) → U be induced by qₐ.comp ψ. On the class of a in Onr, λ' gives k₀(q(ψ(a))); therefore λ' = k₀ ∘ λ by surjectivity of the quotient map. The residue map q̄ : T → U induced by q likewise sends q(s₀) to k₀(q(s₀)) for every s₀ in S. Since q is surjective, q̄ = k₀. These are equalities of ring homomorphisms; proof fields in their quotient-map definitions do not affect them.
3. Apply the sibling theorem curve_ring_equiv to k and σ.Eb, and separately to k and σ.Ab. Obtain curves B,A over T and scheme isomorphisms i_b : σ.Eb.A ≅ B.A and i_A : σ.Ab.A ≅ A.A. Their forward maps satisfy IsPullbackVia over k₀, and their inverse maps satisfy IsPullbackVia over e. The inverse squares identify B-points over t with σ.Eb-points over t ≫ e*, by composition with i_b.inv; similarly for A. These are bijections, preserve multiplication and actions, and preserve level membership in both directions: the inverse pullback predicates give one implication and the forward predicates give the other after cancelling the isomorphisms and the inverse base maps.
4. Define the prospective rigidification by ρ.Eb = B, ρ.Ab = A, ρ.gb = i_b.inv ≫ σ.gb ≫ g, ρ.gA = i_A.inv ≫ σ.gA, ρ.d = σ.d, ρ.φ = i_b.inv ≫ σ.φ ≫ i_A.hom, and ρ.φ' = i_A.inv ≫ σ.φ' ≫ i_b.hom. These expressions have exactly the required sources and targets. The remaining steps verify each proof field of Rigidification.
5. Pullback squares compose: to lift a compatible pair into a composite square, first use the lower square's unique lift and then the upper square's unique lift; the two uniqueness statements also prove uniqueness for the composite. Apply this to the inverse square for i_b, σ.isPullback_Eb, and hg. Their base morphisms compose as e* ≫ k* ≫ q* = q*. Thus the composite is the required pullback square for ρ.gb. Multiplication compatibility follows by applying the three compatibility equations successively. The three action equations compose by associativity. For level factorization, take the witness through σ.Eb.lev supplied by the first predicate, then through V.lev supplied by the second, and finally through E.lev supplied by hg. This verifies all components of FakeEllipticCurve.IsPullbackVia q E B ρ.gb.
6. Compose the inverse square for i_A with σ.isPullback_Ab. Its base morphism is e* ≫ (λ')* = e* ≫ k* ≫ λ* = λ*, by step 2. Consequently this is the required pullback square for ρ.gA. Applying the two multiplication equations, composing the two action equations, and composing their level-factorization witnesses proves all remaining components of FakeEllipticCurve.IsPullbackVia λ A₀ A ρ.gA.
7. The inverse pullback equation gives i_b.inv ≫ σ.Eb.f = B.f ≫ e*, and the forward equation gives i_A.hom ≫ A.f = σ.Ab.f ≫ k*. Using σ.φ_over and e* ≫ k* = id yields ρ.φ ≫ A.f = B.f. Using the over-base equation for σ.φ' gives ρ.φ' ≫ B.f = A.f in the same way. Thus both isogeny maps are over Spec T, and the first equality supplies ρ.φ_over.
8. For a point Q of B over t, the image of ρ.φ(Q) under the point bijection for A is σ.φ applied to the image of Q under the point bijection for B. On underlying morphisms this is the cancellation i_A.hom ≫ i_A.inv = id. The corresponding statement for ρ.φ' follows by cancelling i_b.hom ≫ i_b.inv. Since the two point bijections preserve multiplication and are injective, σ's two multiplication-preservation equations imply those for ρ.φ and ρ.φ'. For action equivariance, substitute their definitions and use the action equations for i_b.inv, i_A.hom, i_A.inv, i_b.hom, and the two action equations for σ. Associativity gives precisely B.act(m) ≫ ρ.φ = ρ.φ ≫ A.act(m) and its reverse-map analogue.
9. Fix any membership witness for the scalar r^σ.d in Λ. Cancellation of i_A.hom ≫ i_A.inv gives ρ.φ ≫ ρ.φ' = i_b.inv ≫ (σ.φ ≫ σ.φ') ≫ i_b.hom. The old isogeny-pair equation replaces the middle composite by σ.Eb's action of that scalar. Action compatibility and i_b.inv ≫ i_b.hom = id turn the result into B's action of the same scalar. Cancelling i_b.hom ≫ i_b.inv in the other order proves ρ.φ' ≫ ρ.φ equals A's scalar action. Since ρ.d = σ.d by definition, these are the exact degree conditions in IsIsogenyPair. Together with steps 7 and 8, they establish ρ.isIsogenyPair.
10. Suppose a B-point factors through B.lev. The level equivalence of step 3 sends it to a point factoring through σ.Eb.lev. Apply σ.preservesLevel to obtain a factorization through σ.Ab.lev, then send it forward through i_A.hom to obtain a factorization through A.lev. The resulting point is its image under ρ.φ by definition. Hence ρ.preservesLevel holds. Steps 5–10 verify every proof field, so ρ is a rigidification with ρ.d = σ.d.
11. To prove the asserted rigidification pullback relation, take ub = i_b.hom and uA = i_A.hom. Its residue map is k₀ by step 2, so the two curve IsPullbackVia conditions are exactly the forward conditions supplied in step 3. The equation ub ≫ ρ.gb = σ.gb ≫ g follows by cancelling i_b.hom ≫ i_b.inv. Similarly uA ≫ ρ.gA = σ.gA. The degree equation σ.d = ρ.d is reflexive. Finally, ub ≫ ρ.φ = σ.φ ≫ i_A.hom = σ.φ ≫ uA, again by cancellation. These are all conjuncts in Rigidification.IsPullbackVia qₐ g hg ρ σ. Thus ρ is the required witness.

## Key steps

1. Show the second quotient is quotient by zero and construct its canonical ring isomorphism.
2. Identify both induced residue maps by evaluation on quotient representatives.
3. Transport the two special-fibre curves using curve_ring_equiv.
4. Define the lifted rigidification by conjugating its isogeny maps.
5. Compose pullback squares and their multiplication, action, and level compatibilities.
6. Verify the over-base, isogeny-pair, and level-preservation fields.
7. Use the forward transport isomorphisms as witnesses of the exact rigidification pullback relation.

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

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/741

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
