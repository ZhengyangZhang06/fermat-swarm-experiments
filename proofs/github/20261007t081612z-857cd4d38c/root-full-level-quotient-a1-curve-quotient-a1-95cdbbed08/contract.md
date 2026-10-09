<!-- theorem-id: fermat-p07/root.full_level_quotient-a1.curve_quotient-a1 -->

## Theorem `Submission.p07_flq_curve_quotient_857cd4d38c`

Let a,b ∈ ℚ, let Λ be a ℤ-submodule of QuaternionAlgebra ℚ a 0 b, let N ∈ ℕ, let S be a universe-zero commutative ring, and let J be an ideal of S. For every E : CerednikDrinfeld.QM.FakeEllipticCurve Λ N S, there exist EJ : CerednikDrinfeld.QM.FakeEllipticCurve Λ N (S/J) and a scheme morphism g : EJ.A → E.A such that FakeEllipticCurve.IsPullbackVia (Ideal.Quotient.mk J) E EJ g. No additional hypotheses on S, J, Λ, or N are imposed.

Node: `root.full_level_quotient-a1.curve_quotient-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/7

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/54

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/78, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/79, https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/80

## Lean problem

Declaration: `Submission.p07_flq_curve_quotient_857cd4d38c`

```lean
∀ {a b : ℚ} (Λ : Submodule ℤ (QuaternionAlgebra ℚ a 0 b)) (N : ℕ) (S : Type) [CommRing S] (J : Ideal S) (E : CerednikDrinfeld.QM.FakeEllipticCurve Λ N S), ∃ (EJ : CerednikDrinfeld.QM.FakeEllipticCurve Λ N (S ⧸ J)) (g : Quiver.Hom EJ.A E.A), CerednikDrinfeld.QM.FakeEllipticCurve.IsPullbackVia (Ideal.Quotient.mk J) E EJ g
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

- Parent DAG node: `root.full_level_quotient-a1`
- Child DAG node: `root.full_level_quotient-a1.curve_quotient-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Put T = S/J, q = Ideal.Quotient.mk J, and β = Spec(q). Form A_T = E.A ×_{Spec S} Spec T, with projections g : A_T → E.A and f_T : A_T → Spec T. For a universe-zero scheme W and t : W → Spec T, define B_t on points over t by Q ↦ Q ≫ g. Its target is the points of E over t ≫ β, since the pullback square commutes. Given such a point R, the compatibility R ≫ E.f = t ≫ β supplies the inverse point, namely the pullback lift of R and t. The projection equations show that applying B_t to this lift gives R. Conversely, the lift of Q ≫ g and t equals Q because both projections agree. Thus B_t is a bijection. For h : W' → W, associativity of composition gives B_{h≫t}(h ≫ Q) = h ≫ B_t(Q), so these bijections commute with precomposition.
2. Define multiplication, identity, and inverse on points of A_T by transporting E.L through B_t. Explicitly, the product of P,Q is B_t⁻¹(E.L.mul (t ≫ β) (B_t P) (B_t Q)), and identity and inverse are defined by the corresponding formulas. Applying the injective B_t to either side of each group-law equation reduces it to E.L.mul_assoc, E.L.one_mul, E.L.mul_one, or E.L.inv_mul_cancel. Applying it to the commutativity equation reduces that equation to E.comm. For multiplication naturality, apply the appropriate B after precomposition; step 1 and E.L.mul_natural identify both sides. This constructs a commutative RelativeGroupLaw L_T.
3. For m ∈ Λ, define a_m : A_T → A_T as the pullback lift of g ≫ E.act(m) and f_T. The compatibility follows from E.act_over. Its projection equations are a_m ≫ g = g ≫ E.act(m) and a_m ≫ f_T = f_T. Consequently B_t intertwines the induced action on points with E's action. For any proof that 1 belongs to Λ, compare both projections of a_1 and the identity: their first projections agree by E.act_one and their second projections are f_T. Thus act_one holds. For x,y ∈ Λ and a proof that xy ∈ Λ, the first projection of a_y ≫ a_x is g ≫ E.act(y) ≫ E.act(x), which equals g ≫ E.act(xy) by E.act_mul; its second projection is f_T. Pullback uniqueness gives a_{xy} = a_y ≫ a_x. Finally, applying B_t to act_hom and act_add reduces them respectively to E.act_hom and E.act_add, using step 2 and action compatibility. These arguments use exactly the membership hypotheses appearing in the action fields.
4. Since f_T is the base change of E.f, it is smooth and proper. The required pinned results are AlgebraicGeometry.smooth_isStableUnderBaseChange in Mathlib/AlgebraicGeometry/Morphisms/Smooth.lean:117 and AlgebraicGeometry.IsProper.isStableUnderBaseChange in Morphisms/Proper.lean:72, at mathlib revision db584cd6d46c92f209a44c0f1c829460d327499d. Their hypotheses follow from E.bundle.smooth and E.bundle.proper.
5. The map β is a closed immersion because q is surjective; this is also the pinned instance IsClosedImmersion.spec_of_quotient_mk in Morphisms/ClosedImmersion.lean. Its base change g is therefore a closed immersion and hence a topological embedding. The image of g is E.f⁻¹(range β), as expressed by AlgebraicGeometry.Scheme.Pullback.range_fst in PullbackCarrier.lean:328. In the quotient situation this also follows directly on an affine chart Spec D: its inverse image is Spec(D ⊗_S T), and D ⊗_S T ≅ D/JD by d ⊗ q(s) ↦ ds mod JD, with inverse d mod JD ↦ d ⊗ 1. The maps are well-defined, kill JD as required, and are inverse on pure tensors and residue classes. Thus the image consists precisely of points whose images in Spec S contain J. Now fix t ∈ Spec T and set s = β(t). Every point x in the fibre of E.f over s lies in the image of g. Its unique preimage y satisfies β(f_T(y)) = E.f(x) = β(t), and injectivity of β gives f_T(y) = t. Hence g restricts to a bijective embedding between the entire fibres over t and s, therefore a homeomorphism. The old fibre is nonempty and connected by E.bundle.connectedFibres, so the new one is also nonempty and connected. A homeomorphism induces an inclusion-preserving bijection on irreducible closed subsets and their strict chains; it therefore preserves topological Krull dimension. E.dim_fibre gives dimension two for the new fibre. Together with step 4 and the witness L_T from step 2, this proves the AbelianSchemePropertyBundle and dimension fields.
6. Verify act_trace. Fix an algebraically closed field K, a ring homomorphism α : T → K, an additive commutative group V with a finite K-module structure, and a parametrization τ of L_T-tangent vectors satisfying all the hypotheses in that field. Put α_S = α ∘ q. Use B on points over Spec K and Spec(DualNumber K), identifying their base maps by functoriality of Spec. These bijections commute with tangentZero and tangentScale, since both operations are precomposition. They preserve identity and multiplication by step 2. For a dual-number point Q, the equation defining IsTangentVector is an equality of K-points. Applying the injective B on K-points identifies this equation with the tangent equation for B(Q). Thus Q is tangent if and only if B(Q) is tangent. Define τ_S(v) = B(τ(v)). It is injective. Its range is exactly the tangent vectors: the forward implication follows from the tangent equivalence, and for the reverse implication lift a tangent point through B⁻¹, use the range hypothesis for τ, and apply B again. Preservation of multiplication proves the addition equation for τ_S, and compatibility with tangentScale proves its scalar equation. If m ∈ Λ and a K-linear map Φ satisfy the action equation for τ, step 3 gives the action equation for τ_S. Therefore E.act_trace, applied to α_S, V, τ_S, and the unchanged Φ, yields trace_K(Φ) = j for every integer j with m + star(m) = ((j : ℚ) : QuaternionAlgebra ℚ a 0 b). This is exactly the required trace condition for the new action.
7. Put c = E.lev ≫ E.f and form C_T = E.C ×_{Spec S} Spec T, with projections r : C_T → E.C and c_T : C_T → Spec T. Define lev_T : C_T → A_T as the lift of r ≫ E.lev and c_T. Its projections give lev_T ≫ g = r ≫ E.lev and lev_T ≫ f_T = c_T. The square with top r, left lev_T, right E.lev, and bottom g is a pullback: given R : W → E.C and Q : W → A_T with R ≫ E.lev = Q ≫ g, put t = Q ≫ f_T. The original square gives R ≫ c = t ≫ β, so R,t lift uniquely to C_T. The composite of this lift with lev_T equals Q by its two projections. Uniqueness follows from the two projections to E.C and Spec T. Hence lev_T is a base change of E.lev, and is a closed immersion by IsClosedImmersion.isStableUnderBaseChange, Morphisms/ClosedImmersion.lean:382.
8. For a point Q over t, prove that Q factors through lev_T if and only if B_t(Q) factors through E.lev. If Q = R_T ≫ lev_T, then Q ≫ g = R_T ≫ r ≫ E.lev, giving the forward implication. Conversely, suppose R ≫ E.lev = Q ≫ g. Composing with E.f gives R ≫ c = t ≫ β. Lift R,t to C_T; its composite with lev_T has first projection Q ≫ g and second projection t, so it equals Q by pullback uniqueness. This proves the reverse implication.
9. Transfer the level-subgroup equations using step 8. If P and Q factor through lev_T, their B-images factor through E.lev. E.lev_sub gives factorization of their product and of the inverse of the first point; preservation of multiplication and inverse under B and step 8 give the desired factorizations on A_T. E.lev_one and preservation of identity similarly give lev_one. Action compatibility and E.lev_stable give lev_stable. For every natural k, B preserves nsmulPt with parameter k: at zero this is preservation of identity, and at k+1 it follows from the defining recursion, the induction hypothesis, and preservation of multiplication. Apply this with k = N to a point factoring through lev_T. E.lev_torsion says that its B-image has N-fold sum equal to the identity; injectivity of B proves the same equation on A_T. This gives lev_torsion.
10. The structure morphism c_T = lev_T ≫ f_T is the base change of c. Finiteness, flatness, and local finite presentation are preserved under base change, as supplied by the pinned Morphisms/Finite.lean:60, Morphisms/Flat.lean:81, and Morphisms/FinitePresentation.lean:85. Concretely, a finite module on an affine chart becomes a module generated by the tensors of its finite generating family. Flatness follows from the natural identification W ⊗_T (D ⊗_S T) ≅ W ⊗_S D for a T-module W: restriction of scalars is exact, and tensoring with the original flat module D preserves exactness. A finite algebra presentation base changes by mapping its finitely many coefficients to T, giving local finite presentation. For t ∈ Spec T, AlgebraicGeometry.Scheme.Hom.finrank_pullback_snd in Morphisms/FlatRank.lean:157 gives c_T.finrank(t) = c.finrank(β(t)); its hypotheses are E.lev_flat and E.lev_finite. E.lev_rank therefore makes the new rank N².
11. Fix an algebraically closed K and α : T → K with (N : K) ≠ 0. Step 8 restricts B to an equivalence between points factoring through lev_T over α and points factoring through E.lev over α ∘ q. Let e₀ be the equivalence from ZMod N × ZMod N supplied by E.lev_fibre at α ∘ q. Compose e₀ with the inverse restricted B to obtain e_T. For x,y, applying B to e_T(x+y) gives e₀(x+y), which equals the product of e₀(x) and e₀(y). By step 2 this is also the B-image of the product of e_T(x) and e_T(y). Injectivity proves the required addition equation for e_T. Thus lev_fibre holds.
12. Assemble A_T, f_T, L_T, its commutativity and bundle witnesses, the action and trace data, and C_T with all the level fields just verified into EJ : FakeEllipticCurve Λ N T. The original pullback square, multiplication compatibility from step 2, action compatibility from step 3, and the forward implication of step 8 are precisely the four components of FakeEllipticCurve.IsPullbackVia q E EJ g. Thus EJ and g prove the stated existential conclusion.

## Key steps

1. Construct the scheme pullback and its natural bijections on relative points.
2. Transport the commutative group law and quaternion action through those bijections.
3. Use quotient closed immersions to identify entire topological fibres and preserve the abelian-scheme bundle and dimension.
4. Transport tangent parametrizations to verify the unchanged linear-map trace condition.
5. Base change the level subscheme and prove the two-way factorization criterion.
6. Transfer the subgroup, action-stability, and torsion fields.
7. Preserve finiteness, flatness, finite presentation, rank, and geometric level parametrizations.
8. Assemble the curve and the exact IsPullbackVia witness.

## Reference use

### local-project

Queries:
- `baseChange|pullback|structure RelativeGroupLaw|structure AbelianSchemePropertyBundle`
- `isStableUnderBaseChange|finrank_pullback_snd|isClosedImmersion_SpecMap|surjective`
- `FakeEllipticCurve|FullLevel|IsPullbackVia`
- `range_pullback|range.*pullback|pullback.*range|pullback.*preimage|image_preimage`
- `\b(sorry|admit|axiom)\b`
- `p07_flq_curve_quotient_857cd4d38c|p07_flq_full_level_pullback_857cd4d38c`
- `/mnt/data/zhengyang-workspace/fermat-example/.humanize/toolchains/lean-4.33.1-linux/bin/lean -DautoImplicit=false -DmaxHeartbeats=4000000 -DsynthInstance.maxHeartbeats=400000 -Dbackward.isDefEq.respectTransparency.types=false /tmp/p07-flq-contract-kgrows4p/TypesAgainstPrerequisites.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/project/Definitions/Def_CerednikDrinfeld_QMModuli.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/project/Definitions/Def_CerednikDrinfeld_QMFineModuli.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/project/Definitions/Def_CerednikDrinfeld_QMFormalModuleOf.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/project/Definitions/Def_AlgebraicGeometry_RelativeGroupLaw.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/project/Definitions/Def_JacJ1Iface.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/project/P2M`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/mathlib/Mathlib/AlgebraicGeometry/Morphisms/Smooth.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/mathlib/Mathlib/AlgebraicGeometry/Morphisms/Proper.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/mathlib/Mathlib/AlgebraicGeometry/Morphisms/ClosedImmersion.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/mathlib/Mathlib/AlgebraicGeometry/Morphisms/FlatRank.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/mathlib/Mathlib/AlgebraicGeometry/Morphisms/Finite.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/mathlib/Mathlib/AlgebraicGeometry/Morphisms/Flat.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/mathlib/Mathlib/AlgebraicGeometry/Morphisms/FinitePresentation.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/.humanize/github-theorem-prover/runs/20261007T081612Z-857cd4d38c/local-references/9bdf6c711efc6a89/mathlib/Mathlib/AlgebraicGeometry/PullbackCarrier.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p07/Submission.lean`
- `/tmp/p07-flq-contract-kgrows4p/Submission.log`
- `/tmp/p07-flq-contract-kgrows4p/Types.lean`
- `/tmp/p07-flq-contract-kgrows4p/TypesAgainstPrerequisites.lean`
- `/tmp/p07-flq-contract-kgrows4p/TypesAgainstPrerequisites.log`

The manifest pins project 73257f1e32d99b75813b037f28a5cf45a2db886d and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. The inspected definitions confirm every curve, full-level, and IsPullbackVia field. The cited base-change results occur at Smooth:117, Proper:72, ClosedImmersion:382, and FlatRank:157; the last requires only flatness and finiteness. PullbackCarrier:328 supplies Scheme.Pullback.range_fst. The P2M search returned no matching helpers, and neither proposed name appears in the inspected DAG or handoffs. Relevant definition files had no explicit axiom or admitted-proof matches. All 47 unchanged prerequisite modules compiled. Both proposed types checked without warnings against Submission's identical five imports, and quotient-ring instance synthesis returned Ideal.Quotient.commRing J. Transitive axiom checks of the three curve/full-level/pullback declarations, one_natural, and the queried smoothness, properness, closed-immersion, rank, and pullback-range results returned only propext, Classical.choice, and Quot.sound. However, literal import Submission validation is blocked: its existing attribute commands fail on AlgebraicGeometry.Scheme.Hom.opensMapFinal, GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase, and RegularLocalRingQuotientAscent.dualNumberFst_apply. No source was repaired or theorem acceptance claimed.


## Acceptance

The exact contract must pass the machine comparator and an independent reviewer's comparator rerun, without changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: Pending

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
