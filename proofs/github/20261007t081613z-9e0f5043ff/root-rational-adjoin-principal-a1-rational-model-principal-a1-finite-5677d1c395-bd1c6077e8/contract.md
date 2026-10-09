<!-- theorem-id: fermat-p06/root.rational_adjoin_principal-a1.rational_model_principal-a1.finite_place_classification-a1 -->

## Theorem `Submission.p06_9e0f5043ff_rmp_finite_place_classification`

Let K be any field, M = FractionRing (Polynomial K) with its canonical K-algebra, and t the image of Polynomial.X in M. If v is a project place of M over K and t belongs to its valuation subring, then there exists a monic irreducible polynomial q ∈ K[T] such that, for every f ∈ M, f belongs to that valuation subring exactly when f = a(t)/b(t) for polynomials a,b with q not dividing b.

Node: `root.rational_adjoin_principal-a1.rational_model_principal-a1.finite_place_classification-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/6

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/43

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p06_9e0f5043ff_rmp_finite_place_classification`

```lean
∀ (K : Type*) [Field K] (v : AlgebraicCurve.Place K (FractionRing (Polynomial K))), algebraMap (Polynomial K) (FractionRing (Polynomial K)) Polynomial.X ∈ v.toValuationSubring → ∃ q : Polynomial K, q.Monic ∧ Irreducible q ∧ (∀ f : FractionRing (Polynomial K), f ∈ v.toValuationSubring ↔ ∃ a b : Polynomial K, ¬ q ∣ b ∧ f = algebraMap (Polynomial K) (FractionRing (Polynomial K)) a / algebraMap (Polynomial K) (FractionRing (Polynomial K)) b)
```

### Frozen project context

`Fermat/Thm_AlgebraicCurve_hasPrincipalDivisors_of_transcendental.lean` at `956e8c600d8b95b46948ae5e37b13930b5f3d06b` supplies the original imports, definitions and root contract. Child hypotheses are stated above; prerequisite declarations are linked in their issues.

```lean
/-
Copyright 2026 Anthropic, PBC. Licensed under Apache-2.0; see LICENSE.
Source: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_AlgebraicCurve_hasPrincipalDivisors_of_transcendental.lean
Modified: replaced the proof with sorry and removed P2M proof imports.
Requires the upstream Definitions modules and their dependencies.
-/

import Definitions.Def_AlgebraicCurve_PlacesOverDVR
attribute [-instance] AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy
attribute [-simp] AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul
attribute [-simp] AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply

open AlgebraicCurve
theorem AlgebraicCurve.hasPrincipalDivisors_of_transcendental (K : Type*) [Field K] [CharZero K] {F : Type*} [Field F]
    [Algebra K F] (x : F) (hx : Transcendental K x)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F] : HasPrincipalDivisors K F := by
  sorry
```

## Natural-language proof

Reviewed mathematical argument; formal verification state: `proved`.

# Parent-supplied natural-language proof

- Parent DAG node: `root.rational_adjoin_principal-a1.rational_model_principal-a1`
- Child DAG node: `root.rational_adjoin_principal-a1.rational_model_principal-a1.finite_place_classification-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix K, M, t and v as stated, and put V = v.toValuationSubring. The canonical map K[T] → M is injective. Because V contains K and t, it contains the image of every polynomial. Thus this map factors through a ring homomorphism K[T] → V.
2. Contract the maximal ideal of the local ring V along that homomorphism, obtaining an ideal p of K[T]. It is proper because one does not belong to the maximal ideal, and prime because the maximal ideal is prime.
3. The ideal p is nonzero. Otherwise every nonzero polynomial would map outside the maximal ideal of V and therefore to a unit of V. Every element of M is a polynomial fraction with nonzero denominator, so every element of M would then belong to V. This contradicts the properness field of the project place.
4. Choose a nonzero element q₀ of p with least degree. Dividing any element of p by q₀ gives a remainder still in p with smaller degree; minimality forces that remainder to be zero. Therefore p = (q₀). Multiplying q₀ by the inverse of its leading coefficient gives a monic generator q. This generator is nonzero and is not a unit since p is proper. It is irreducible: if q = ab, primality of p puts a or b in (q). If a = qc, cancellation of the nonzero q in q = qcb gives cb = 1, so b is a unit; the other case is symmetric.
5. If q does not divide b, then b does not belong to p. Consequently b(t) is a unit of V. Since a(t) belongs to V for every polynomial a, every fraction a(t)/b(t) with q not dividing b belongs to V. This proves one direction of the required characterization.
6. For the converse, zero has the permitted representation 0/1. Let f ∈ V be nonzero and write f = a(t)/b(t) with a,b nonzero. Repeated division by the positive-degree polynomial q terminates, giving a = q^r a₀ and b = q^s b₀, with q dividing neither a₀ nor b₀. By step 5, both a₀(t) and b₀(t) are units of V. Hence u = a₀(t)/b₀(t) is a V-unit and f = u q(t)^(r−s), with the exponent interpreted in ℤ.
7. The element q(t) belongs to the maximal ideal of V by the definition of p. If r < s, then f u⁻¹ q(t)^(s−r−1) = q(t)⁻¹ belongs to V. This would make q(t) a unit, contradicting its membership in the maximal ideal. Thus r ≥ s. The expression f = (q^(r−s)a₀)(t)/b₀(t) now has a denominator not divisible by q. This proves the reverse implication for every f. The monicity and irreducibility established in step 4 complete the statement.

## Key steps

1. Embed K[T] into the valuation subring using membership of t.
2. Contract the maximal ideal and prove that the contraction is proper, prime, and nonzero.
3. Use least-degree division and monic normalization to obtain an irreducible generator q.
4. Show that denominators not divisible by q become units.
5. Factor powers of q from a fraction and exclude a negative exponent using the maximal ideal.
6. Deduce the exact localization membership characterization.

## Reference use

### local-project

Queries:
- `HasPrincipalDivisors|namespace RationalFunctionField|structure Place|def ord|def deg|ord_unit_smul_zpow|placeOf|infinity`
- `namespace RationalFunctionField|heightOneSpectrumOfIrreducible|deg_placeOfPoint`
- `eq_of_le|eq_or_eq_top|overring|isUnit_iff|natDegree.*factor|sum.*natDegree|natDegree.*sum|multiplicity`
- `p06_9e0f5043ff_rmp_finite_place_model|p06_9e0f5043ff_rmp_finite_place_classification|p06_9e0f5043ff_rmp_infinity_place`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/project/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/project/Definitions/Def_AlgebraicCurve_PlacesOverDVR.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/Valuation/ValuationSubring.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/Polynomial/UniqueFactorization.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/FieldTheory/RatFunc/AsPolynomial.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-rational-adjoin-principal-a1-rational-model-principal-a1/decomposition-typecheck/CheckTypes.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-rational-adjoin-principal-a1-rational-model-principal-a1/decomposition-typecheck/CheckTypes.interface-check.log`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-rational-adjoin-principal-a1-rational-model-principal-a1/decomposition-typecheck/Submission.frozen-source-check.log`

The DAG identifies the supplied statement as the depth-2 rational_model_principal child; the frozen root remains unchanged. DivisorClassGroup supplies Place, its DVR instance, normalized-order formulas, residue-field degree, degree_single, and HasPrincipalDivisors.exists_divisor. Mathlib supplies polynomial unique factorization and the proper-overring theorem ValuationSubring.eq_of_le_of_ne_top. Searches for the named RationalFunctionField constructions found only attribute references in specification files, not reusable construction definitions. Proposed names have no active-DAG or searched-source collisions. Both snapshot revisions and all nine dependencies match their manifests and have clean tracked files. Relevant project sources match the cached interface byte-for-byte. All three proposed types elaborate without warnings against the isolated import-only Submission interface. Definitional checks verify the canonical K-algebra through Polynomial.C and the residue-field algebra underlying Place.deg. Audited supporting declarations use only propext, Classical.choice, and Quot.sound. However, a fresh check of actual Submission.lean fails on three pre-existing unknown attribute targets: AlgebraicCurve.IsCurveOver.instNontrivialKaehler, AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply, and AlgebraicCurve.SemilinearAut.coe_torsion_smul. Actual import Submission validation remains an activation blocker; no comparator acceptance is claimed.


## Acceptance

The exact contract must pass the machine comparator and an independent reviewer's comparator rerun, without changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: Pending

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
