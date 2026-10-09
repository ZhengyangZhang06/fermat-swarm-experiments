<!-- theorem-id: fermat-p06/root.rational_adjoin_principal-a1.rational_model_principal-a1.finite_place_model-a1.normalized_orders-a1.irreducible_evaluation-a1 -->

## Theorem `Submission.p06_9e0f5043ff_fno_irreducible_aeval`

Let K and F be fields with a K-algebra structure on F, let x in F be transcendental over K, and let q in K[T] be monic and irreducible. Let v : AlgebraicCurve.Place K F satisfy, for every f in F, f belongs to A = v.toValuationSubring if and only if f = a(x)/b(x) for some polynomials a,b with q not dividing b. Then there exists pi in A whose image in F is q(x) and which is irreducible in A. No fraction-generation hypothesis on F is assumed.

Node: `root.rational_adjoin_principal-a1.rational_model_principal-a1.finite_place_model-a1.normalized_orders-a1.irreducible_evaluation-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/6

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/108

Prerequisites: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/121

Decomposition children: None

## Lean problem

Declaration: `Submission.p06_9e0f5043ff_fno_irreducible_aeval`

```lean
∀ (K F : Type*) [Field K] [Field F] [Algebra K F] (x : F), Transcendental K x → ∀ q : Polynomial K, q.Monic → Irreducible q → ∀ v : AlgebraicCurve.Place K F, (∀ f : F, f ∈ v.toValuationSubring ↔ ∃ a b : Polynomial K, ¬ q ∣ b ∧ f = Polynomial.aeval x a / Polynomial.aeval x b) → ∃ π : v.toValuationSubring, (π : F) = Polynomial.aeval x q ∧ Irreducible π
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

- Parent DAG node: `root.rational_adjoin_principal-a1.rational_model_principal-a1.finite_place_model-a1.normalized_orders-a1`
- Child DAG node: `root.rational_adjoin_principal-a1.rational_model_principal-a1.finite_place_model-a1.normalized_orders-a1.irreducible_evaluation-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix all the stated data, write R = K[T], A = v.toValuationSubring and e(r) = r(x). Transcendence makes e injective. The irreducible polynomial q is nonzero and not a unit. Hence q does not divide 1: a factorization 1 = q r would make q a unit. The membership criterion applied to e(r) = e(r)/e(1) shows that e(r) belongs to A for every polynomial r. In particular let pi be e(q) with this membership proof. Its image is e(q), and pi is nonzero because q is nonzero and e is injective.
2. Apply the sibling fraction_unit_criterion to pi, numerator q and denominator 1. The required fraction identity follows from e(1) = 1 and the denominator condition was proved in step 1. It gives IsUnit(pi) if and only if q does not divide q. Since q divides itself, pi is not a unit.
3. The polynomial q is prime. To verify this directly, if q does not divide r, the gcd of q and r divides q and r. Irreducibility of q forces that gcd to be a unit, since otherwise it is associated to q and q would divide r. Bezout's identity then gives u q + t r = 1. Multiplying by s shows that q dividing r s forces q to divide s. This proves the prime-divisor property for all products.
4. Consider any factorization pi = y z in A. Apply the membership criterion to the images of y and z to choose a,b,c,t in R with q dividing neither b nor t, y = e(a)/e(b), and z = e(c)/e(t). Both b and t are nonzero because q divides zero, so both denominator evaluations are nonzero by injectivity of e.
5. The factorization in F reads e(q) = (e(a)/e(b))(e(c)/e(t)). Multiplying by e(b)e(t) gives e(a c) = e(q b t). Injectivity of e yields a c = q b t.
6. Suppose q divided both a and c. Write a = q a1 and c = q c1. The identity in step 5 becomes q(q a1 c1) = q(b t). Since R is a domain and q is nonzero, cancellation gives q a1 c1 = b t. Thus q divides b t. Primality from step 3 forces q to divide b or t, contradicting the chosen representations. Consequently q does not divide a or q does not divide c.
7. In the first case, apply fraction_unit_criterion to y with its representation a/b and denominator condition to obtain that y is a unit. In the second case, apply that criterion to z with its representation c/t to obtain that z is a unit. Every factorization of pi therefore has a unit factor. Together with step 2 this proves Irreducible(pi). The element pi constructed in step 1, its stated image, and this irreducibility give the required existential conclusion.

## Key steps

1. Use denominator 1 to place every polynomial evaluation in A and construct pi mapping to q(x).
2. Apply the sibling unit criterion to q/1 to prove that pi is a nonunit.
3. Establish the prime-divisor property of q by the gcd and Bezout argument.
4. Represent both factors of pi by permitted fractions and derive ac = qbt.
5. Exclude q dividing both numerators by cancellation and primality.
6. Apply the sibling unit criterion to obtain a unit factor, proving irreducibility.

## Reference use

### local-project

Queries:
- `ord_coe_irreducible|ord_coe_unit|structure Place|def ord|isUnit_iff|theorem ord`
- `aeval_injective|transcendental_iff_injective|theorem.*isUnit.*inv|isUnit_iff.*inv|inv_mem.*isUnit`
- `theorem Irreducible.prime|lemma Irreducible.prime`
- `p06_9e0f5043ff_fno_fraction_isunit|p06_9e0f5043ff_fno_irreducible_aeval|ord.*aeval|aeval.*ord|Irreducible.*aeval|aeval.*Irreducible`
- `p06_9e0f5043ff_fno_fraction_isunit|p06_9e0f5043ff_fno_irreducible_aeval`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/project/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/Algebraic/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/Algebra/Prime/Defs.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-rational-adjoin-principal-a1-rational-model-principal-a1-finite-654f5e977f/decomposition-typecheck/CheckTypes.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-rational-adjoin-principal-a1-rational-model-principal-a1-finite-654f5e977f/decomposition-typecheck/CheckTypes.interface-check.log`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-rational-adjoin-principal-a1-rational-model-principal-a1-finite-654f5e977f/decomposition-typecheck/Submission.frozen-source-check.log`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-rational-adjoin-principal-a1-rational-model-principal-a1-finite-654f5e977f/decomposition-typecheck/provenance-check.json`

The snapshot supplies Place.ord_coe_unit, Place.ord_coe_irreducible, transcendental_iff_injective, and Irreducible.prime. The searched snapshot sources contained no matching evaluation-order theorem or proposed-name collision; neither proposed identifier is reserved in the inspected DAG. Both snapshot revisions and all nine dependencies match their manifests and have clean tracked files. Both proposed types elaborate without warnings against the existing isolated import-only Submission interface; definitional checks confirm canonical valuation-subring multiplication. Audited supporting declarations use only propext, Classical.choice, and Quot.sound. However, actual Submission.lean still fails on three pre-existing unknown attribute targets: AlgebraicCurve.IsCurveOver.instNontrivialKaehler, AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply, and AlgebraicCurve.SemilinearAut.coe_torsion_smul. Actual import validation remains required before activation; interface checks are not comparator acceptance.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/330

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
