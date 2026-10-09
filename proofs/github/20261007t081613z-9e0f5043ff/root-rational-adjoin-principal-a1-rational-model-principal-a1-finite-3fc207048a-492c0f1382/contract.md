<!-- theorem-id: fermat-p06/root.rational_adjoin_principal-a1.rational_model_principal-a1.finite_place_model-a1.normalized_orders-a1.fraction_unit_criterion-a1 -->

## Theorem `Submission.p06_9e0f5043ff_fno_fraction_isunit`

Let K and F be fields with a K-algebra structure on F, let x in F be transcendental over K, and let q in K[T] be monic and irreducible. Let v : AlgebraicCurve.Place K F satisfy, for every f in F, f belongs to A = v.toValuationSubring if and only if f = a(x)/b(x) for some polynomials a,b with q not dividing b. For all a,b in K[T] and z in A, if q does not divide b and the image of z in F equals a(x)/b(x), then z is a unit of A if and only if q does not divide a. No fraction-generation hypothesis on F is assumed.

Node: `root.rational_adjoin_principal-a1.rational_model_principal-a1.finite_place_model-a1.normalized_orders-a1.fraction_unit_criterion-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/6

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/108

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p06_9e0f5043ff_fno_fraction_isunit`

```lean
∀ (K F : Type*) [Field K] [Field F] [Algebra K F] (x : F), Transcendental K x → ∀ q : Polynomial K, q.Monic → Irreducible q → ∀ v : AlgebraicCurve.Place K F, (∀ f : F, f ∈ v.toValuationSubring ↔ ∃ a b : Polynomial K, ¬ q ∣ b ∧ f = Polynomial.aeval x a / Polynomial.aeval x b) → ∀ (a b : Polynomial K) (z : v.toValuationSubring), ¬ q ∣ b → (z : F) = Polynomial.aeval x a / Polynomial.aeval x b → (IsUnit z ↔ ¬ q ∣ a)
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
- Child DAG node: `root.rational_adjoin_principal-a1.rational_model_principal-a1.finite_place_model-a1.normalized_orders-a1.fraction_unit_criterion-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix all the stated data, write R = K[T], A = v.toValuationSubring, and e(r) = r(x), and identify elements of A with their images in F when computing. Transcendence makes the ring homomorphism e injective: e(r) = 0 forces r = 0, and applying this to a difference proves injectivity. In particular, nonzero polynomials have nonzero evaluations. The irreducible polynomial q is nonzero and not a unit.
2. The polynomial q is prime. Indeed, if q does not divide r, put d = gcd(q,r). Since d divides q and q is irreducible, either d is a unit or d is associated to q. The latter case would imply q divides r, since d divides r. Thus d is a unit. The Euclidean algorithm, followed by multiplication by the inverse of d, gives u q + t r = 1 for some u,t in R. If q divides r s, multiplying this identity by s expresses s as a sum of two multiples of q, so q divides s. Applying this when q does not divide r proves that q dividing r s always forces q to divide r or s.
3. Fix a,b,z satisfying the two final hypotheses. Since q does not divide b and every polynomial divides zero, b is nonzero, hence e(b) is nonzero. First assume q does not divide a. The same reasoning makes e(a) nonzero. By the membership criterion the fraction e(b)/e(a) belongs to A; call the resulting element w. In F the given representation of z yields z w = (e(a)/e(b))(e(b)/e(a)) = 1 and w z = 1. The inclusion A into F is injective and preserves multiplication and one, so both identities hold in A. The pair z,w therefore defines a unit of A with value z.
4. Conversely, assume z is a unit of A and choose its inverse w in A. Applying the membership criterion to the image of w gives c,d in R with q not dividing d and w = e(c)/e(d). Thus d and e(d) are nonzero. The equality z w = 1 in F, together with the representations of z and w, gives e(a)e(c) = e(b)e(d) after multiplication by the nonzero denominator e(b)e(d). Since e is a ring homomorphism and is injective, a c = b d.
5. If q divided a, it would divide a c, hence b d. Primality from step 2 would force q to divide b or d, contradicting the two denominator conditions. Therefore q does not divide a. This proves the reverse implication and hence the stated equivalence.

## Key steps

1. Use transcendence to obtain injectivity of evaluation and nonvanishing of evaluated denominators.
2. Prove primality of q using the polynomial gcd and Bezout identity.
3. For a numerator not divisible by q, use the reversed fraction as an inverse in the valuation ring.
4. For a unit, represent its inverse with a permitted denominator and derive ac = bd by cross multiplication and injectivity.
5. Use primality and the two denominator conditions to exclude q dividing the numerator.

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

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/315

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
