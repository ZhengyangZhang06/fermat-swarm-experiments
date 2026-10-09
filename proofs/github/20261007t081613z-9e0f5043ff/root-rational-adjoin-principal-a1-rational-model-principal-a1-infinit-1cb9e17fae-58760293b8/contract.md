<!-- theorem-id: fermat-p06/root.rational_adjoin_principal-a1.rational_model_principal-a1.infinity_place-a1.reciprocal_presentation-a1 -->

## Theorem `Submission.p06_9e0f5043ff_inf_reciprocal_presentation`

Let K be any field, let M = FractionRing (Polynomial K) with its canonical K-algebra, let t be the image of Polynomial.X in M, and put s = t⁻¹. Then s is transcendental over K, and every f ∈ M admits polynomials a,b ∈ K[T] with b ≠ 0 and f = a(s)/b(s).

Node: `root.rational_adjoin_principal-a1.rational_model_principal-a1.infinity_place-a1.reciprocal_presentation-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/6

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/75

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p06_9e0f5043ff_inf_reciprocal_presentation`

```lean
∀ (K : Type*) [Field K], Transcendental K ((algebraMap (Polynomial K) (FractionRing (Polynomial K)) Polynomial.X)⁻¹) ∧ (∀ f : FractionRing (Polynomial K), ∃ a b : Polynomial K, b ≠ 0 ∧ f = Polynomial.aeval ((algebraMap (Polynomial K) (FractionRing (Polynomial K)) Polynomial.X)⁻¹) a / Polynomial.aeval ((algebraMap (Polynomial K) (FractionRing (Polynomial K)) Polynomial.X)⁻¹) b)
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

- Parent DAG node: `root.rational_adjoin_principal-a1.rational_model_principal-a1.infinity_place-a1`
- Child DAG node: `root.rational_adjoin_principal-a1.rational_model_principal-a1.infinity_place-a1.reciprocal_presentation-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix K and write M = Frac(K[T]), ι : K[T] → M for the fraction-ring embedding, t = ι(T), and s = t⁻¹. Since K[T] is a domain, ι is injective. The canonical K-algebra on M sends c to ι(C(c)); consequently polynomial evaluation at t agrees with ι, as follows by expanding each polynomial into its monomials. Thus p(t) ≠ 0 whenever p ≠ 0. In particular t ≠ 0, s ≠ 0, and s⁻¹ = t.
2. For a nonzero polynomial p of degree d, define P(T) = Σ_{i=0}^d C(p_i)T^(d−i). Its constant coefficient is p_d, the nonzero leading coefficient of p, so P ≠ 0. Expanding and using t ≠ 0 gives t^d p(s) = Σ_{i=0}^d p_i t^(d−i) = P(t). Injectivity from step 1 gives P(t) ≠ 0, hence p(s) ≠ 0. Therefore no nonzero polynomial vanishes at s, which proves Transcendental K s.
3. The element 0 has the required representation 0(s)/1(s), with denominator polynomial 1 ≠ 0. Now fix f ≠ 0. By the definition of the fraction field, f = a(t)/b(t) for polynomials a,b with b ≠ 0. Necessarily a ≠ 0, since otherwise f = 0.
4. Put d = a.natDegree and e = b.natDegree, and define their reversed polynomials A(T) = Σ_{i=0}^d C(a_i)T^(d−i) and B(T) = Σ_{i=0}^e C(b_i)T^(e−i). Their constant coefficients are the respective nonzero leading coefficients, so A and B are nonzero. Since t = s⁻¹, expansion gives A(s) = s^d a(t) and B(s) = s^e b(t). Since s ≠ 0, these identities imply f = s^((e : ℤ)−(d : ℤ)) A(s)/B(s). Also B(s) ≠ 0 by step 2.
5. If d ≤ e, take numerator polynomial X^(e−d)A and denominator polynomial B. Evaluation of their quotient is exactly the expression in step 4, and B ≠ 0.
6. If e < d, take numerator polynomial A and denominator polynomial X^(d−e)B. Its evaluation again gives the expression in step 4. This denominator polynomial is nonzero because K[T] is a domain, X is nonzero, and B is nonzero. Its evaluation at s is also nonzero by step 2. These two cases give the required representation for every f, completing both conclusions.

## Key steps

1. Identify evaluation at the fraction-ring variable with the injective canonical embedding.
2. Use reversed polynomials and their nonzero constant coefficients to prove transcendence of the inverse variable.
3. Represent a nonzero rational function as a quotient of nonzero polynomials in the original variable.
4. Reverse numerator and denominator to obtain an integer power of the inverse variable times their evaluated quotient.
5. Absorb that power into the numerator or denominator according to the degree comparison, preserving a nonzero denominator.
6. Handle zero by the representation 0/1.

## Reference use

### local-project

Queries:
- `finite_place_model|reverse_eval|eval₂_reverse|eval_reverse|transcendental_inv|transcendental_iff_inv`
- `mem_or_inv_mem|isUnit_iff|eq_of_le_of_ne_top|algebraMap_mem|X_dvd_iff|exists.*pow.*dvd|X_pow|trailingDegree|factor.*X`
- `isMaximal.*X|X.*isMaximal|ker.*eval|span_X|eval.*ker`
- `p06_9e0f5043ff_inf_reciprocal_presentation|p06_9e0f5043ff_inf_reciprocal_polynomial_order|p06_9e0f5043ff_inf_valuation_fraction_characterization`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/project/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/Algebra/Polynomial/Reverse.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/Algebra/Polynomial/Div.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/Algebraic/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/Valuation/ValuationSubring.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/Polynomial/Ideal.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/Polynomial/Quotient.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-rational-adjoin-principal-a1-rational-model-principal-a1-infinity-place-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-rational-adjoin-principal-a1-rational-model-principal-a1-infinity-place-a1/decomposition-typecheck/CheckTypes.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-rational-adjoin-principal-a1-rational-model-principal-a1-infinity-place-a1/decomposition-typecheck/CheckTypes.interface-check.log`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-rational-adjoin-principal-a1-rational-model-principal-a1-infinity-place-a1/decomposition-typecheck/Submission.frozen-source-check.log`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-rational-adjoin-principal-a1-rational-model-principal-a1-infinity-place-a1/decomposition-typecheck/provenance-check.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-rational-adjoin-principal-a1-rational-model-principal-a1-infinity-place-a1/decomposition-typecheck/name-collision-check.json`

The snapshot supplies Place.ext, Place.ord_mul, Place.ord_zpow, polynomial reversal identities, X-divisibility and root-multiplicity factorization, valuation-subring locality, and the quotient-by-X identification with K. No finite_place_model declaration was found in the snapshot; it is an existing ancestor-level DAG dependency, not an accepted library theorem. Proposed identifiers have no searched-source or active-DAG collisions. Project revision 956e8c600d8b95b46948ae5e37b13930b5f3d06b, mathlib revision db584cd6d46c92f209a44c0f1c829460d327499d, and all nine dependencies match their manifests with clean tracked files. All three proposed types elaborate warning-free under the existing isolated import-only Submission interface. Definitional checks verify the canonical FractionRing algebra, polynomial evaluation, and Place subring and residue algebras. Audited supporting declarations use only propext, Classical.choice, and Quot.sound. However, checking the unchanged actual Submission.lean fails on the pre-existing unknown attribute targets AlgebraicCurve.IsCurveOver.instNontrivialKaehler, AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply, and AlgebraicCurve.SemilinearAut.coe_torsion_smul. Consequently actual import Submission validation remains blocked; interface typechecking is not comparator acceptance or authorization to activate children.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/360

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
