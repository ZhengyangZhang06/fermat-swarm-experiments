<!-- theorem-id: fermat-p06/root.finite_order_support_ascent-a1.polynomial_coefficients_integral_off_fa-a1 -->

## Theorem `Submission.p06_9e0f5043ff_fosa_coefficients_integral_off_finite`

Let K and E be fields with a K-algebra structure on E. Assume that for every nonzero a in E, the set {v : AlgebraicCurve.Place K E | v.ord a ≠ 0} is finite. Then for every polynomial P over E there exists a finite set T of project places of E over K such that, for every v outside T and every natural number i, P.coeff i belongs to v.toValuationSubring.

Node: `root.finite_order_support_ascent-a1.polynomial_coefficients_integral_off_fa-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/6

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/35

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p06_9e0f5043ff_fosa_coefficients_integral_off_finite`

```lean
∀ (K E : Type*) [Field K] [Field E] [Algebra K E], (∀ a : E, a ≠ 0 → {v : AlgebraicCurve.Place K E | v.ord a ≠ 0}.Finite) → ∀ P : Polynomial E, ∃ T : Set (AlgebraicCurve.Place K E), T.Finite ∧ ∀ v : AlgebraicCurve.Place K E, v ∉ T → ∀ i : ℕ, P.coeff i ∈ v.toValuationSubring
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

- Parent DAG node: `root.finite_order_support_ascent-a1`
- Child DAG node: `root.finite_order_support_ascent-a1.polynomial_coefficients_integral_off_fa-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix K, E, their stated field and algebra structures, the finite-support hypothesis H, and a polynomial P. For each i in the finite polynomial support P.support, the coefficient c_i = P.coeff i is nonzero. Consequently S_i = {v : AlgebraicCurve.Place K E | v.ord c_i ≠ 0} is finite by H.
2. Define T = ⋃ i ∈ P.support, S_i. This is a finite union of finite sets, so T is finite.
3. Fix a place v outside T and a natural number i. If P.coeff i = 0, then this coefficient belongs to v.toValuationSubring because every subring contains zero. Otherwise i belongs to P.support. Since v is outside T, it is outside S_i, and therefore v.ord (P.coeff i) = 0.
4. The valuation subring of v is a discrete valuation ring. Choose an irreducible uniformizer π in it, using IsDiscreteValuationRing.exists_irreducible. Apply Place.exists_unit_mul_zpow to the nonzero coefficient. It supplies a unit u of v.toValuationSubring such that P.coeff i = ((u : v.toValuationSubring) : E) * ((π : E) ^ (v.ord (P.coeff i))). The exponent is zero by step 3, so P.coeff i equals the image of u. Thus the coefficient belongs to v.toValuationSubring.
5. The two cases prove coefficient membership for every i at every v outside T. Together with the finiteness of T, this proves the statement.

## Key steps

1. Index the nonzero coefficients by the finite polynomial support.
2. Use the hypothesis to obtain a finite order support for each such coefficient.
3. Take their finite union as the exceptional set.
4. Outside this set, each nonzero coefficient has order zero.
5. Use unit–uniformizer factorization to obtain membership; handle zero coefficients separately.

## Reference use

### local-project

Queries:
- `rg -n 'finite_setOf_restrict_eq|mem_of_eval_monic_eq_zero|exists_unit_mul_zpow|ord_coe_unit|def restrict|HasPrincipalDivisors|hasPrincipalDivisors_of_transcendental' .humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f --glob '*.lean'`
- `rg -n 'finite.*coeff|coeff.*finite|coeff.*ord|ord.*coeff|mem_of_ord_nonneg|ord_eq_zero_of' .humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/project/Definitions/Def_AlgebraicCurve_*.lean`
- `rg -n 'exists_irreducible|theorem isIntegral|isIntegral_of_finite' .humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/DiscreteValuationRing .humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/IntegralClosure/Algebra/Basic.lean`
- `rg -n 'p06_9e0f5043ff_fosa_coefficients_integral_off_finite|p06_9e0f5043ff_fosa_ord_zero_of_monic_pair' .humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/dag.json Submission.lean Definitions Fermat`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/problem.md`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/project/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/project/Definitions/Def_AlgebraicCurve_DivisorPushPull.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/DiscreteValuationRing/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/IntegralClosure/Algebra/Basic.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/project/Definitions/Def_AlgebraicCurve_PlacesOverDVR.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/dag.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-finite-order-support-ascent-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-finite-order-support-ascent-a1/decomposition-typecheck/CheckTypes.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-finite-order-support-ascent-a1/decomposition-typecheck/CheckTypes.interface-check.log`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/nodes/root-finite-order-support-ascent-a1/decomposition-typecheck/Submission.unchanged-check.log`

DivisorClassGroup supplies the DVR instance, unit–uniformizer factorization, and order zero for units. DivisorPushPull defines restriction by valuation-subring comap and supplies mem_restrict_iff; its order-to-membership lemmas are private. PlacesOverDVR supplies mem_of_eval_monic_eq_zero and finite_setOf_restrict_eq, the latter without principal-divisor assumptions. No existing public coefficient-exceptional-set or monic-pair order-zero theorem matched the targeted search. Neither proposed name matched existing DAG reservations or project declarations. Project HEAD matches 956e8c600d8b95b46948ae5e37b13930b5f3d06b; all nine dependencies are clean at their pinned revisions, including mathlib db584cd6d46c92f209a44c0f1c829460d327499d. The three imported project sources match the snapshot and existing interface build byte-for-byte. Both proposed types elaborate under the existing import-only Submission interface. Additional checks verify restriction is definitionally the intended comap and finite-dimensionality supplies Algebra.IsIntegral. The six audited supporting declarations have only propext, Classical.choice, and Quot.sound as transitive axioms. However, the unchanged authoritative Submission still fails on three pre-existing attribute directives naming unavailable declarations. Successful validation through that unchanged module remains blocked; interface checking is not comparator acceptance.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/488

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
