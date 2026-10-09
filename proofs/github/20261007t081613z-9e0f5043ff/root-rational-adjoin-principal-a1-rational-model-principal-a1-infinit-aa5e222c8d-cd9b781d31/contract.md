<!-- theorem-id: fermat-p06/root.rational_adjoin_principal-a1.rational_model_principal-a1.infinity_place-a1.valuation_fraction_characterization-a1.polynomial_unit_criterion-a1 -->

## Theorem `Submission.p06_9e0f5043ff_vfc_polynomial_unit_criterion`

Let K and F be fields with a K-algebra structure on F. Let s ∈ F and w : AlgebraicCurve.Place K F, and put W = w.toValuationSubring. Assume s⁻¹ ∉ W. For every polynomial p ∈ K[T], there exists a unit u of W whose image in F equals p(s) if and only if T does not divide p. Here p(s) denotes Polynomial.aeval s p. No transcendence or fraction-generation hypothesis is required.

Node: `root.rational_adjoin_principal-a1.rational_model_principal-a1.infinity_place-a1.valuation_fraction_characterization-a1.polynomial_unit_criterion-a1`

Root: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/6

Parent: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/issues/244

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.p06_9e0f5043ff_vfc_polynomial_unit_criterion`

```lean
∀ (K F : Type*) [Field K] [Field F] [Algebra K F] (s : F) (w : AlgebraicCurve.Place K F), s⁻¹ ∉ w.toValuationSubring → ∀ p : Polynomial K, (∃ u : Units w.toValuationSubring, ((u : w.toValuationSubring) : F) = Polynomial.aeval s p) ↔ ¬ (Polynomial.X : Polynomial K) ∣ p
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

- Parent DAG node: `root.rational_adjoin_principal-a1.rational_model_principal-a1.infinity_place-a1.valuation_fraction_characterization-a1`
- Child DAG node: `root.rational_adjoin_principal-a1.rational_model_principal-a1.infinity_place-a1.valuation_fraction_characterization-a1.polynomial_unit_criterion-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Fix K, F, their algebra structure, s and w satisfying the hypotheses, and put W = w.toValuationSubring. Since zero belongs to W and the inverse of zero is zero, the exclusion s⁻¹ ∉ W implies s ≠ 0. The valuation-subring property gives s ∈ W or s⁻¹ ∈ W, so s ∈ W. The resulting element of W is not a unit: the image in F of an inverse in W would equal s⁻¹, contradicting its exclusion.
2. The defining property of a project place puts algebraMap K F c in W for every c ∈ K. Together with s ∈ W and closure under finite sums and products, this puts p(s) in W for every polynomial p. Consequently evaluation defines a unital ring homomorphism E : K[T] → W, whose composition with the inclusion W → F is Polynomial.aeval s. Its homomorphism laws follow from the evaluation laws and injectivity of the inclusion.
3. A valuation subring is a local ring. Let m be its maximal ideal, which consists exactly of its nonunits, and let J = E⁻¹(m). This is a proper ideal of K[T]: E(1) = 1 is a unit and hence does not belong to m. By step 1, E(T) is a nonunit, so T ∈ J and the principal ideal (T) is contained in J.
4. The ideal (T) is maximal. Indeed, every polynomial p has the form C(c) + Tq, where c is its constant coefficient, and T divides p exactly when c = 0. In particular, (T) is proper because the constant coefficient of 1 is nonzero. If an ideal I properly contains (T), choose p ∈ I with T not dividing p. Its constant coefficient c is nonzero. Subtracting Tq from p shows C(c) ∈ I, and multiplying by C(c⁻¹) shows 1 ∈ I. Thus I is the whole polynomial ring, proving maximality. Since J is proper and contains (T), it follows that J = (T).
5. Fix any polynomial p. The local-ring unit criterion and the definition of J give: E(p) is a unit if and only if E(p) ∉ m, if and only if p ∉ J. By J = (T), this is equivalent to T not dividing p.
6. If E(p) is a unit, choose a unit u of W with value E(p). Its image in F is p(s), giving the required existential statement. Conversely, if a unit u of W has image p(s), its value and E(p) have the same image in F. Injectivity of W → F identifies them, so E(p) is a unit. Combining this equivalence with step 5 proves the stated biconditional for every p.

## Key steps

1. Use inverse exclusion to place s in W and show that it is a nonunit.
2. Factor polynomial evaluation through a unital ring homomorphism E into W.
3. Contract the maximal ideal to a proper polynomial ideal J containing T.
4. Use constant coefficients to prove maximality of (T), hence J = (T).
5. Translate avoidance of J into being a unit and then into the stated unit witness.

## Reference use

### local-project

Queries:
- `structure Place|def center|center_ne_bot|toValuationSubring_eq_of_forall_mem|mem_or_inv_mem|algebraMap_mem`
- `exists.*X_pow|X_pow.*exists|X_pow_mul.*[a-z]|not_dvd.*iff|exists_eq_pow_mul_and_not_dvd|exists_pow_mul`
- `isUnit_iff|mem_or_inv_mem|IsLocalRing|isUnit.*mem|mem.*isUnit`
- `theorem X_dvd_iff|theorem irreducible_X|lemma irreducible_X|quotientSpanXSubCAlgEquiv`

Files inspected:
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/manifest.json`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/project/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/project/Definitions/Def_AlgebraicCurve_PlacesOverDVR.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/Algebra/Polynomial/Div.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/Algebra/Polynomial/RingDivision.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/Valuation/ValuationSubring.lean`
- `/mnt/data/zhengyang-workspace/fermat-swarm-projects/fermat-p06/.humanize/github-theorem-prover/runs/20261007T081613Z-9e0f5043ff/local-references/08e30764522e474f/mathlib/Mathlib/RingTheory/LocalRing/MaximalIdeal/Basic.lean`
- `/tmp/p06_vfc_decomposition_p_0ah0j7/CheckTypes.lean`
- `/tmp/p06_vfc_decomposition_p_0ah0j7/CheckTypes.log`
- `/tmp/p06_vfc_decomposition_p_0ah0j7/source-compatibility.json`
- `/tmp/p06_vfc_decomposition_p_0ah0j7/frozen_header_repair.json`

The manifest pins project 956e8c600d8b95b46948ae5e37b13930b5f3d06b and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. Place.algebraMap_mem' supplies containment of constants; valuation subrings supply mem_or_inv_mem and IsLocalRing; IsLocalRing.notMem_maximalIdeal identifies units. Polynomial.X_dvd_iff and exists_eq_pow_rootMultiplicity_mul_and_not_dvd supply divisibility and the required factorization at zero, so polynomial factorization needs no new node. Consulted sources matched installed sources, and installed mathlib was clean at its pinned revision. The checked library declarations have only propext, Classical.choice and Quot.sound as transitive axioms. Both proposed types elaborated after import Submission in a disposable compiler copy of the node's frozen proof base; subring ring instances and unit multiplication coercions were checked. Both proposed names were absent from run metadata and the imported base. Compiler-copy evidence records the prescribed policy digest, exact omitted lines 9–11, reversible original/build hashes, and a successful Lean absence probe for all 95 targets. Original repository files remain unchanged. These are interface diagnostics, not comparator acceptance of either proposed theorem.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Local integration must pass before publication. Every decomposition child has its own issue and verified solution PR.

Solution PR: https://github.com/ZhengyangZhang06/fermat-swarm-experiments/pull/493

Current user-authorized lifecycle: merge the exact verified PR, validate its remote tree, then close this proved issue. This supersedes historical no-auto-merge instructions in the original experiment brief.

Remote merge status is recorded by GitHub; local `proved` does not mean merged.
